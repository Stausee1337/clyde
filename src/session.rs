
use std::{cell::{Cell, OnceCell, RefCell}, env, ffi::OsStr, path::{Path, PathBuf}, process::ExitCode, rc::Rc, str::FromStr};

use index_vec::IndexVec;
use crate::{syntax::{ast::AstInfo, parser}, context::{GlobalCtxt, Providers, TyCtxt}, diagnostics::DiagnosticsCtxt, analysis::{intermediate, resolve, typecheck}, type_ir, files, target::Target};

const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Default, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationLevel {
    #[default] O0, O1, O2, O3
}

impl OptimizationLevel {
    pub const fn as_str(&self) -> &'static str {
        macro_rules! build_match {
            ($($ident:ident),*) => {
                match self {
                    $(OptimizationLevel::$ident => stringify!($ident)),*
                }
            };
        }
        build_match!(O0, O1, O2, O3)
    }
}

impl TryFrom<&str> for OptimizationLevel {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "0" => Ok(OptimizationLevel::O0),
            "1" => Ok(OptimizationLevel::O1),
            "2" => Ok(OptimizationLevel::O2),
            "3" => Ok(OptimizationLevel::O3),
            _ => Err(())
        }
    }
}

pub struct Cfg {
    pub print_ir: bool,
    pub print_llvm_ir: bool,
    pub run_output: bool,
    pub opt_level: OptimizationLevel
}

pub struct Session {
    input: PathBuf,
    pub target: Target,

    pub output_dir: PathBuf,
    pub output_file: PathBuf,
    pub working_dir: PathBuf,

    pub config: Cfg,
    diagnostics: DiagnosticsCtxt,
    file_cacher: Rc<files::FileCacher>,
}

impl Session {
    pub fn diagnostics(&self) -> &DiagnosticsCtxt {
        &self.diagnostics
    }

    pub fn file_cacher(&self) -> Rc<files::FileCacher> {
        self.file_cacher.clone()
    }

    pub fn global_ctxt<F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> Result<R, ()>, R>(&self, f: F) -> Result<R, ()> {
        let ast_info = AstInfo {
            arena: bumpalo::Bump::new(),
            global_owners: RefCell::new(IndexVec::new()),
            tainted_with_errors: Cell::new(None)
        };
        let entry = parser::parse_file(&self, &self.input, &ast_info)?;
        let resolutions = resolve::resolve_from_entry(&self, entry, &ast_info);

        let providers = Providers {
            type_of: typecheck::type_of,
            typecheck: typecheck::typecheck,
            fn_sig: typecheck::fn_sig,
            build_ir: intermediate::build_ir,
            layout_of: type_ir::layout_of
        };
        let arena = bumpalo::Bump::new();

        let gcx = GlobalCtxt::new(&self, &arena, providers, resolutions);
        gcx.enter(f)
    }
}

pub struct Options {
    input: PathBuf,
    output_dir: Option<PathBuf>,
    output_file: Option<PathBuf>,
    working_dir: PathBuf,

    config: Cfg
}

impl Options {
    pub fn create_compile_session(self) -> Result<Session, ()> {
        let target = Target::host().ok_or(())?;

        let file_cacher: Rc<files::FileCacher> = FILE_CACHER.with(|cacher| cacher.clone());
        let output_file = self.output_file.unwrap_or_else(|| {
            let input = self.input.clone();
            assert!(input.is_file());
            let mut output = input;
            // FIXME: ommit this on non-windows systems
            output.set_extension("exe");

            output
        });
        Ok(Session {
            target,
            input: self.input,
            output_dir: self.output_dir.unwrap_or_else(|| self.working_dir.clone()),
            output_file,
            working_dir: self.working_dir,

            config: self.config,
            diagnostics: DiagnosticsCtxt::new(file_cacher.clone()),
            file_cacher
        })
    }
}

pub fn parse_argv_options(args: env::Args) -> Result<Options, ExitCode> {
    let mut args: Vec<String> = args.collect();

    let program = if args.is_empty() { "clydec".to_string() } else { args.remove(0) };
    let program = PathBuf::from_str(program.as_str()).unwrap();
    let program = get_filename(&program).unwrap_or_else(|| "clydec");

    let working_dir = env::current_dir().map_err(|error| {
        eprintln!("ERROR: Could not get current working directory {error}");
        ExitCode::FAILURE
    })?;

    macro_rules! flag {
        ($shortopt:literal, $fullopt:literal, $desc:literal) => {
            |parser| parser.optflag($shortopt, $fullopt, $desc)
        };
    }

    macro_rules! flagopt {
        ($shortopt:literal, $fullopt:literal, $desc:literal, $hint:literal) => {
            |parser| parser.optmulti($shortopt, $fullopt, $desc, $hint)
        };
    }

    macro_rules! opt {
        ($shortopt:literal, $fullopt:literal, $desc:literal, $arg:literal) => {
            |parser| parser.optopt($shortopt, $fullopt, $desc, $arg)
        };
    }

    const CMD_OPTIONS: &[fn(&mut getopts::Options) -> &mut getopts::Options] = &[
        flagopt!("C", "", "Specifiy compiler config", ""),
        opt!("o", "", "Put the output into <file>", "<file>"),
        opt!("", "out-dir", "Write the output into <dir>", "<dir>"),

        flag!("R", "run", "Run the programm upon successful build"),
        flag!("v", "version", "Print clydec version"),
        flag!("h", "help", "Displays this message"),
    ];

    let mut parser = getopts::Options::new();
    for coption in CMD_OPTIONS {
        coption(&mut parser);
    }
    let matches = parser.parse(args).map_err(|e| {
        eprintln!("ERROR: {e}");
        ExitCode::FAILURE
    })?;

    if matches.opt_present("h") || matches.opt_present("help") {
        eprint!(
            "{}",
            parser.usage(format!("Usage: {program} [OPTIONS] INPUT").as_str())
        );
        return Err(ExitCode::SUCCESS);
    }

    if matches.opt_present("v") || matches.opt_present("version") {
        eprintln!("{program} version {VERSION}");
        return Err(ExitCode::SUCCESS);
    }

    let input_file = match &matches.free[..] {
        [input_file] => {
            let file = PathBuf::from_str(input_file).unwrap();
            let res;
            if file.is_absolute() {
                res = file.canonicalize();
            } else {
                let mut path = working_dir.clone();
                path.push(file);
                res = path.canonicalize();
            }

            Some(res.map_err(|err| (input_file, err)))
        },
        _ => None
    };

    let output_file = matches.opt_str("o").map(PathBuf::from);

    let mut options = Options {
        input: PathBuf::new(),

        output_dir: None,
        output_file,
        working_dir,

        config: matches_to_config(&matches)?
    };

    match input_file {
        Some(Ok(input)) => options.input = input,
        Some(Err((input_file, err))) => {
            eprintln!("ERROR: couldn't read {input_file}: {err}");
            return Err(ExitCode::FAILURE);
        }
        None if matches.free.len() == 0 => {
            eprintln!("ERROR: no input files provided");
            return Err(ExitCode::FAILURE);
        }
        None if matches.free.len() > 1 => {
            eprintln!("ERROR: provided multiple input files");
            return Err(ExitCode::FAILURE);
        }
        _ => unreachable!()
    }

    Ok(options)
}

fn matches_to_config(matches: &getopts::Matches) -> Result<Cfg, ExitCode> {
    let opt_level = OnceCell::new();
    let mut print_ir = false;
    let mut print_llvm_ir = false;

    for cfg in matches.opt_strs("C") {
        let parts = cfg.splitn(2, '=').collect::<Vec<_>>();
        match &*parts {
            ["print-ir"] => print_ir = true,
            ["print-llvm-ir"] => print_llvm_ir = true,
            ["opt-level", opt] => {
                let level = OptimizationLevel::try_from(opt.trim())
                    .map_err(|()| {
                        eprintln!("ERROR: Unknown opt-level: found `-C opt-level={}`, valid values are `0`, `1`, `2` and `3`", opt);
                        ExitCode::FAILURE
                    })?;
                opt_level.set(level)
                    .map_err(|_| {
                        eprintln!("ERROR: Cannot specify multiple opt-levels: found `-C opt-level={}` and later `-C opt-level={}`", opt_level.get().unwrap().as_str(), opt);
                        ExitCode::FAILURE
                    })?;
            }
            ["help"] => {
                eprintln!("Config Options:");
                const OPTIONS: &[(&'static str, &'static str)] = &[
                    ("print-ir", ""),
                    ("print-llvm-ir", ""),
                    ("opt-level", "Specify llvm optimization level, valid values are `0`, `1`, `2` and `3"),
                ];
                for (name, desc) in OPTIONS {
                    eprintln!("    -C {name:20}{desc}");
                }
                return Err(ExitCode::SUCCESS);
            }
            _ => {
                eprintln!("ERROR: Unknown config option: `-C {}`; Run with `-C help` to get a list of all config options", cfg);
                return Err(ExitCode::FAILURE);
            }
        }
    }

    Ok(Cfg {
        print_ir,
        print_llvm_ir,
        run_output: matches.opt_present("R") || matches.opt_present("run"),
        opt_level: opt_level.into_inner().unwrap_or_default()
    })
}

unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    // let bytes = osstr.as_bytes();
    let bytes = osstr.as_encoded_bytes();
    std::str::from_utf8_unchecked(bytes)
}

fn get_filename(path: &Path) -> Option<&str> {
    Some(unsafe { osstr_as_str(path.file_name()?) })
}

thread_local! {
    static FILE_CACHER: Rc<files::FileCacher> = Rc::new(files::FileCacher::create());
}

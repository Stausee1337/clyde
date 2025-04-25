
use std::{cell::RefCell, env, ffi::OsStr, path::{Path, PathBuf}, process::ExitCode, rc::Rc, str::FromStr};

use index_vec::IndexVec;
use crate::{syntax::{ast::AstInfo, parser}, context::{GlobalCtxt, Providers, TyCtxt}, diagnostics::DiagnosticsCtxt, analysis::{intermediate, resolve, typecheck}, type_ir, files};

const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct Cfg {
    run_output: bool
}

pub struct Session {
    input: PathBuf,

    output_dir: PathBuf,
    output_file: PathBuf,
    working_dir: PathBuf,

    config: Cfg,
    diagnostics: DiagnosticsCtxt,
    file_cacher: Rc<files::FileCacher>
}

impl Session {
    pub fn diagnostics(&self) -> &DiagnosticsCtxt {
        &self.diagnostics
    }

    pub fn file_cacher(&self) -> &files::FileCacher {
        &self.file_cacher
    }

    pub fn global_ctxt<F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> Result<R, ()>, R>(&self, f: F) -> Result<R, ()> {
        let ast_info = AstInfo {
            arena: bumpalo::Bump::new(),
            global_owners: RefCell::new(IndexVec::new())
        };
        let entry = parser::parse_file(&self, &self.input, &ast_info)?;
        let resolutions = resolve::resolve_from_entry(
            &self.diagnostics,
            entry, &ast_info
        );

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
    pub fn create_compile_session(self) -> Session {
        inkwell::targets::Target::initialize_x86(&inkwell::targets::InitializationConfig::default());
        let triple = inkwell::targets::TargetMachine::get_default_triple();
        eprintln!("compiling for: {:?}", triple.as_str());

        let target = inkwell::targets::Target::from_triple(&triple).unwrap();
        let machine = target.create_target_machine_from_options(&triple, inkwell::targets::TargetMachineOptions::default()).unwrap();
        let data_layout = machine.get_target_data().get_data_layout();
        let layout_string = data_layout.as_str();
        println!("{:?}", layout_string);

        let file_cacher: Rc<files::FileCacher> = files::FILE_CACHER.with(|cacher| cacher.clone());
        Session {
            input: self.input,
            output_dir: self.output_dir.unwrap_or_else(|| self.working_dir.clone()),
            output_file: self.output_file.unwrap_or_else(|| self.working_dir.clone()),
            working_dir: self.working_dir,

            config: self.config,
            diagnostics: DiagnosticsCtxt::new(file_cacher.clone()),
            file_cacher
        }
    }
}

pub fn parse_argv_options(args: env::Args) -> Result<Options, ExitCode> {
    let mut args: Vec<String> = args.collect();

    let program = if args.is_empty() { "wpc".to_string() } else { args.remove(0) };
    let program = PathBuf::from_str(program.as_str()).unwrap();
    let program = get_filename(&program).unwrap_or_else(|| "wpc");

    let working_dir = env::current_dir().map_err(|error| {
        eprintln!("ERROR: Could not get current working directory {error}");
        ExitCode::FAILURE
    })?;

    macro_rules! optflag {
        ($shortopt:literal, $fullopt:literal, $desc:literal) => {
            |parser| parser.optflag($shortopt, $fullopt, $desc)
        };
    }

    macro_rules! optopt {
        ($shortopt:literal, $fullopt:literal, $desc:literal, $arg:literal) => {
            |parser| parser.optopt($shortopt, $fullopt, $desc, $arg)
        };
    }

    const CMD_OPTIONS: &[fn(&mut getopts::Options) -> &mut getopts::Options] = &[
        optflag!("h", "help", "Displays this message"),
        optopt!("o", "", "Put the output into <file>", "<file>"),
        optopt!("", "out-dir", "Write the output into <dir>", "<dir>"),
        optflag!("R", "run", "Run the generated output upon successful build"),
        optflag!("v", "version", "Print wpc version")
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
        print!(
            "{}",
            parser.usage(format!("Usage: {program} [OPTIONS] INPUT").as_str())
        );
        return Err(ExitCode::SUCCESS);
    }

    if matches.opt_present("v") || matches.opt_present("version") {
        println!("{program} version {VERSION}");
        return Err(ExitCode::SUCCESS);
    }

    let input_file = match &matches.free[..] {
        [input_file] => {
            Some(PathBuf::from_str(input_file))
        },
        _ => None
    };

    let mut options = Options {
        input: PathBuf::new(),

        output_dir: None,
        output_file: None,
        working_dir,

        config: matches_to_config(&matches)
    };

    match input_file {
        Some(Ok(input)) => options.input = input,
        other => {
            match other {
                Some(Err(err)) =>
                    eprintln!("ERROR: {err}"),
                None if matches.free.len() == 0 =>
                    eprintln!("ERROR: no input files provided"),
                None if matches.free.len() > 1 =>
                    eprintln!("ERROR: provided multiple input files"),
                _ => unreachable!()
            }
            return Err(ExitCode::FAILURE);
        }
    }

    Ok(options)
}

fn matches_to_config(matches: &getopts::Matches) -> Cfg {
    Cfg {
        run_output: matches.opt_present("R") || matches.opt_present("run")
    }
}

unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    // let bytes = osstr.as_bytes();
    let bytes = osstr.as_encoded_bytes();
    std::str::from_utf8_unchecked(bytes)
}

fn get_filename(path: &Path) -> Option<&str> {
    Some(unsafe { osstr_as_str(path.file_name()?) })
}


use std::{path::{PathBuf, Path}, env, process::ExitCode, str::FromStr, os::unix::ffi::OsStrExt, ffi::OsStr, io::Read, fs::File, cell::{OnceCell, RefCell}, rc::Rc, ops::Range};

use crate::{context::{GlobalCtxt, Providers}, ast, diagnostics::DiagnosticsCtxt, parser, typecheck, types};

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
    file_cacher: Rc<FileCacher>
}

impl Session {
    pub fn diagnostics(&self) -> &DiagnosticsCtxt {
        &self.diagnostics
    }

    pub fn file_cacher(&self) -> &FileCacher {
        &self.file_cacher
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
        let file_cacher = Rc::new(
            FileCacher::new(&self.working_dir));
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

pub struct Source {
    path: PathBuf,
    range: Range<usize>,
}

impl Source {
    pub fn as_str(&self) -> &str {
        todo!()
    }

    pub fn translate(&self, range: Range<usize>) -> Range<usize> {
        self.range.start + range.start..self.range.start + range.end
    }

    pub fn path(&self) -> &str {
        FileCacher::decode_path(&self.path)
    }
}

pub struct FileCacher {
    files: RefCell<Vec<Source>>,
    working_dir: PathBuf,
}

impl FileCacher {
    fn new(working_dir: &Path) -> Self {
        Self {
            files: RefCell::new(Vec::new()),
            working_dir: working_dir.to_owned()
        }
    }

    pub fn load_file(&self, path: &Path) -> Result<&Source, ()> {
        let mut contents = String::new();
        File::open(path)
            .and_then(|mut f| f.read_to_string(&mut contents))
            .map_err(|err| {
                let file = FileCacher::decode_path(path);
                eprintln!("ERROR: couldn't read {file}: {err}");
            })?;
        todo!()
    }

    pub fn lookup_file(&self, _pos: usize) -> Option<Source> {
        todo!()
    }

    fn decode_path(path: &Path) -> &str {
        let osstr = path.as_os_str();
        let bytes = osstr.as_bytes();
        unsafe { std::str::from_utf8_unchecked(bytes) }
    }
}

fn get_filename(path: &Path) -> Option<&str> {
    Some(unsafe { osstr_as_str(path.file_name()?) })
}

pub unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    let bytes = osstr.as_bytes();
    std::str::from_utf8_unchecked(bytes)
}

pub struct Compiler<'tcx> {
    pub sess: Session,
    gcx_cell: OnceCell<GlobalCtxt<'tcx>>,
    gcx: RefCell<Option<&'tcx GlobalCtxt<'tcx>>>
}

impl<'tcx> Compiler<'tcx> {
    pub fn parse_entry(&'tcx self) -> Result<ast::SourceFile, ()> {
        parser::parse_file(&self.sess, &self.sess.input)
    }

    pub fn global_ctxt(&'tcx self) -> &'tcx GlobalCtxt<'tcx> {
        self.gcx
            .borrow_mut()
            .get_or_insert_with(|| {
            let providers = Providers {
                type_of: typecheck::type_of,
                typecheck: typecheck::typecheck,
                fn_sig: typecheck::fn_sig,
                size_of: types::size_of,
            };

            let gcx = self.gcx_cell
                .get_or_init(|| GlobalCtxt::new(&self.sess, providers));
            gcx
        })
    }
}

pub fn build_compiler<T, F>(sess: Session, f: F) -> T
where
    F: for<'tcx> FnOnce(&'tcx Compiler<'tcx>) -> T
{
    let mut compiler = Compiler {
        sess, 
        gcx_cell: OnceCell::new(),
        gcx: RefCell::new(None)
    };

    f(&mut compiler)
}


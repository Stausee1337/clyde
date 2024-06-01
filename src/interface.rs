
use std::{path::{PathBuf, Path}, env, process::ExitCode, str::FromStr, os::unix::ffi::OsStrExt, ffi::OsStr, io::{self, Read}, fs::File, cell::{OnceCell, RefCell}, mem::transmute};

use crate::{context::GlobalCtxt, ast, diagnostics::{Diagnostics, DiagnosticsData}, parser};

const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct Cfg {
    run_output: bool
}

pub const INPUT_FILE_IDX: FileIdx = FileIdx(0);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FileIdx(pub u32);

impl index_vec::Idx for FileIdx {
    fn index(self) -> usize {
        return self.0 as usize
    }

    fn from_usize(idx: usize) -> Self {
        Self(idx as u32)
    }
}

pub struct Session {
    input: PathBuf,

    output_dir: PathBuf,
    output_file: PathBuf,
    working_dir: PathBuf,

    config: Cfg,
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
        Session {
            input: self.input,
            output_dir: self.output_dir.unwrap_or_else(|| self.working_dir.clone()),
            output_file: self.output_file.unwrap_or_else(|| self.working_dir.clone()),
            working_dir: self.working_dir,

            config: self.config
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

fn get_filename(path: &Path) -> Option<&str> {
    Some(unsafe { osstr_as_str(path.file_name()?) })
}

pub unsafe fn path_as_str(path: &Path) -> &str {
    osstr_as_str(path.as_os_str())
}

pub unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    let bytes = osstr.as_bytes();
    std::str::from_utf8_unchecked(bytes)
}

fn matches_to_config(matches: &getopts::Matches) -> Cfg {
    Cfg {
        run_output: matches.opt_present("R") || matches.opt_present("run")
    }
}

fn read_entire_file(filename: &Path) -> Result<String, io::Error> {
    let mut result = String::new();
    File::open(filename)?
        .read_to_string(&mut result)?;
    Ok(result)
}

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

#[derive(Debug)]
pub struct Steal<T> {
    value: RefCell<Option<T>>
}

impl<T> Steal<T> {
    pub fn new(value: T) -> Self {
        Self { value: RefCell::new(Some(value)) }
    }

    #[allow(unused)]
    pub fn get(&self) -> &'_ T {
        let borrow = self.value.borrow();
        if borrow.is_none() {
            panic!("attempted to read from stolen value: {}", std::any::type_name::<T>());
        }
        unsafe { transmute(borrow.as_ref().unwrap()) }
    }

    #[allow(unused)]
    pub fn get_mut(&mut self) -> &'_ mut T {
        self.value.get_mut().as_mut().expect("attempt to read from stolen value")
    }

    #[allow(unused)]
    pub fn steal(&self) -> T {
        let value = self.value.take();
        value.expect("attempt to steal from stolen value")
    }
}

pub struct Compiler<'tcx> {
    pub sess: Session,
    gcx_cell: OnceCell<GlobalCtxt<'tcx>>,
    gcx: RefCell<Option<&'tcx GlobalCtxt<'tcx>>>
}

impl<'tcx> Compiler<'tcx> {
    pub fn parse(&'tcx self) -> Result<(ast::SourceFile, Diagnostics<'tcx>), ()> {
        let gcx = self.global_ctxt();
        let source = read_entire_file(&gcx.session.input)
            .map_err(|err| {
                let file = unsafe { path_as_str(&gcx.session.input) };
                eprintln!("ERROR: couldn't read {file}: {err}");
            })
            .map(|s| gcx.alloc_str(&s))?;

        let diagnostics = Diagnostics(gcx.alloc(DiagnosticsData::new(&gcx.session.input, source)));

        Ok((parser::parse_file(diagnostics), diagnostics))
    }

    pub fn global_ctxt(&'tcx self) -> &'tcx GlobalCtxt<'tcx> {
        self.gcx
            .borrow_mut()
            .get_or_insert_with(|| {
            let gcx = self.gcx_cell
                .get_or_init(|| GlobalCtxt::new(&self.sess));
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


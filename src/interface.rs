
use std::{mem::transmute, path::{PathBuf, Path}, env, process::ExitCode, str::FromStr, os::unix::ffi::OsStrExt, collections::HashMap, cell::RefCell, ffi::OsStr};

use crate::{
    ast_analysis as analysis,
    diagnostics::{Diagnostics, DiagnosticsData},
    parser, ast
};

const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct Cfg {
    run_output: bool
}

pub struct Session {
    diagnostic_arena: bumpalo::Bump,
    diagnostics_file_map: RefCell<HashMap<&'static str, Diagnostics>>,

    input: PathBuf,

    output_dir: PathBuf,
    output_file: PathBuf,
    working_dir: PathBuf,

    config: Cfg,
}

impl Session {
    pub fn create_diagnostics_for_file<'s>(&self, filename: &'s str, source: &'s str) -> Diagnostics {
        let filename = unsafe { 
            transmute::<&mut str, &str>(self.diagnostic_arena.alloc_str(filename))
        };
        let source = unsafe { 
            transmute::<&mut str, &str>(self.diagnostic_arena.alloc_str(source))
        };

        let data = self.diagnostic_arena.alloc(DiagnosticsData::new(filename, source));
        let data = unsafe { transmute::<&mut DiagnosticsData, &DiagnosticsData>(data) };

        let diagnostics = Diagnostics(data);
        self.diagnostics_file_map.borrow_mut().insert(filename, diagnostics);

        diagnostics
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
        Session {
            diagnostic_arena: bumpalo::Bump::new(),
            diagnostics_file_map: Default::default(),

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
    let program = get_filename(program).unwrap_or_else(|| "wpc".to_string());

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

fn get_filename(path: PathBuf) -> Option<String> {
    Some(unsafe { osstr_to_string(path.file_name()?) })
}


pub unsafe fn path_to_string(path: &Path) -> String {
    osstr_to_string(path.as_os_str())
}

pub unsafe fn osstr_to_string(osstr: &OsStr) -> String {
    let bytes = osstr.as_bytes();
    String::from_utf8_unchecked(bytes.to_vec())
}

pub unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    std::str::from_utf8_unchecked(osstr.as_bytes())
}


fn matches_to_config(matches: &getopts::Matches) -> Cfg {
    Cfg {
        run_output: matches.opt_present("R") || matches.opt_present("run")
    }
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

pub struct Compiler {
    pub sess: Session
}

impl Compiler {
    pub fn parse(&mut self) -> Result<ast::Unit, ()> {
        parser::parse_unit_from_file(&self.sess.input, &self.sess)
    }
}

pub fn build_compiler<T, F: FnOnce(&mut Compiler) -> T>(sess: Session, f: F) -> T {
    let mut compiler = Compiler { sess };

    f(&mut compiler)
}

pub fn fully_resolve_unit(mut unit: ast::Unit) {
    let mut resolver = analysis::Resolver::new();
    resolver.resolve_unit(&mut unit);
}


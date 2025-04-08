
use std::{path::{PathBuf, Path}, env, process::{ExitCode, abort}, str::FromStr, ffi::OsStr, io::Read, fs, cell::{OnceCell, RefCell}, rc::Rc};

#[cfg(target_family = "unix")]
use rustix::mm::{mmap_anonymous, mprotect, ProtFlags, MapFlags, MprotectFlags};

#[cfg(target_family = "windows")]
use windows::Win32::System::Memory::{VirtualAlloc, VirtualFree, MEM_COMMIT, MEM_RESERVE, MEM_RELEASE, PAGE_READWRITE};

use crate::{context::{GlobalCtxt, Providers}, ast, diagnostics::DiagnosticsCtxt, parser, typecheck, lexer::Span};

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
        let file_cacher: Rc<FileCacher> = FILE_CACHER.with(|cacher| cacher.clone());
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

#[derive(Clone)]
pub struct File {
    path: PathBuf,
    contents: &'static [u8],
    byte_span: Span
}

impl File {
    pub fn contents(&self) -> &[u8] {
        self.contents
    }

    pub fn translate(&self, span: Span) -> Span {
        Span::new(
            self.byte_span.start + span.start,
            self.byte_span.start + span.end)
    }

    pub fn path(&self) -> &str {
        FileCacher::decode_path(&self.path)
    }

    pub fn relative_start(&self) -> u32 {
        self.byte_span.start
    }

    pub fn unicode_slice(&self, pos: u32) -> usize {
        todo!()
    }

    pub fn decode_to_lineno(&self, pos: u32) -> Option<usize> {
        todo!()
    }

    pub fn decode_to_file_pos(&self, pos: u32) -> (usize, usize) {
        todo!()
    }

    pub fn get_line(&self, idx: usize) -> &str {
        todo!()
    }
}

pub struct FileCacher {
    files: RefCell<Vec<Rc<File>>>,
    storage: RefCell<ContinuousSourceStorage>
}

impl FileCacher {
    fn new() -> Self {
        Self {
            files: RefCell::new(Default::default()),
            storage: RefCell::new(ContinuousSourceStorage::allocate()),
        }
    }

    pub fn load_file(&self, path: &Path) -> Result<Rc<File>, ()> {
        let mut storage = self.storage.borrow_mut();
        let (contents, pos, len) = fs::File::open(path)
            .and_then(|mut f| {
                let metadata = f.metadata()?;
                let size = metadata.len() as usize;
                let (buf, pos) = storage.new_buffer(size);
                f.read_exact(buf)?;
                Ok((buf, pos as u32, size as u32))
            })
            .map_err(|err| {
                let file = FileCacher::decode_path(path);
                eprintln!("ERROR: couldn't read {file}: {err}");
            })?;
        let mut files = self.files.borrow_mut();
        let source = Rc::new(File {
            path: path.to_owned(),
            contents,
            byte_span: Span::new(pos, pos + len),
        });
        files.push(source.clone());
        Ok(source)
    }

    pub fn lookup_file(&self, needle: u32) -> Rc<File> {
        let files = self.files.borrow() ;
        let idx = files.partition_point(|source| !source.byte_span.contains(needle));
        files[idx].clone()
    }

    fn decode_path(path: &Path) -> &str {
        let osstr = path.as_os_str();
        let bytes = osstr.as_encoded_bytes();
        unsafe { std::str::from_utf8_unchecked(bytes) }
    }
}

struct ContinuousSourceStorage {
    start: *mut u8,
    current_end: *mut u8,
    allocated_bytes: usize
}

impl ContinuousSourceStorage {
    const STORAGE_SIZE: usize = u32::MAX as usize;
    const PAGE_SIZE: usize = 4096;

    #[cfg(target_family = "unix")]
    fn allocate() -> Self {
        unsafe {
            let ptr = mmap_anonymous(
                std::ptr::null_mut(),
                Self::STORAGE_SIZE,
                ProtFlags::empty(),
                MapFlags::PRIVATE
            )
            .map_err(|err| {
                eprintln!("Memory Allocation Failure: {}", err.to_string());
                abort();
            })
            .unwrap_unchecked();

            Self {
                start: ptr as *mut u8,
                current_end: ptr as *mut u8,
                allocated_bytes: 0
            }
        }
    }

    #[cfg(target_family = "windows")]
    fn allocate() -> Self {
        unsafe {
            let ptr = VirtualAlloc(
                None,
                Self::STORAGE_SIZE,
                MEM_RESERVE,
                PAGE_READWRITE
            );
            if ptr == std::ptr::null_mut() {
                eprintln!("Win32 Memory Allocation Failure");
                abort();
            }


            Self {
                start: ptr as *mut u8,
                current_end: ptr as *mut u8,
                allocated_bytes: 0
            }
        }
    }

    unsafe fn grow(&mut self, added_size: usize) {
        let mut new_size = self.allocated_bytes;
        let target = new_size + added_size;
        loop {
            if new_size >= target {
                break;
            }
            let dsize = Self::PAGE_SIZE - (new_size & (Self::PAGE_SIZE - 1));
            new_size += dsize;
        }
        let page_diff = self.current_end.offset_from(self.start) as usize;
        let len = new_size - page_diff;
        let new_end = self.current_end.add(len);
        if new_end >= self.start.add(Self::STORAGE_SIZE) {
            eprintln!("Memory Allocation Failure: Attempt to allocate to many files (> 4 GiB) in one thread");
            abort();
        }
        #[cfg(target_family = "unix")]
        {
            mprotect(
                self.current_end as *mut _, len,
                MprotectFlags::WRITE | MprotectFlags::READ
            )
            .map_err(|err| {
                eprintln!("Memory Allocation Failure: {}", err.to_string());
                abort();
            })
            .unwrap_unchecked();
        }
        #[cfg(target_family = "windows")]
        {
            assert!(len % Self::PAGE_SIZE == 0);
            VirtualAlloc(
                Some(self.current_end as *const _),
                len,
                MEM_COMMIT,
                PAGE_READWRITE
            );
        }
        self.current_end = new_end;
    }

    fn new_buffer(&mut self, size: usize) -> (&'static mut [u8], usize) {
        unsafe {
            let start = self.allocated_bytes;
            let start_ptr = self.start.add(start);
            let end_ptr = start_ptr.add(size);

            if end_ptr > self.current_end {
                self.grow(size);
            }

            self.allocated_bytes += size;

            let buf = std::slice::from_raw_parts_mut(start_ptr, size);
            (buf, start)
        }
    }
}

thread_local! {
    static FILE_CACHER: Rc<FileCacher> = Rc::new(FileCacher::new());
}

fn get_filename(path: &Path) -> Option<&str> {
    Some(unsafe { osstr_as_str(path.file_name()?) })
}

pub unsafe fn osstr_as_str(osstr: &OsStr) -> &str {
    // let bytes = osstr.as_bytes();
    let bytes = osstr.as_encoded_bytes();
    std::str::from_utf8_unchecked(bytes)
}

pub struct Compiler<'tcx> {
    pub sess: Session,
    gcx_cell: OnceCell<GlobalCtxt<'tcx>>,
    gcx: RefCell<Option<&'tcx GlobalCtxt<'tcx>>>
}

impl<'tcx> Compiler<'tcx> {
    pub fn parse_entry(&'tcx self) -> Result<ast::SourceFile<'tcx>, ()> {
        parser::parse_file(&self.sess, &self.sess.input)
    }

    pub fn global_ctxt(&'tcx self) -> &'tcx GlobalCtxt<'tcx> {
        self.gcx
            .borrow_mut()
            .get_or_insert_with(|| {
            let providers = Providers {
                type_of: typecheck::type_of,
                typecheck: typecheck::typecheck,
                fn_sig: typecheck::fn_sig
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



use std::{path::{PathBuf, Path}, env, process::{ExitCode, abort}, str::FromStr, ffi::OsStr, io::Read, fs, cell::{OnceCell, RefCell}, rc::Rc};

#[cfg(target_family = "unix")]
use rustix::mm::{mmap_anonymous, mprotect, ProtFlags, MapFlags, MprotectFlags};

#[cfg(target_family = "windows")]
use windows::Win32::System::Memory::{VirtualAlloc, VirtualFree, MEM_COMMIT, MEM_RESERVE, MEM_RELEASE, PAGE_READWRITE};

use crate::{ast, context::{GlobalCtxt, Providers}, diagnostics::DiagnosticsCtxt, lexer::Span, parser, string_internals::{run_utf8_validation, next_code_point}, typecheck};

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

#[derive(Clone, Copy)]
pub struct Utf8Error;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct RelativePosition(u32);

impl std::fmt::Debug for RelativePosition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

pub struct File {
    path: PathBuf,
    contents: Result<&'static [u8], Utf8Error>,
    byte_span: Span,
    lines: Vec<RelativePosition>,
    multibyte_chars: Vec<MultibyteChar>,
}

impl File {
    fn new(path: PathBuf, bytes: &'static [u8], byte_span: Span) -> File {
        let (contents, lines, multibyte_chars);
        if run_utf8_validation(bytes) {
            (lines, multibyte_chars) = unsafe {
                // this is safe as we now know we're handling valid unicode
                analyze_unicode(bytes)
            };
            contents = Ok(bytes);
        } else {
            (lines, multibyte_chars) = (vec![], vec![]);
            contents = Err(Utf8Error);
        }
        Self {
            path,
            contents,
            byte_span,
            lines,
            multibyte_chars
        }
    }

    pub fn contents(&self) -> Result<&[u8], Utf8Error> {
        self.contents
    }

    pub fn path(&self) -> &str {
        FileCacher::decode_path(&self.path)
    }

    pub fn relative_start(&self) -> u32 {
        self.byte_span.start
    }

    pub fn relative_position(&self, pos: u32) -> RelativePosition {
        debug_assert!((self.byte_span.start..self.byte_span.end).contains(&pos), "position within the file");
        RelativePosition(pos - self.byte_span.start)
    }

    /// converts a byte position `pos` to a character position
    pub fn pos_to_charpos(&self, pos: RelativePosition) -> usize {
        let mut extra_bytes = 0;

        for item in &self.multibyte_chars {
            if item.pos < pos {
                extra_bytes += item.len as usize - 1;  
                debug_assert!(pos.0 >= item.pos.0 + item.len as u32);
            } else {
                break;
            }
        }

        pos.0 as usize - extra_bytes
    }

    /// gets the 0-based lineno for the given byte position
    pub fn decode_to_lineno(&self, pos: RelativePosition) -> Option<usize> {
        self.lines.partition_point(|start| *start <= pos).checked_sub(1)
    }

    pub fn decode_to_file_pos(&self, pos: RelativePosition) -> (usize, usize) {
        let char_pos = self.pos_to_charpos(pos);
        let Some(lineno) = self.decode_to_lineno(pos) else {
            return (0, char_pos);
        };
        let linebbegin = self.lines[lineno];
        let linecbegin = self.pos_to_charpos(linebbegin);

        let col = char_pos - linecbegin;
        (lineno + 1, col + 1)
    }

    pub fn get_line(&self, lineno: usize) -> Option<&str> {
        let begin = *self.lines.get(lineno)?;
        let subslice = &self.contents().ok()?[begin.0 as usize..];
        let subslice = unsafe { std::str::from_utf8_unchecked(subslice) };

        let line = match subslice.find(&['\n', '\r']) {
            Some(end) => &subslice[..end],
            None => subslice,
        };

        Some(line)
    }

    pub fn lines(&self) -> &[RelativePosition] {
        &self.lines
    }
}

struct MultibyteChar {
    pos: RelativePosition,
    len: u8
}

unsafe fn analyze_unicode(unicode: &[u8]) -> (Vec<RelativePosition>, Vec<MultibyteChar>) {
    let start = unicode.as_ptr();
    let length = unicode.len() as u32;
    let mut bytes = unicode.iter();

    let (mut lines, mut multibyte_chars) = (vec![RelativePosition(0)], vec![]);

    let mut offset = 0;
    while let Some(char) = next_code_point(&mut bytes) {
        let char = char::from_u32_unchecked(char);

        let char_len = char.len_utf8();
        if char_len >= 2 {
            multibyte_chars.push(MultibyteChar {
                pos: RelativePosition(offset),
                len: char_len as u8
            });
        } else if char == '\n' && offset < length - 1 {
            // \n (unix)
            lines.push(RelativePosition(offset + 1)); // push the beginning of the line
        } else if char == '\r' && offset < length - 2 && bytes.as_slice()[0] == b'\n' {
            // \r\n (windows)
            bytes.next(); // advance over '\n'
            lines.push(RelativePosition(offset + 2)); // push the beginning of the line
        } else if char == '\r' && offset < length - 1 {
            // \r (osx)
            lines.push(RelativePosition(offset + 1)); // push the beginning of the line
        }

        offset = bytes.as_slice().as_ptr().offset_from(start) as u32;
    }

    (lines, multibyte_chars)
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
                // NOTE: Should we already read into the file cacher here?
                // Maybe the file is invalid utf8 and we're wasting space,
                // But the compilation fails anyways so maybe it doesn't matter
                // FIXME: (from above) maybe we should try to detect different
                // encodings here (utf16, utf16-le-bom (common on windows), utf32, etc)
                // in that case we couldn't write directly into the cacher to begin with
                let (buf, pos);
                if size > 0 {
                    (buf, pos) = storage.new_buffer(size);
                    f.read_exact(buf)?;
                } else {
                    (buf, pos) = (&mut [], 0);
                }
                Ok((buf, pos as u32, size as u32))
            })
            .map_err(|err| {
                let file = FileCacher::decode_path(path);
                eprintln!("ERROR: couldn't read {file}: {err}");
            })?;
        let mut files = self.files.borrow_mut();
        let source = Rc::new(File::new(path.to_owned(), contents, Span::new(pos, pos + len)));
        if len > 0 {
            files.push(source.clone());
        }
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


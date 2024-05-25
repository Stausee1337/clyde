use std::cell::RefCell;
use std::mem::transmute;
use std::ops::{Range, Deref};
use std::fmt::Write;
use std::os::raw::c_void;
use std::hash::Hash;

use bitflags::bitflags;

use crate::context::GlobalCtxt;

pub trait JoinToHumanReadable {
    fn join_to_human_readable(&self) -> String;
}

impl JoinToHumanReadable for Vec<String> {
    fn join_to_human_readable(&self) -> String {
        let mut result = String::new();
        for (idx, item) in self.iter().enumerate() {
            let needle = self.len().checked_sub(2);
            let glue = if idx < needle.unwrap_or(0) { ", " }
            else if Some(idx) == needle { " or " }
            else { "" };
            write!(result, "{item}{glue}").unwrap();
        }
        result
    }
}

bitflags! {
    pub struct HappenedEvents: u8 {
        const WARNING = 0b0001;
        const ERROR = 0b0010;
        const FATAL = 0b0100;
    }
}

pub struct DiagnosticsData {
    pub source: String,
    pub filename: String,
    events: RefCell<Vec<Reported>>,
    flags: RefCell<HappenedEvents>
}

impl DiagnosticsData {
    pub fn new(filename: String, source: String) -> Self {
        Self {
            filename,
            source,
            events: RefCell::new(Vec::new()),
            flags: RefCell::new(HappenedEvents::empty())
        }
    }

    fn push_event(&self, kind: DiagnosticKind, message: String) -> &mut Reported {
        let mut events = self.events.borrow_mut();
        events.push(Reported {
            kind,
            message,
            location: Where::Unspecified 
        });
        unsafe { transmute::<&mut Reported, &mut Reported>(events.last_mut().unwrap()) }
    }

    pub fn error<T: Into<String>>(&self, message: T) -> &mut Reported {
        self.flags.borrow_mut().insert(HappenedEvents::ERROR);
        self.push_event(DiagnosticKind::Error, message.into())
    }

    pub fn fatal<T: Into<String>>(&self, message: T) -> &mut Reported {
        self.flags.borrow_mut().insert(HappenedEvents::FATAL);
        self.push_event(DiagnosticKind::Fatal, message.into())
    }

    pub fn warning<T: Into<String>>(&self, message: T) -> &mut Reported {
        self.flags.borrow_mut().insert(HappenedEvents::WARNING);
        self.push_event(DiagnosticKind::Warning, message.into())
    }

    pub fn note<T: Into<String>>(&self, message: T) -> &mut Reported {
        self.push_event(DiagnosticKind::Note, message.into())
    }

    pub fn has_error(&self) -> bool {
        self.flags.borrow().contains(HappenedEvents::ERROR)
    }

    pub fn has_warning(&self) -> bool {
        self.flags.borrow().contains(HappenedEvents::WARNING)
    }

    pub fn has_fatal(&self) -> bool {
        self.flags.borrow().contains(HappenedEvents::FATAL)
    }

    pub fn print_diagnostics(&self) {
        for event in self.events.borrow().iter() {
            let source_pos = event.location.pos_in_source(&self.source);
            eprintln!("{}: {}:{}: {}",
                event.kind,
                self.filename,
                source_pos.map(|SourcePosition { position: (row, col), .. }| format!("{row}:{col}"))
                    .unwrap_or(String::new()),
                event.message);
            if event.location.has_span() {
                let source_pos = source_pos.unwrap();
                let lineno = source_pos.position.0.to_string();
                eprintln!(" {lineno}|{line}", line = source_pos.line(&self.source));
                eprintln!(" {npad}|{lpad}{span}",
                    npad = " ".repeat(lineno.len()), lpad = " ".repeat(source_pos.position.1 - 1),
                    span = "^".repeat(event.location.len().unwrap()));
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct Diagnostics<'tcx>(&'tcx DiagnosticsData);

impl<'tcx> std::cmp::PartialEq for Diagnostics<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            let a = transmute::<Diagnostics, *const c_void>(*self);
            let b = transmute::<Diagnostics, *const c_void>(*other);

            a == b
        }
    }
}

impl<'tcx> std::cmp::Eq for Diagnostics<'tcx> {}

impl<'tcx> std::fmt::Debug for Diagnostics<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Diagnostics({:?})", self.filename)
    }
}

impl<'tcx> Deref for Diagnostics<'tcx> {
    type Target = DiagnosticsData;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

pub struct Reported {
    kind: DiagnosticKind,
    message: String,
    location: Where
}

impl Reported {
    pub fn with_span(&mut self, span: Range<usize>) -> &mut Self {
        self.location = Where::Span(span);
        self
    }

    pub fn with_pos(&mut self, pos: usize) -> &mut Self {
        self.location = Where::Position(pos);
        self
    }
}

enum DiagnosticKind {
    Error, Fatal, Warning, Note
}

impl std::fmt::Display for DiagnosticKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            DiagnosticKind::Error => "ERROR",
            DiagnosticKind::Fatal => "FATAL",
            DiagnosticKind::Note => "NOTE",
            DiagnosticKind::Warning => "WARN"
        })
    }
}

enum Where {
    Unspecified,
    Position(usize),
    Span(Range<usize>)
}

impl Where {
    fn pos_in_source(&self, source: &str) -> Option<SourcePosition> {
        let pos = match self {
            Where::Unspecified => return None,
            Where::Position(pos) => *pos,
            Where::Span(Range { start, .. }) => *start
        };

        let mut bol = 0;
        let mut line = 1;
        for (offset, char) in source.chars().enumerate() {
            if offset == pos {
                return Some(SourcePosition {
                    position: (line, offset - bol),
                    bol
                });
            } else if char == '\n' {
                bol = offset;
                line += 1;
            }
        }
        None
    }

    fn has_span(&self) -> bool {
        match self {
            Where::Span(..) => true,
            _ => false
        }
    }

    fn len(&self) -> Option<usize> {
        Some(match self {
            Where::Span(span) => span.len(),
            Where::Position(..) => 0,
            _ => return None
        })
    }
}

#[derive(Clone, Copy)]
struct SourcePosition {
    position: (usize, usize),
    bol: usize
}

impl SourcePosition {
    fn line<'s>(&self, source: &'s str) -> &'s str {
        let line = &source[self.bol+1..];
        &line[..line.find('\n').unwrap_or(line.len() - 1)]
    }
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn diagnostics_for(&self, filename: String, source: String) -> Diagnostics<'tcx> {
        use crate::context::Interner;
        Diagnostics(
            self.interners.diagnostics.intern(filename, |filename| {
                self.interners.alloc(DiagnosticsData::new(filename, source))
            })
        )
    }

    pub fn all_diagnostics(&'tcx self) -> impl Iterator<Item = Diagnostics<'tcx>> {
        struct DiagnosticsIterator<'tcx> {
            ctxt: &'tcx GlobalCtxt<'tcx>,
            hashes: Vec<u64>,
            index: usize
        }

        impl<'tcx> Iterator for DiagnosticsIterator<'tcx> {
            type Item = Diagnostics<'tcx>;

            fn next(&mut self) -> Option<Self::Item> {
                if self.index >= self.hashes.len() {
                    return None;
                }
                let diag = *self.ctxt.interners.diagnostics.borrow().get(&self.hashes[self.index]).unwrap();
                self.index += 1;
                Some(Diagnostics(unsafe { transmute::<&DiagnosticsData, &'tcx DiagnosticsData>(diag) }))
            }
        }

        DiagnosticsIterator {
            ctxt: self,
            hashes: self.interners.diagnostics.borrow().keys().map(|k| *k).collect(),
            index: 0
        }
    }

    pub fn has_fatal_errors(&'tcx self) -> bool {
        self.all_diagnostics().any(|diag| diag.has_fatal())
    }
}

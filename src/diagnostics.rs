use std::cell::RefCell;
use std::mem::transmute;
use std::ops::{Range, Deref};
use std::fmt::Write;
use std::os::raw::c_void;
use std::hash::Hash;
use std::path::Path;

use bitflags::bitflags;

use crate::{context::{GlobalCtxt, TyCtxt}, interface, queries::caches::QueryCache};

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

pub struct DiagnosticsData<'tcx> {
    pub source: &'tcx str,
    pub filename: &'tcx str,
    events: RefCell<Vec<Reported>>,
    flags: RefCell<HappenedEvents>
}

impl<'tcx> DiagnosticsData<'tcx> {
    pub fn new(path: &'tcx Path, source: &'tcx str) -> Self {
        let filename = unsafe { interface::path_as_str(&path) };

        Self {
            source, filename,
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
        let mut events = self.events.take();
        events.sort_by(|a, b| {
            let pos_a = match &a.location {
                Where::Span(span) => span.start,
                Where::Position(pos) => *pos,
                Where::Unspecified => usize::MAX
            };
            let pos_b = match &b.location {
                Where::Span(span) => span.start,
                Where::Position(pos) => *pos,
                Where::Unspecified => usize::MAX
            };
            pos_a.cmp(&pos_b)
        });
        for event in &events {
            let source_positions = event.location.pos_in_source(&self.source);
            eprintln!("{}: {}:{}: {}",
                event.kind,
                self.filename,
                source_positions.first()
                    .map(|SourcePosition { position: (row, col), .. }| format!("{row}:{col}"))
                    .unwrap_or(String::new()),
                event.message);
            if event.location.has_span() {
                for (idx, source_pos) in source_positions.iter().enumerate() {
                    let lineno = source_pos.position.0.to_string();
                    eprintln!(" {lineno}|{line}", line = source_pos.line(&self.source));
                    if idx == 0 || idx == source_positions.len() - 1 {
                        eprintln!(" {npad}|{lpad}{span}",
                            npad = " ".repeat(lineno.len()), lpad = " ".repeat(source_pos.position.1 - 1),
                            span = "^".repeat(source_pos.length));
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct Diagnostics<'tcx>(pub &'tcx DiagnosticsData<'tcx>);

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
        write!(f, "Diagnostics(file: {:?})", self.filename)
    }
}

impl<'tcx> Deref for Diagnostics<'tcx> {
    type Target = DiagnosticsData<'tcx>;

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
            DiagnosticKind::Warning => "WARNING"
        })
    }
}

enum Where {
    Unspecified,
    Position(usize),
    Span(Range<usize>)
}

impl Where {
    fn pos_in_source(&self, source: &str) -> Vec<SourcePosition> {
        let (start, end) = match self {
            Where::Unspecified => return vec![],
            Where::Position(pos) => (*pos, *pos),
            Where::Span(Range { start, end }) => (*start, *end)
        };

        let mut bol = 0;
        let mut line = 1;
        let mut positions = vec![];
        let mut line_flushed = false;
        for (offset, char) in source.chars().enumerate() {
            if offset >= start && offset <= end && !line_flushed {
                positions.push(SourcePosition {
                    bol,
                    length: 0,
                    position: (line, offset - bol),
                });
                line_flushed = true;
            } else if offset > end {
                if let Some(pos) = positions.last_mut() {
                    pos.length = (offset - 1) - (pos.position.1 + pos.bol);
                }
                break;
            }

            if char == '\n' {
                if let Some(pos) = positions.last_mut() {
                    pos.length = offset - (pos.position.1 + bol);
                }
                bol = offset;
                line += 1;
                line_flushed = false;
            }
        }
        positions
    }

    fn has_span(&self) -> bool {
        match self {
            Where::Span(..) => true,
            _ => false
        }
    }
}

#[derive(Clone)]
struct SourcePosition {
    position: (usize, usize),
    bol: usize,
    length: usize
}

impl SourcePosition {
    fn line<'s>(&self, source: &'s str) -> &'s str {
        let line = &source[self.bol+1..];
        &line[..line.find('\n').unwrap_or(line.len() - 1)]
    }
}

impl<'tcx> GlobalCtxt<'tcx> {
    pub fn all_diagnostics<F: FnMut(Diagnostics<'tcx>)>(&'tcx self, mut _f: F) {
        todo!()
    }

    pub fn has_fatal_errors(&'tcx self) -> bool {
        let mut has_fatal_errors = false;
        self.all_diagnostics(|diag| has_fatal_errors |= diag.has_fatal());
        has_fatal_errors
    }

    pub fn has_errors(&'tcx self) -> bool {
        let mut has_errors = false;
        self.all_diagnostics(|diag| has_errors |= diag.has_error());
        has_errors
    }
}


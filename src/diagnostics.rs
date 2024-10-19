use std::{cell::RefCell, rc::Rc};
use std::mem::transmute;
use std::ops::Range;
use std::fmt::Write;
use std::hash::Hash;

use bitflags::bitflags;

use crate::interface::FileCacher;

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
        const FATAL = 0b10;
        const ERROR = 0b01;
    }
}

struct DiagnosticsCtxtInner {
    file_cacher: Rc<FileCacher>,
    events: Vec<Reported>,
    flags: HappenedEvents
}

impl DiagnosticsCtxtInner {
    fn push_event<'a>(&mut self, kind: DiagnosticKind, message: String) -> &'a mut Reported {
        self.events.push(Reported {
            kind,
            message,
            location: Where::Unspecified 
        });
        unsafe { transmute::<&mut Reported, &mut Reported>(self.events.last_mut().unwrap()) }
    }

    pub fn render(&mut self) {
        self.events.sort_by(|a, b| {
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
        for event in &self.events {
            let location = match &event.location {
                Where::Span(span) => span.start,
                Where::Position(pos) => *pos,
                Where::Unspecified => todo!()
            };
            let file_idx = self.file_cacher.lookup_file(location);
            let source = std::str::from_utf8(self.file_cacher.entire_file_contents(file_idx))
                .expect("FIXME: this error message shouldn't be here");
            let path = self.file_cacher.file_path(file_idx);
            let source_positions = event.location.pos_in_source(source);
            eprintln!("{}: {}:{}: {}",
                event.kind,
                path,
                source_positions.first()
                    .map(|SourcePosition { position: (row, col), .. }| format!("{row}:{col}"))
                    .unwrap_or(String::new()),
                event.message);
            if event.location.has_span() {
                for (idx, source_pos) in source_positions.iter().enumerate() {
                    let lineno = source_pos.position.0.to_string();
                    eprintln!(" {lineno}|{line}", line = source_pos.line(source));
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

pub struct DiagnosticsCtxt(RefCell<DiagnosticsCtxtInner>);

impl DiagnosticsCtxt { 
    pub fn new(file_cacher: Rc<FileCacher>) -> DiagnosticsCtxt {
        let inner = DiagnosticsCtxtInner {
            file_cacher,
            events: Vec::new(),
            flags: HappenedEvents::empty()
        };
        DiagnosticsCtxt(RefCell::new(inner))
    }

    pub fn render(&self) {
        self.0.borrow_mut().render();
    }

    pub fn error<T: Into<String>>(&self, message: T) -> &mut Reported {
        let mut inner = self.0.borrow_mut();
        inner.flags |= HappenedEvents::ERROR;
        inner.push_event(DiagnosticKind::Error, message.into())
    }

    pub fn fatal<T: Into<String>>(&self, message: T) -> &mut Reported {
        let mut inner = self.0.borrow_mut();
        inner.flags |= HappenedEvents::FATAL;
        inner.push_event(DiagnosticKind::Fatal, message.into())
    }

    pub fn warning<T: Into<String>>(&self, message: T) -> &mut Reported {  
        self.0.borrow_mut().push_event(DiagnosticKind::Warning, message.into())
    }

    pub fn note<T: Into<String>>(&self, message: T) -> &mut Reported {
        self.0.borrow_mut().push_event(DiagnosticKind::Note, message.into())
    }

    pub fn has_error(&self) -> bool {
        self.0.borrow().flags.contains(HappenedEvents::ERROR)
    }

    pub fn has_fatal(&self) -> bool {
        self.0.borrow().flags.contains(HappenedEvents::FATAL)
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


use std::cell::OnceCell;
use std::{cell::RefCell, rc::Rc};
use std::hash::Hash;

use bitflags::bitflags;

use crate::interface::File;
use crate::{interface::FileCacher, lexer::Span};

bitflags! {
    pub struct HappenedEvents: u8 {
        const FATAL = 0b10;
        const ERROR = 0b01;
    }
}

pub struct InternalMessage {
    kind: MessageKind,
    span: Span,
    message: String,
    hint: Option<(String, Span)>,
    note: Option<String>
}

struct DiagnosticsCtxtInner {
    file_cacher: Rc<FileCacher>,
    messages: Vec<InternalMessage>,
    flags: HappenedEvents,
}

impl DiagnosticsCtxtInner {
    fn push_event<'a>(&mut self, message: InternalMessage) {
        self.messages.push(message);
    }

    pub fn render(&mut self) {
        self.messages.sort_by(
            |a, b| a.span.start.cmp(&b.span.start));
        for message in &self.messages {
            let file = self.file_cacher.lookup_file(message.span.start);

            let (row, col) = file.decode_to_file_pos(message.span.start);
            eprintln!("{}:{row}:{col}: {}: {}",
                file.path(),
                message.kind,
                message.message);

            let mut pre_hint = None;
            let mut post_hint = None;
            if let Some(hint) = &message.hint {
                if hint.1.start < message.span.start {
                    pre_hint = Some(hint);
                } else {
                    post_hint = Some(hint);
                }
            }

            if let Some(pre_hint) = pre_hint {
                render_code(&file, pre_hint.1, "-", Some(&pre_hint.0));
            }

            render_code(&file, message.span, "^", None);

            if let Some(post_hint) = post_hint {
                render_code(&file, post_hint.1, "-", Some(&post_hint.0));
            }

            if let Some(note) = &message.note {
                eprintln!("  -> NOTE: {note}");
            }
        }
    }
}

fn render_code(file: &File, span: Span, decoration: &'static str, annotation: Option<&str>) {
    let mut row = file.decode_to_lineno(span.start).unwrap();
    let end_row = file.decode_to_lineno(span.end).unwrap();

    while row <= end_row {
        let char_start = file.unicode_slice(span.start);
        let char_end = file.unicode_slice(span.end);
        eprintln!(" {row}|{line}", line = file.get_line(row - 1));
        eprintln!(" {npad}|{lpad}{span} {annotation}",
                  npad = " ".repeat(format!("{row}").len()), lpad = " ".repeat(char_start),
                  span = decoration.repeat(char_end - char_start),
                  annotation = annotation.unwrap_or(""));
        row += 1;
    }
}

pub struct DiagnosticsCtxt(RefCell<DiagnosticsCtxtInner>);

impl DiagnosticsCtxt { 
    pub fn new(file_cacher: Rc<FileCacher>) -> DiagnosticsCtxt {
        let inner = DiagnosticsCtxtInner {
            file_cacher,
            messages: Vec::new(),
            flags: HappenedEvents::empty()
        };
        DiagnosticsCtxt(RefCell::new(inner))
    }

    pub fn render(&self) {
        self.0.borrow_mut().render();
    }

    pub fn has_error(&self) -> bool {
        self.0.borrow().flags.contains(HappenedEvents::ERROR)
    }

    pub fn has_fatal(&self) -> bool {
        self.0.borrow().flags.contains(HappenedEvents::FATAL)
    }
}

pub struct Message {
    kind: MessageKind,
    message: String,
    note: OnceCell<String>,
    hint: OnceCell<(String, Span)>,
    location: OnceCell<Span>
}

impl Message {
    fn new(kind: MessageKind, message: String) -> Self {
        Self {
            kind, message,
            note: OnceCell::new(),
            hint: OnceCell::new(),
            location: OnceCell::new()
        }
    }

    #[must_use]
    pub fn warning<T: Into<String>>(message: T) -> Self {  
        Self::new(MessageKind::Warning, message.into())
    }

    #[must_use]
    pub fn error<T: Into<String>>(message: T) -> Self {  
        Self::new(MessageKind::Error, message.into()) 
    }

    #[must_use]
    pub fn fatal<T: Into<String>>(message: T) -> Self {   
        Self::new(MessageKind::Fatal, message.into()) 
    }

    #[must_use]
    pub fn at(self, span: Span) -> Self {
        self.location.set(span)
            .unwrap();
        self
    }

    #[must_use]
    pub fn note<T: Into<String>>(self, message: T) -> Self {
        self.note.set(message.into())
            .unwrap();
        self
    }

    #[must_use]
    pub fn hint<T: Into<String>>(self, message: T, span: Span) -> Self {
        self.hint.set((message.into(), span)).unwrap();
        self
    }

    pub fn push(self, _diagnostics: &DiagnosticsCtxt) {
        todo!()
    }
}

// Message::warning(format!())
//  .at(span)
//  .note(format!())
//  .push(diagnostics);

enum MessageKind {
    Error, Fatal, Warning
}

impl std::fmt::Display for MessageKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            MessageKind::Error => "error",
            MessageKind::Fatal => "fatal",
            MessageKind::Warning => "warning"
        })
    }
}


/*fn pos_in_source(&self, source: &str) -> Vec<SourcePosition> {
    let (start, end) = match self {
        Where::Unspecified => return vec![],
        Where::Position(pos) => (*pos, *pos),
        Where::Span(Span { start, end }) => (*start, *end)
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
    todo!()
}*/


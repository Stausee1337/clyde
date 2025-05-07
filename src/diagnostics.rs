use std::cell::OnceCell;
use std::{cell::RefCell, rc::Rc};

use crate::{files::{File, RelativePosition, FileCacher}, syntax::lexer::Span};

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
            let to_relative_span = |span: Span| (
                file.relative_position(span.start),
                file.relative_position(span.end)
            );

            let file_realtive_span = to_relative_span(message.span);

            let (row, col) = file.decode_to_file_pos(file_realtive_span.0);
            eprintln!("{}:{row}:{col}: {}: {}",
                file.str_path(),
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
                render_code(&file, to_relative_span(pre_hint.1), "-", Some(&pre_hint.0));
            }

            render_code(&file, file_realtive_span, "^", None);

            if let Some(post_hint) = post_hint {
                render_code(&file, to_relative_span(post_hint.1), "-", Some(&post_hint.0));
            }

            if let Some(note) = &message.note {
                eprintln!("  -> NOTE: {note}");
            }
        }
    }
}

fn render_code(file: &File, span: (RelativePosition, RelativePosition), decoration: &'static str, annotation: Option<&str>) {
    let start_row = file.decode_to_lineno(span.0).unwrap();
    let end_row = file.decode_to_lineno(span.1).unwrap();

    let span_start = file.pos_to_charpos(span.0);
    let span_end = file.pos_to_charpos(span.1);

    for row in start_row..=end_row {
        let line_start = file.pos_to_charpos(file.lines()[row]);
        let line = file.get_line(row).unwrap_or("");

        let char_start;
        if row == start_row {
            char_start = span_start;
        } else {
            char_start = line_start;
        }

        let char_end;
        if row == end_row {
            char_end = span_end;
        } else {
            char_end = line_start + line.chars().count();
        }

        eprintln!(" {}| {line}", row + 1);
        if line.len() > 0 {
            eprintln!(" {npad}| {lpad}{span} {annotation}",
                      npad = " ".repeat(num_digits(row + 1)), lpad = " ".repeat(char_start - line_start),
                      span = decoration.repeat(char_end - char_start),
                      annotation = annotation.unwrap_or(""));
        }
    }
}

fn num_digits(n: usize) -> usize {
    if n == 0 {
        return 1;
    }
    (n as f64).log10().floor() as usize + 1
}

pub struct DiagnosticsCtxt(RefCell<DiagnosticsCtxtInner>);

impl DiagnosticsCtxt { 
    pub fn new(file_cacher: Rc<FileCacher>) -> DiagnosticsCtxt {
        let inner = DiagnosticsCtxtInner {
            file_cacher,
            messages: Vec::new(),
        };
        DiagnosticsCtxt(RefCell::new(inner))
    }

    pub fn render(&self) {
        self.0.borrow_mut().render();
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

    pub fn push(self, diagnostics: &DiagnosticsCtxt) {
        let Self { kind, message, note, hint, location } = self;
        let message = InternalMessage {
            kind, message,
            span: location.into_inner().unwrap(),
            note: note.into_inner(),
            hint: hint.into_inner() 
        };
        diagnostics.0
            .borrow_mut()
            .push_event(message);
    }
}

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


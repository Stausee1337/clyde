use std::{fmt::Write, marker::PhantomData, ops::{Deref, DerefMut}};

use crate::{diagnostics::{DiagnosticsCtxt, Message}, files::{File, Utf8Error}, string_internals};
use super::symbol::Symbol;
use clyde_macros::{LexFromString, Operator};

use tinyvec::ArrayVec;

pub(crate) trait Operator: Sized {
    fn from_punct(punct: Punctuator) -> Option<Self>;
}

#[macro_export]
macro_rules! Token {
    [_] => { crate::syntax::lexer::Punctuator::Underscore };
    [.] => { crate::syntax::lexer::Punctuator::Dot };
    [,] => { crate::syntax::lexer::Punctuator::Comma };
    [:] => { crate::syntax::lexer::Punctuator::Colon };
    [::] => { crate::syntax::lexer::Punctuator::DoubleColon };
    [;] => { crate::syntax::lexer::Punctuator::Semicolon };
    [=] => { crate::syntax::lexer::Punctuator::Assign };
    [..] => { crate::syntax::lexer::Punctuator::DotDot };
    [->] => { crate::syntax::lexer::Punctuator::Arrow };
    [^] => { crate::syntax::lexer::Punctuator::Circumflex };
    [?] => { crate::syntax::lexer::Punctuator::Question };

    [&] => { crate::syntax::lexer::Punctuator::Ampersand };
    [|] => { crate::syntax::lexer::Punctuator::VBar };
    [~] => { crate::syntax::lexer::Punctuator::Tilde };

    [<<] => { crate::syntax::lexer::Punctuator::LDoubleChevron };
    [>>] => { crate::syntax::lexer::Punctuator::RDoubleChevron };

    [+] => { crate::syntax::lexer::Punctuator::Plus };
    [-] => { crate::syntax::lexer::Punctuator::Minus };
    [*] => { crate::syntax::lexer::Punctuator::Star };
    [/] => { crate::syntax::lexer::Punctuator::Slash };
    [%] => { crate::syntax::lexer::Punctuator::Percent };

    [<] => { crate::syntax::lexer::Punctuator::LChevron };
    [<=] => { crate::syntax::lexer::Punctuator::LChevronEq };
    [>] => { crate::syntax::lexer::Punctuator::RChevron };
    [>=] => { crate::syntax::lexer::Punctuator::RChevronEq };
    [==] => { crate::syntax::lexer::Punctuator::DoubleEq };
    [!=] => { crate::syntax::lexer::Punctuator::BangEq };

    [&&] => { crate::syntax::lexer::Punctuator::DoubleAmpersand };
    [||] => { crate::syntax::lexer::Punctuator::DoubleVBar };
    [!] => { crate::syntax::lexer::Punctuator::Bang };

    [:=] => { crate::syntax::lexer::Punctuator::ColonAssign };

    [+=] => { crate::syntax::lexer::Punctuator::PlusAssign };
    [-=] => { crate::syntax::lexer::Punctuator::MinusAssing };
    [*=] => { crate::syntax::lexer::Punctuator::StarAssign };
    [/=] => { crate::syntax::lexer::Punctuator::SlashAssign };
    [%=] => { crate::syntax::lexer::Punctuator::PercentAssign };

    [||=] => { crate::syntax::lexer::Punctuator::DoubleVBarAssign };
    [&&=] => { crate::syntax::lexer::Punctuator::DoubleAnpersandAssign };
    [^=] => { crate::syntax::lexer::Punctuator::CircumflexAssign };

    [<<=] => { crate::syntax::lexer::Punctuator::LDoubleChevronAssign };
    [>>=] => { crate::syntax::lexer::Punctuator::RDoubleChevronAssign };

    [&=] => { crate::syntax::lexer::Punctuator::AnpersandAssign };
    [|=] => { crate::syntax::lexer::Punctuator::VBarAssign };

    [++] => { crate::syntax::lexer::Punctuator::DoublePlus };
    [--] => { crate::syntax::lexer::Punctuator::DoubleMinus };



    [const] => { crate::syntax::lexer::Keyword::Const };
    [use] => { crate::syntax::lexer::Keyword::Use };
    [with] => { crate::syntax::lexer::Keyword::With };
    [var] => { crate::syntax::lexer::Keyword::Var };
    [static] => { crate::syntax::lexer::Keyword::Static };
    [cast] => { crate::syntax::lexer::Keyword::Cast };
    [transmute] => { crate::syntax::lexer::Keyword::Transmute };
    [out] => { crate::syntax::lexer::Keyword::Out };
    [is] => { crate::syntax::lexer::Keyword::Is };
    [extern] => { crate::syntax::lexer::Keyword::Extern };
    [while] => { crate::syntax::lexer::Keyword::While };
    [for] => { crate::syntax::lexer::Keyword::For };
    [in] => { crate::syntax::lexer::Keyword::In };
    [if] => { crate::syntax::lexer::Keyword::If };
    [else] => { crate::syntax::lexer::Keyword::Else };
    [struct] => { crate::syntax::lexer::Keyword::Struct };
    [enum] => { crate::syntax::lexer::Keyword::Enum };
    [return] => { crate::syntax::lexer::Keyword::Return };
    [break] => { crate::syntax::lexer::Keyword::Break };
    [continue] => { crate::syntax::lexer::Keyword::Continue };
    [yeet] => { crate::syntax::lexer::Keyword::Yeet };
    [template] => { crate::syntax::lexer::Keyword::Template };
    [interface] => { crate::syntax::lexer::Keyword::Interface };
    [closure] => { crate::syntax::lexer::Keyword::Closure };
    [true] => { crate::syntax::lexer::Keyword::True };
    [false] => { crate::syntax::lexer::Keyword::False };
    [null] => { crate::syntax::lexer::Keyword::Null };

    [#scope] => { crate::syntax::lexer::Directive::Scope };
    [#link] => { crate::syntax::lexer::Directive::Link };
    [#c_call] => { crate::syntax::lexer::Directive::CCall };
    [#include] => { crate::syntax::lexer::Directive::Include };
    [#compiler_intrinsic] => { crate::syntax::lexer::Directive::CompilerIntrinsic };
}

macro_rules! must {
    ($e:expr) => {
        match $e {
            Some(chr) => chr,
            None => return Err(LexErrorKind::UnexpectedEOS),
        }
    };
}

macro_rules! goto {
    ($state:ident) => {{
        return Ok(LexState::$state);
    }};
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(usize)]
enum LexState {
    Initial = 0,
    CommentOrPunct = 1,
    CharOrStringLiteral = 2,
    SymbolDirectiveOrKeyword = 3,
    NumberLiteral = 4,
    PunctOrError = 5,
    Comment = 6,
    IntegerLiteral = 7,

    End,
    EOS
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LexErrorKind {
    UnexpectedEOS,
    InvalidCharacter(char),
    IncompleteIntegerLiteral,
    NonDecimalFloatingPointLiteral,
    UnknownDirective(Symbol),
    StringError(StringError),
}

#[derive(Debug, Clone, Copy)]
struct LexError {
    kind: LexErrorKind,
    span: Span
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.end - self.start).cmp(&(other.end - other.start))
    }
}

impl Span {
    pub const NULL: Self = Span::new(0, 0);

    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub const fn zero() -> Span {
        Span::new(0, 0)
    }

    pub const fn interpolate(start: Span, end: Span) -> Self {
        Self {
            start: start.start,
            end: end.end
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StringKind {
    String, Char
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringError {
    UnclosedLiteral,
    EmptyCharLiteral,
    MultiCharLiteral,
    UnknownCharEscape,
    InvalidCharInHexByte,
    InvalidCharInUnicodeLiteral,
    NonUnicodeCharInLiteral
}

#[derive(PartialEq, Eq)]
pub enum StringParseState {
    Normal,
    Escape,
    HexByte(ArrayVec<[u8; 2]>),
    Unicode {
        data: ArrayVec<[u8; 8]>,
        is_long: bool
    },
    Ended
}

pub struct StringParser {
    kind: StringKind,
    state: StringParseState,
    length: usize,
}

impl StringParser {
    pub fn new(kind: StringKind) -> Self {
        Self {
            kind,
            state: StringParseState::Normal,
            length: 0
        }
    }

    fn normal(&mut self, char: char) -> Result<Option<char>, StringError> {
        match char {
            '\\' => self.state = StringParseState::Escape,
            '\n' | '\r' => {
                self.state = StringParseState::Ended;
                return Err(StringError::UnclosedLiteral)
            },
            '\'' if self.kind == StringKind::Char => {
                self.state = StringParseState::Ended;
                if self.length < 1 {
                    return Err(StringError::EmptyCharLiteral);
                } else if self.length > 1 {
                    return Err(StringError::MultiCharLiteral);
                }
            }
            '"' if self.kind == StringKind::String => {
                self.state = StringParseState::Ended;
            }
            _ => return Ok(Some(char)),
        }
        return Ok(None);
    }

    fn escape(&mut self, char: char) -> Result<Option<char>, StringError> {
        let result = match char {
            'a' => '\x07',
            'b' => '\x08',
            'f' => '\x0C',
            'n' => '\x0A',
            'r' => '\x0D',
            't' => '\x09',
            'v' => '\x0B',
            '\\' => '\\',
            '\'' if self.kind == StringKind::Char => '\'',
            '"' if self.kind == StringKind::String => '"',
            'x' => {
                self.state = StringParseState::HexByte(ArrayVec::new());
                return Ok(None);
            }
            'u' | 'U' => {
                self.state = StringParseState::Unicode {
                    data: ArrayVec::new(),
                    is_long: char.is_ascii_uppercase()
                };
                return Ok(None);
            }
            _ => return Err(StringError::UnknownCharEscape)
        };
        self.state = StringParseState::Normal;
        Ok(Some(result))
    }

    fn hex_byte(&mut self, char: char) -> Result<Option<char>, StringError> {
        let StringParseState::HexByte(ref mut vec) = self.state else {
            unreachable!();
        };
        let (('a'..='f') | ('A'..='F') | ('0'..='9')) = char else {
            self.state = StringParseState::Normal;
            return Err(StringError::InvalidCharInHexByte);
        };
        vec.push(char as u8);
        if vec.len() == 2 {
            let src = unsafe { std::str::from_utf8_unchecked(vec.as_slice()) };
            let char = u8::from_str_radix(src, 16).unwrap();
            self.state = StringParseState::Normal;
            return Ok(Some(char as char));
        }
        return Ok(None);
    }

    fn unicode(&mut self, char: char) -> Result<Option<char>, StringError> {
        let StringParseState::Unicode { ref mut data, is_long } = self.state else {
            unreachable!();
        };
        let (('a'..='f') | ('A'..='F') | ('0'..='9')) = char else {
            self.state = StringParseState::Normal;
            return Err(StringError::InvalidCharInUnicodeLiteral);
        };
        data.push(char as u8);
        if data.len() == 4 && !is_long {
            let src = unsafe { std::str::from_utf8_unchecked(data.as_slice()) };
            let number = u32::from_str_radix(src, 16).unwrap();
            self.state = StringParseState::Normal;
            let Some(unichar) = char::from_u32(number) else {
                return Err(StringError::NonUnicodeCharInLiteral);
            };
            return Ok(Some(unichar));
        } else if data.len() == 8 && is_long {
            let src = unsafe { std::str::from_utf8_unchecked(data.as_slice()) };
            let number = u32::from_str_radix(src, 16).unwrap();
            self.state = StringParseState::Normal;
            let Some(unichar) = char::from_u32(number) else {
                return Err(StringError::NonUnicodeCharInLiteral);
            };
            return Ok(Some(unichar));
        }

        return Ok(None);
    }

    pub fn feed(&mut self, char: char) -> Result<Option<char>, StringError> {
        let result = match self.state {
            StringParseState::Normal => self.normal(char)?,
            StringParseState::Escape => self.escape(char)?,
            StringParseState::HexByte(..) => self.hex_byte(char)?,
            StringParseState::Unicode { .. } => self.unicode(char)?,
            StringParseState::Ended =>
                panic!("calling feed(..) on ended StringParser")
        };
        if result.is_some() {
            self.length += 1;
        }
        return Ok(result);
    }

    pub fn ended(&self) -> bool {
        self.state == StringParseState::Ended
    }
}

pub trait Tokenish: std::fmt::Display {
    fn matches(&self, tok: Token) -> bool;
}

impl Tokenish for Symbol {
    fn matches(&self, tok: Token) -> bool {
        if let TokenKind::Symbol(sym) = tok.kind {
            return *self == sym;
        }
        false
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Token<'a> {
    pub kind: TokenKind<'a>,
    pub span: Span
}

#[derive(Debug, Clone, Copy)]
pub enum TokenKind<'a> {
    Keyword(Keyword),
    Directive(Directive),
    Punctuator(Punctuator),
    Literal(&'a str, LiteralKind),
    Symbol(Symbol),
    EOS
}

#[derive(Debug, Clone, Copy)]
pub enum LiteralKind {
    IntNumber(NumberMode), FloatingPoint,
    String, Char
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NumberMode {
    Binary,
    Octal,
    Decimal,
    Hex
}

impl<'a> std::fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('`')?;
        match self.kind {
            TokenKind::Keyword(keyword) =>
                std::fmt::Display::fmt(&keyword, f),
            TokenKind::Punctuator(punct) =>
                std::fmt::Display::fmt(&punct, f),
            TokenKind::Directive(directive) =>
                write!(f, "#{}", directive),
            TokenKind::Symbol(symbol) =>
                f.write_str(symbol.get()),
            TokenKind::Literal(repr, _) =>
                f.write_str(repr),
            TokenKind::EOS =>
                f.write_str("<eof>"),
        }?;
        f.write_char('`')
    }
}

pub struct TokenStream<'a> {
    tokens: Vec<Token<'a>>,
    tainted_with_errors: bool
}

impl<'a> TokenStream<'a> {
    fn build(tokens: Vec<Token<'a>>, diagnostics: &DiagnosticsCtxt) -> Result<Self, ()> {

        #[derive(PartialEq, Eq)]
        enum Delimiter { Paren, Bracket, Curly }

        macro_rules! indent {
            ($stack:ident, $kind:path, $tok:ident) => {{
                $stack.push(($kind, $tok));
            }};
        }

        macro_rules! dedent {
            ($stack:ident, $kind:path, $tok:ident) => {{
                let Some((kind, start)) = $stack.pop() else {
                    Self::create_delimiter_diagnostic(None, Some(*$tok), diagnostics);
                    return Err(());
                };
                if kind != $kind {
                    Self::create_delimiter_diagnostic(Some(*start), Some(*$tok), diagnostics);
                    return Err(());
                }
            }};
        }

        let mut stack = vec![];
        for tok in &tokens {
            match tok.kind {
                TokenKind::Punctuator(Punctuator::LParen) =>
                    indent!(stack, Delimiter::Paren, tok),
                TokenKind::Punctuator(Punctuator::LCurly) =>
                    indent!(stack, Delimiter::Curly, tok),
                TokenKind::Punctuator(Punctuator::LBracket) =>
                    indent!(stack, Delimiter::Bracket, tok),

                TokenKind::Punctuator(Punctuator::RParen) =>
                    dedent!(stack, Delimiter::Paren, tok),
                TokenKind::Punctuator(Punctuator::RCurly) =>
                    dedent!(stack, Delimiter::Curly, tok),
                TokenKind::Punctuator(Punctuator::RBracket) =>
                    dedent!(stack, Delimiter::Bracket, tok),
                _ => ()
            }
        }

        if let Some((_, tok)) = stack.first() {
            Self::create_delimiter_diagnostic(Some(**tok), None, diagnostics);
            return Err(());
        }

        Ok(Self { tokens, tainted_with_errors: false })
    }

    fn create_delimiter_diagnostic(start: Option<Token<'a>>, end: Option<Token<'a>>, diagnostics: &DiagnosticsCtxt) {
        assert!(start.is_some() || end.is_some());
        let span = end.map_or_else(|| start.unwrap().span, |tok| tok.span);
        let message = match (start, end) {
            (Some(..), Some(..)) => "unmatched closing delimiter",
            (None, Some(..)) => "unexpected closing delimiter",
            (Some(..), None) => "unclosed opening delimiter",
            (None, None) => unreachable!()
        };
        let mut diagmsg = Message::error(message).at(span);
        if let (Some(start), Some(_)) = (start, end) {
            diagmsg = diagmsg.hint("unclosed delimiter", start.span);
        }
        diagmsg.push(diagnostics);
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    pub fn into_boxed_slice(self) -> Box<[Token<'a>]> {
        self.tokens.into_boxed_slice()
    }

    pub fn tainted_with_errors(&self) -> bool {
        self.tainted_with_errors
    }
}

#[derive(Clone)]
struct SourceCursor<'a> {
    current: *const u8,
    _length: usize,
    _position: usize,
    _phantom: PhantomData<&'a ()>
}

impl<'a> SourceCursor<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self {
            current: source.as_ptr(),
            _length: source.len(),
            _position: 0,
            _phantom: PhantomData::default()
        }
    }

    #[doc(hidden)]
    fn _step(&mut self) -> Option<char> {
        if self._position >= self.length() {
            return None;
        }
        unsafe {
            let char = string_internals::next_code_point(self)
                .and_then(char::from_u32)
                .unwrap();

            Some(char)
        }
    }

    #[doc(hidden)]
    fn _lookahead(&mut self) -> Option<char> {
        let mut clone = self.clone();
        clone._step()
    }

    fn length(&self) -> usize {
        self._length
    }

    fn position(&self) -> usize {
        self._position
    }

    fn slice(&self, relative_start: usize, length: usize) -> Option<&'a str> {
        if self.position() - relative_start + length > self.length() {
            return None;
        }
        unsafe { 
            let ptr = self.current.sub(relative_start + 1);
            let slice = std::slice::from_raw_parts(ptr, length);
            Some(std::str::from_utf8(slice)
                 .unwrap())
        }
    }

    fn slice_bytes(&self, relative_start: usize, length: usize) -> Option<&'a [u8]> {
        if self.position() - relative_start + length > self.length() {
            return None;
        }
        unsafe { 
            let ptr = self.current.sub(relative_start + 1);
            let slice = std::slice::from_raw_parts(ptr, length);
            Some(slice)
        }
    }

    fn matches(&self, offset: usize, pattern: &[u8]) -> bool {
        let offset = offset as isize;
        let rem = self.length() - self.position();
        if pattern.len() > rem {
            return false;
        }
        for i in 0..(pattern.len() as isize) {
            let b = unsafe { *self.current.offset(i - offset) };
            if b != pattern[i as usize] {
                return false;
            }
        }
        return true;
    }
}

impl<'a> Iterator for SourceCursor<'a> {
    type Item = &'a u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self._position >= self.length() {
            return None;
        }

        unsafe {
            let prev = self.current;
            self.current = self.current.add(1);
            self._position += 1;
            Some(&*prev)
        }
    }
}

struct Tokenizer<'a> {
    offset: u32,
    bol: usize,
    cursor: SourceCursor<'a>,
    current: Option<char>,
    token: Token<'a>
}

impl<'a> Tokenizer<'a> {
    fn tokenize_relative_source(mut cursor: SourceCursor<'a>, offset: u32) -> (Vec<Token<'a>>, Vec<LexError>) {
        let mut tokenizer = Tokenizer {
            offset,
            bol: 0,
            current: cursor._step(),
            cursor,
            token: Token {
                kind: TokenKind::Punctuator(Punctuator::Dot),
                span: Span::zero()
            }
        };
        tokenizer.lex_to_tokens()
    }
    
    fn lex_to_tokens(&mut self) -> (Vec<Token<'a>>, Vec<LexError>) {
        let mut tokens = Vec::new();
        let mut errors = Vec::new();
        loop {
            let start = self.position();
            match self.lex() {
                Ok(Some(token)) => tokens.push(token),
                Ok(None) => break,
                Err(kind) => {
                    errors.push(LexError {
                        kind,
                        span: self.make_span(start, self.position())
                    });
                    // TODO: also push an error token here, and add resilliance in the parser in
                    // those cases
                    self.bump();
                }
            }
        }
        if !tokens.is_empty() {
            tokens.push(Token {
                kind: TokenKind::EOS,
                span: self.make_span(self.position(), self.position())
            });
        }
        (tokens, errors)
    }

    fn initial(&mut self) -> Result<LexState, LexErrorKind> {
        if let None = self.current() {
            goto!(EOS);
        }

        let mut current = must!(self.current());
        while let ' ' | '\x09'..='\x0d' = current {
            let next = if self.eat_newline() { self.current() } else { self.bump() };
            let Some(next) = next else {
                break;
            };
            current = next;
        }
        
        if let None = self.current() {
            goto!(EOS);
        }

        if current == '/' {
            goto!(CommentOrPunct);
        }
        if let '"' | '\'' = current {
            goto!(CharOrStringLiteral);
        }
        if current.is_alphabetic() || current == '_' || current == '#' {
            goto!(SymbolDirectiveOrKeyword);
        }
        if let '0'..='9' = current {
            goto!(NumberLiteral);
        }

        goto!(PunctOrError);
    }

    fn comment_or_punct(&mut self) -> Result<LexState, LexErrorKind> {
        if let Some('/' | '*') = self.lookahead() {
            goto!(Comment);
        }
        goto!(PunctOrError);
    }

    fn char_or_string_literal(&mut self) -> Result<LexState, LexErrorKind> {
        let start = self.position();
        let kind = match self.current().unwrap() {
            '"' => StringKind::String,
            '\'' => StringKind::Char,
            _ => unreachable!()
        };

        let mut parser = StringParser::new(kind);

        let mut length = 1;
        let mut error = None;
        loop {
            let next = must!(self.bump());
            length += next.len_utf8();
            match parser.feed(next) {
                Ok(..) if parser.ended() => break,
                Ok(..) => continue,
                Err(err) if parser.ended() => {
                    error = Some(err);
                    break;
                },
                Err(err) => {
                    error = Some(err);
                    continue;
                },
            }
        }
        if !self.eat_newline() {
            self.bump().unwrap();
        }
        if let Some(error) = error {
            return Err(LexErrorKind::StringError(error));
        }

        let kind = match kind {
            StringKind::Char => LiteralKind::Char,
            StringKind::String => LiteralKind::String,
        };

        let literal = self.slice(self.position() - start, length).unwrap();
        self.token = Token {
            kind: TokenKind::Literal(literal, kind),
            span: self.make_span(start, self.position())
        };
        goto!(End);
    }

    fn symbol_directive_or_keyword(&mut self) -> Result<LexState, LexErrorKind> {
        let directive = self.current().unwrap() == '#';
        if directive {
            must!(self.bump());
        }
        let start = self.position();
        let mut length = 1;
        loop {
            let current = self.bump();
            let Some(current) = current else {
                break;
            };
            if !current.is_alphanumeric() && current != '_' {
                break;
            }
            length += current.len_utf8();
        }
        let symbol = self.slice_bytes(self.position() - start, length).unwrap();
        if directive {
            let directive = Directive::try_from_string(symbol).ok_or_else(|| {
                let symbol = Symbol::intern(std::str::from_utf8(symbol).unwrap());
                LexErrorKind::UnknownDirective(symbol)
            })?;
            self.token = Token {
                kind: TokenKind::Directive(directive),
                span: self.make_span(start - 1, (start - 1) + (length + 1))
            };
        } else if let Some(keyword) = Keyword::try_from_string(symbol) {
            self.token = Token {
                kind: TokenKind::Keyword(keyword),
                span: self.make_span(start, start + length)
            };
        } else if let Some(punct) = Punctuator::try_from_string(symbol) {
            self.token = Token {
                kind: TokenKind::Punctuator(punct),
                span: self.make_span(start, start + length)
            };
        } else {
            let symbol = Symbol::intern(std::str::from_utf8(symbol).unwrap());
            self.token = Token {
                kind: TokenKind::Symbol(symbol),
                span: self.make_span(start, start + length)
            };
        }
        goto!(End);
    }

    fn lex_digits(&mut self, start: usize, mut length: usize, mode: NumberMode) -> &'a str {
        loop {
            let current = self.bump();
            match current {
                Some('_' | ('0'..='1')) => length += 1,
                Some('2'..='7') if mode >= NumberMode::Octal => length += 1,
                Some('8'..='9') if mode >= NumberMode::Decimal => length += 1,
                Some(('a'..='f') | ('A'..='F')) if mode == NumberMode::Hex => length += 1,
                _ => break
            }
        }
        self.slice(self.position() - start, length).unwrap()
    }

    fn number_literal(&mut self) -> Result<LexState, LexErrorKind> {
        let start = self.position();
        if let Some('0') = self.current() {
            let next_char = self.lookahead();
            if let Some('o' | 'O' | 'x' | 'X' | 'b' | 'B') = next_char {
                goto!(IntegerLiteral);
            }
        }

        let mut literal = self.lex_digits(start, 1, NumberMode::Decimal);
        let mut kind = LiteralKind::IntNumber(NumberMode::Decimal);

        if let Some('.' | 'e' | 'E') = self.current() {
            must!(self.bump());
            kind = LiteralKind::FloatingPoint;
            literal = self.lex_digits(start, literal.len() + 1, NumberMode::Decimal);
        }

        self.token = Token {
            kind: TokenKind::Literal(literal, kind),
            span: self.make_span(start, start + literal.len())
        };

        goto!(End);
    }

    fn punct_or_error(&mut self) -> Result<LexState, LexErrorKind> {
        let start = self.position();
        let mut length = Punctuator::MAX_LENGTH;
        let mut punctuator = self
            .slice_bytes(0, length)
            .and_then(Punctuator::try_from_string);
        while let None = punctuator {
            if length == 0 {
                break;
            }
            length -= 1;
            punctuator = self
                .slice_bytes(0, length)
                .and_then(Punctuator::try_from_string);
        }

        let Some(punctuator) = punctuator else {
            return Err(LexErrorKind::InvalidCharacter(self.current().unwrap()));
        };

        for _ in 0..length {
            self.bump().unwrap();
        }

        self.token = Token {
            kind: TokenKind::Punctuator(punctuator),
            span: self.make_span(start, start + length),
        };

        goto!(End);
    }

    fn comment(&mut self) -> Result<LexState, LexErrorKind> {
        let multiline_comment = self.matches(1, b"/*");
        self.bump();
        let mut level = multiline_comment as u32;
        let mut current = self.bump();
        let mut ate_newline = false;
        loop {
            if multiline_comment {
                if current.is_none() {
                    return Err(LexErrorKind::UnexpectedEOS);
                }
                if self.matches(1, b"/*") {
                    level += 1;
                } else if self.matches(1, b"*/") {
                    level -= 1;
                }

                if level == 0 {
                    self.bump().unwrap();
                    self.bump().unwrap();
                    break;
                }
            } else if ate_newline || current.is_none() {
                break;
            }

            if self.eat_newline() {
                ate_newline = true;
                current = self.current();
            } else {
                ate_newline = false;
                current = self.bump();
            }
        }

        // don't emit comment as a token; lex a new one
        goto!(Initial);
    }

    /// This is a helper function for specifically lexing non-decimal
    /// integer literals. It does not consider floating points to be
    /// valid and error on seeing a `Dot` token behind the number
    fn integer_literal(&mut self) -> Result<LexState, LexErrorKind> {
        let span_start = self.position();
        let current = self.bump().unwrap(); // In this case always '0'
        let mode = match current {
            'b' | 'B' => NumberMode::Binary,
            'o' | 'O' => NumberMode::Octal,
            'x' | 'X' => NumberMode::Hex,
            _ => unreachable!()
        };

        let start = self.position();
        let literal = self.lex_digits(start, 0, mode);
        if literal.len() == 0 {
            return Err(LexErrorKind::IncompleteIntegerLiteral);
        }
        if let Some('.') = self.current() {
            return Err(LexErrorKind::NonDecimalFloatingPointLiteral);
        }

        self.token = Token {
            kind: TokenKind::Literal(literal, LiteralKind::IntNumber(mode)),
            span: self.make_span(span_start, self.position() - 1)
        };

        goto!(End);
    }

    fn lex(&mut self) -> Result<Option<Token<'a>>, LexErrorKind> {
        let mut state = LexState::Initial;
        let states = [
            Self::initial,
            Self::comment_or_punct,
            Self::char_or_string_literal,
            Self::symbol_directive_or_keyword,
            Self::number_literal,
            Self::punct_or_error,
            Self::comment,
            Self::integer_literal,
        ];

        while state < LexState::End {
            state = states[state as usize](self)?;
        }
        if state == LexState::EOS {
            return Ok(None);
        }
        Ok(Some(self.token))
    }

    fn eat_newline(&mut self) -> bool {
        let Some('\r' | '\n') = self.current() else {
            return false;
        };
        let next = self.bump();
        self.bol = self.position();
        if let Some('\n') = next { // hanlde windows: \r\n
            self.bump();
            self.bol += 1;
        }
        true
    }

    fn lookahead(&mut self) -> Option<char> {
        self.cursor._lookahead()
    }

    fn bump(&mut self) -> Option<char> {
        self.current = self.cursor._step();
        self.current
    }

    fn current(&self) -> Option<char> {
        self.current
    }

    fn make_span(&self, mut start: usize, mut end: usize) -> Span {
        // self.position() is always one step in the future
        start = start.saturating_sub(1);
        end = end.saturating_sub(1);
        Span::new(
            start as u32 + self.offset,
            end as u32 + self.offset)
    }
}

impl<'a> Deref for Tokenizer<'a> {
    type Target = SourceCursor<'a>;

    fn deref(&self) -> &Self::Target {
        &self.cursor
    }
}

impl<'a> DerefMut for Tokenizer<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cursor
    }
}


pub fn tokenize<'a>(source_file: &'a File, diagnostics: &DiagnosticsCtxt) -> Result<TokenStream<'a>, ()> {
    let contents = match source_file.contents() {
        Ok(contents) => contents,
        Err(Utf8Error) => {
            eprintln!("ERROR: couldn't read {}: stream contains invalid UTF-8", source_file.str_path());
            return Err(());
        }
    };
    let cursor = SourceCursor::new(contents);
    let (tokens, errors) = Tokenizer::tokenize_relative_source(cursor, source_file.relative_start());
    let mut stream = TokenStream::build(tokens, diagnostics)?;

    for err in errors {
        stream.tainted_with_errors = true;
        match err.kind {
            LexErrorKind::InvalidCharacter(chr) => {
                Message::error(format!("invalid character in stream: {chr:?}"))
                    .at(err.span)
                    .push(diagnostics);
            }
            LexErrorKind::IncompleteIntegerLiteral => {
                Message::error(format!("integer literal seems incomplete"))
                    .at(err.span)
                    .push(diagnostics);
            }
            LexErrorKind::NonDecimalFloatingPointLiteral => {
                Message::error(format!("non-decimal float literal is not allowed"))
                    .at(err.span)
                    .push(diagnostics);
            }
            LexErrorKind::UnknownDirective(symbol) => {
                Message::error(format!("unknown directive `#{}`", symbol.get()))
                    .at(err.span)
                    .push(diagnostics);
            }
            LexErrorKind::StringError(error) => {
                let message = match error {
                    StringError::UnclosedLiteral => "unterminated string literal",
                    StringError::EmptyCharLiteral => "char literal cannot be empty",
                    StringError::MultiCharLiteral => "multi-character char literal is invalid",
                    StringError::UnknownCharEscape => "unknown escape character in literal",
                    StringError::InvalidCharInHexByte => "invalid hexadecimal in literal escape",
                    StringError::InvalidCharInUnicodeLiteral => "invalid hexadecimal in unicode literal escape",
                    StringError::NonUnicodeCharInLiteral => "non unicode character in escape literal"
                };
                Message::error(message)
                    .at(err.span)
                    .push(diagnostics);
            }
            LexErrorKind::UnexpectedEOS => {
                Message::error("file ended unexpectedly")
                    .at(err.span)
                    .push(diagnostics);
            }
        }
    }

    Ok(stream)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, LexFromString)]
pub enum Punctuator {
    #[str = "_"]
    Underscore,
    #[str = "."]
    Dot,
    #[str = ","]
    Comma,
    #[str = ":"]
    Colon,
    #[str = "::"]
    DoubleColon,
    #[str = ";"]
    Semicolon,
    #[str = "["]
    LBracket,
    #[str = "]"]
    RBracket,
    #[str = "{"]
    LCurly,
    #[str = "}"]
    RCurly,
    #[str = "("]
    LParen,
    #[str = ")"]
    RParen,
    #[str = "="]
    Assign,
    #[str = ".."]
    DotDot,
    #[str = "->"]
    Arrow,
    #[str = "^"]
    Circumflex,
    #[str = "?"]
    Question,

    #[str = "&"]
    Ampersand,
    #[str = "|"]
    VBar,
    #[str = "~"]
    Tilde,

    #[str = "<<"]
    LDoubleChevron,
    #[str = ">>"]
    RDoubleChevron,

    #[str = "+"]
    Plus,
    #[str = "-"]
    Minus,
    #[str = "*"]
    Star,
    #[str = "/"]
    Slash,
    #[str = "%"]
    Percent,

    #[str = "<"]
    LChevron,
    #[str = "<="]
    LChevronEq,
    #[str = ">"]
    RChevron,
    #[str = ">="]
    RChevronEq,
    #[str = "=="]
    DoubleEq,
    #[str = "!="]
    BangEq,

    #[str = "&&"]
    DoubleAmpersand,
    #[str = "||"]
    DoubleVBar,
    #[str = "!"]
    Bang,

    #[str = ":="]
    ColonAssign,

    #[str = "+="]
    PlusAssign,
    #[str = "-="]
    MinusAssing,
    #[str = "*="]
    StarAssign,
    #[str = "/="]
    SlashAssign,
    #[str = "%="]
    PercentAssign,

    #[str = "||="]
    DoubleVBarAssign,
    #[str = "&&="]
    DoubleAnpersandAssign,
    #[str = "^="]
    CircumflexAssign,

    #[str = "<<="]
    LDoubleChevronAssign,
    #[str = ">>="]
    RDoubleChevronAssign,

    #[str = "&="]
    AnpersandAssign,
    #[str = "|="]
    VBarAssign,



    #[str = "++"]
    DoublePlus,
    #[str = "--"]
    DoubleMinus,
}

impl Punctuator {
    const MAX_LENGTH: usize = 3;
}

impl Tokenish for Punctuator {
    fn matches(&self, tok: Token) -> bool {
        if let TokenKind::Punctuator(punct) = tok.kind {
            return *self == punct;
        }
        false
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, LexFromString)]
pub enum Keyword {
    #[str = "const"]
    Const,
    #[str = "use"]
    Use,
    #[str = "with"]
    With,
    #[str = "var"]
    Var,
    #[str = "static"]
    Static,
    #[str = "cast"]
    Cast,
    #[str = "transmute"]
    Transmute,
    #[str = "out"]
    Out,
    #[str = "is"]
    Is,
    #[str = "extern"]
    Extern,
    #[str = "while"]
    While,
    #[str = "for"]
    For,
    #[str = "in"]
    In,
    #[str = "if"]
    If,
    #[str = "else"]
    Else,
    #[str = "struct"]
    Struct,
    #[str = "enum"]
    Enum,
    #[str = "return"]
    Return,
    #[str = "break"]
    Break,
    #[str = "continue"]
    Continue,
    #[str = "yeet"]
    Yeet,
    #[str = "template"]
    Template,
    #[str = "interface"]
    Interface,
    #[str = "closure"]
    Closure,
    #[str = "true"]
    True,
    #[str = "false"]
    False,
    #[str = "null"]
    Null
}

impl Tokenish for Keyword {
    fn matches(&self, tok: Token) -> bool { 
        if let TokenKind::Keyword(keyword) = tok.kind {
            return *self == keyword;
        }
        false
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, LexFromString)]
pub enum Directive {
    #[str = "scope"]
    Scope,
    #[str = "c_call"]
    CCall,
    #[str = "link"]
    Link,
    #[str = "compiler_intrinsic"]
    CompilerIntrinsic,
    #[str = "include"]
    Include,
}

impl Tokenish for Directive {
    fn matches(&self, tok: Token) -> bool { 
        if let TokenKind::Directive(keyword) = tok.kind {
            return *self == keyword;
        }
        false
    }
}

trait LexFromString: Sized {
    fn try_from_string(str: &[u8]) -> Option<Self>;
}

#[repr(u32)]
#[derive(Clone, Copy, Debug)]
pub enum Associotivity {
    Right = 0,
    Left = 1
}

#[derive(Debug, Clone, Copy, Operator)]
pub enum BinaryOp {
    #[precedence = 11]
    #[token = "*"]
    Mul,
    #[precedence = 11]
    #[token = "/"]
    Div,
    #[precedence = 11]
    #[token = "%"]
    Mod,

    #[precedence = 10]
    #[token = "+"]
    Plus,
    #[precedence = 10]
    #[token = "-"]
    Minus,

    #[precedence = 9]
    #[token = "<<"]
    LeftShift,
    #[precedence = 9]
    #[token = ">>"]
    RightShift,

    #[precedence = 8]
    #[token = "&"]
    BitwiseAnd,
    #[precedence = 7]
    #[token = "^"]
    BitwiseXor,
    #[precedence = 6]
    #[token = "|"]
    BitwiseOr,

    #[precedence = 5]
    #[token = "=="]
    Equals,
    #[precedence = 5]
    #[token = "!="]
    NotEquals,
    #[precedence = 5]
    #[token = ">"]
    GreaterThan,
    #[precedence = 5]
    #[token = ">="]
    GreaterEqual,
    #[precedence = 5]
    #[token = "<"]
    LessThan,
    #[precedence = 5]
    #[token = "<="]
    LessEqual,

    #[precedence = 4]
    #[token = "&&"]
    BooleanAnd,
    #[precedence = 3]
    #[token = "||"]
    BooleanOr,
}

#[derive(Clone, Copy, Operator, Debug)]
pub enum AssignmentOp {
    #[token = "="]
    Assign,
    // #[token = ":="]
    // WalrusAssign,

    #[token = "+="]
    PlusAssign,
    #[token = "-="]
    MinusAssign,
    #[token = "*="]
    MulAssign,
    #[token = "/="]
    DivAssign,
    #[token = "%="]
    ModAssign,

    #[token = "<<="]
    LeftShiftAssign,
    #[token = ">>="]
    RightShiftAssign,

    #[token = "&="]
    BitwiseAndAssign,
    #[token = "|="]
    BitwiseOrAssign,
    #[token = "^="]
    BitwiseXorAssign,
}

impl AssignmentOp {
    const ASSIGMENT_PRECEDENCE: u32 = 2;
}

#[derive(Clone, Copy)]
pub enum AssociotiveOp {
    BinaryOp(BinaryOp),
    AssignOp(AssignmentOp),
}

impl AssociotiveOp {
    pub fn precedence(&self) -> u32 {
        match self {
            AssociotiveOp::BinaryOp(binary) =>
                binary.precedence(),
            AssociotiveOp::AssignOp(..) =>
                AssignmentOp::ASSIGMENT_PRECEDENCE
        }
    }

    pub fn associotivity(&self) -> Associotivity {
        match self {
            AssociotiveOp::BinaryOp(..) =>
                Associotivity::Left,
            AssociotiveOp::AssignOp(..) =>
                Associotivity::Right
        }
    }
}

#[derive(Debug, Clone, Copy, Operator, PartialEq, Eq)]
pub enum UnaryOp {
    #[token = "~"]
    BitwiseNot,
    #[token = "!"]
    Not,
    #[token = "-"]
    Minus,
    #[token = "&"]
    Ref,
}


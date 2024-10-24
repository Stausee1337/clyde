use std::{ops::{DerefMut, Deref}, marker::PhantomData};

use crate::{symbol::Symbol, parser::{TokenCursor, ParseToken}, interface::File, string_internals};
use clyde_macros::{LexFromString, Operator};

macro_rules! Token {
    [.] => { crate::lexer::punctuators::Dot };
    [,] => { crate::lexer::punctuators::Comma };
    [:] => { crate::lexer::punctuators::Colon };
    [::] => { crate::lexer::punctuators::DoubleColon };
    [;] => { crate::lexer::punctuators::Semicolon };
    [=] => { crate::lexer::punctuators::Assign };
    [..] => { crate::lexer::punctuators::DotDot };
    [->] => { crate::lexer::punctuators::Arrow };
    [^] => { crate::lexer::punctuators::Circumflex };
    [?] => { crate::lexer::punctuators::Question };

    [&] => { crate::lexer::punctuators::Ampersand };
    [|] => { crate::lexer::punctuators::VBar };
    [~] => { crate::lexer::punctuators::Tilde };

    [<<] => { crate::lexer::punctuators::LDoubleChevron };
    [>>] => { crate::lexer::punctuators::RDoubleChevron };

    [+] => { crate::lexer::punctuators::Plus };
    [-] => { crate::lexer::punctuators::Minus };
    [*] => { crate::lexer::punctuators::Star };
    [/] => { crate::lexer::punctuators::Slash };
    [%] => { crate::lexer::punctuators::Percent };

    [<] => { crate::lexer::punctuators::LChevron };
    [<=] => { crate::lexer::punctuators::LChevronEq };
    [>] => { crate::lexer::punctuators::RChevron };
    [>=] => { crate::lexer::punctuators::RChevronEq };
    [==] => { crate::lexer::punctuators::DoubleEq };
    [!=] => { crate::lexer::punctuators::BangEq };

    [&&] => { crate::lexer::punctuators::DoubleAmpersand };
    [||] => { crate::lexer::punctuators::DoubleVBar };
    [!] => { crate::lexer::punctuators::Bang };

    [:=] => { crate::lexer::punctuators::ColonAssign };

    [+=] => { crate::lexer::punctuators::PlusAssign };
    [-=] => { crate::lexer::punctuators::MinusAssing };
    [*=] => { crate::lexer::punctuators::StarAssign };
    [/=] => { crate::lexer::punctuators::SlashAssign };
    [%=] => { crate::lexer::punctuators::PercentAssign };

    [||=] => { crate::lexer::punctuators::DoubleVBarAssign };
    [&&=] => { crate::lexer::punctuators::DoubleAnpersandAssign };
    [^=] => { crate::lexer::punctuators::CircumflexAssign };

    [<<=] => { crate::lexer::punctuators::LDoubleChevronAssign };
    [>>=] => { crate::lexer::punctuators::RDoubleChevronAssign };

    [&=] => { crate::lexer::punctuators::AnpersandAssign };
    [|=] => { crate::lexer::punctuators::VBarAssign };
}

macro_rules! must {
    ($e:expr) => {
        match $e {
            Some(chr) => chr,
            None => return Err(LexError::UnexpectedEOS),
        }
    };
}

macro_rules! goto {
    ($state:ident) => {
        return Ok(LexState::$state);
    };
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum LexState {
    Initial = 0,
    CommentOrPunct = 1,
    CharOrStringLiteral = 2,
    SymbolOrKeyword = 3,
    NumberLiteral = 4,
    PunctOrError = 5,
    Comment = 6,
    IntegerLiteral = 7,

    End,
}

#[derive(Debug, Clone, Copy)]
pub enum LexError {
    UnexpectedEOS,
    InvalidCharacter,
    IncompleteIntegerLiteral,
    NonDecimalFloatingPointLiteral,
}

#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: u32,
    pub end: u32
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn contains(&self, pos: u32) -> bool {
        return self.start <= pos && pos < self.end;
    }

    pub const fn zero() -> Span {
        Span::new(0, 0)
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
    Punctuator(Punctuator),
    Literal(&'a str, LiteralKind),
    Symbol(Symbol),
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

pub struct TokenStream<'a> {
    tokens: Vec<Token<'a>>
}

#[derive(Clone)]
struct SourceCursor<'a> {
    current: *const u8,
    length: usize,
    position: usize,
    _phantom: PhantomData<&'a ()>
}

impl<'a> SourceCursor<'a> {
    fn new(source: &'a [u8]) -> Self {
        Self {
            current: source.as_ptr(),
            length: source.len(),
            position: 0,
            _phantom: PhantomData::default()
        }
    }

    fn bump(&mut self) -> Option<char> {
        unsafe {
            let char = string_internals::next_code_point(self);
            char.map(|char| char::from_u32_unchecked(char))
        }
    }

    fn length(&self) -> usize {
        self.length
    }

    fn position(&self) -> usize {
        self.position
    }

    fn slice(&self, relative_start: usize, length: usize) -> Option<&'a str> {
        if self.position - relative_start + length > self.length {
            return None;
        }
        unsafe { 
            let ptr = self.current.sub(relative_start);
            let slice = std::slice::from_raw_parts(ptr, length);
            Some(std::str::from_utf8_unchecked(slice))
        }
    }

    fn matches(&self, pattern: &[u8]) -> bool {
        let rem = self.length - self.position;
        if rem > pattern.len() {
            return false;
        }
        for i in 0..rem {
            let b = unsafe { *self.current.add(i) };
            if b != pattern[i] {
                return false;
            }
        }
        return true;
    }
}

impl<'a> Iterator for SourceCursor<'a> {
    type Item = &'a u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.length {
            return None;
        }

        unsafe {
            let prev = self.current;
            self.current = self.current.add(1);
            self.position += 1;
            Some(&*prev)
        }
    }
}


struct Tokenizer<'a> {
    offset: u32,
    bol: usize,
    cursor: SourceCursor<'a>,
    current: Option<char>,
    lookahead_map: Option<char>,
    token: Token<'a>
}

impl<'a> Tokenizer<'a> {
    fn tokenize_relative_source(mut cursor: SourceCursor<'a>, offset: u32) -> TokenStream<'a> {
        let mut tokenizer = Tokenizer {
            offset,
            bol: 0,
            current: cursor.bump(),
            cursor,
            lookahead_map: None,
            token: Token {
                kind: TokenKind::Punctuator(Punctuator::Dot),
                span: Span::zero()
            }
        };
        tokenizer.lex_to_stream()
    }
    
    fn make_span(&self, start: usize, end: usize) -> Span {
        Span::new(
            start as u32 + self.offset,
            end as u32 + self.offset)
    }

    fn lex_to_stream(&mut self) -> TokenStream<'a> {
        loop {
            let token = self.lex().unwrap();
            println!("{token:?}");
            if self.current.is_none() {
                break;
            }
        }
        todo!()
    }

    fn initial(&mut self) -> Result<LexState, LexError> {
        let mut current = must!(self.current());
        while let ' ' | '\x09'..='\x0d' = current {
            self.eat_newline();
            let Some(next) = self.bump() else {
                break;
            };
            current = next;
        }

        if current == '/' {
            goto!(CommentOrPunct);
        }
        if let '"' | '\'' = current {
            goto!(CharOrStringLiteral);
        }
        if current.is_alphabetic() || current == '_' {
            goto!(SymbolOrKeyword);
        }
        if let '0'..='9' = current {
            goto!(NumberLiteral);
        }

        goto!(PunctOrError);
    }

    fn comment_or_punct(&mut self) -> Result<LexState, LexError> {
        if let Some('/' | '*') = self.lookahead() {
            goto!(Comment);
        }
        goto!(PunctOrError);
    }

    fn char_or_string_literal(&mut self) -> Result<LexState, LexError> {
        goto!(End);
    }

    fn symbol_or_keyword(&mut self) -> Result<LexState, LexError> {
        let start = self.position();
        let mut length = 1;
        loop {
            let current = self.cursor.bump();
            let Some(current) = current else {
                break;
            };
            if !current.is_alphanumeric() && current != '_' {
                break;
            }
            length += current.len_utf8();
        }
        let symbol = self.slice(self.position() - start, length).unwrap();
        if let Some(keyword) = Keyword::try_from_string(symbol) {
            self.token = Token {
                kind: TokenKind::Keyword(keyword),
                span: self.make_span(start, start + length)
            };
        } else {
            let symbol = Symbol::intern(symbol);
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

    fn number_literal(&mut self) -> Result<LexState, LexError> {
        if let Some('0') = self.current() {
            let next_char = self.lookahead();
            if let Some('o' | 'O' | 'x' | 'X' | 'b' | 'B') = next_char {
                goto!(IntegerLiteral);
            }
        }

        let start = self.position();
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

    fn punct_or_error(&mut self) -> Result<LexState, LexError> {
        let start = self.position();
        let mut length = Punctuator::MAX_LENGTH;
        let mut punctuator = self
            .slice(0, length)
            .and_then(Punctuator::try_from_string);
        while let None = punctuator {
            if self.length == 0 {
                break;
            }
            length -= 1;
            punctuator = self
                .slice(0, length)
                .and_then(Punctuator::try_from_string);
        }

        let Some(punctuator) = punctuator else {
            return Err(LexError::InvalidCharacter);
        };

        self.token = Token {
            kind: TokenKind::Punctuator(punctuator),
            span: self.make_span(start, start + length),
        };

        goto!(End);
    }

    fn comment(&mut self) -> Result<LexState, LexError> {
        let multiline_comment = self.matches(b"/*");
        self.bump();
        let mut level = multiline_comment as u32;
        let mut current = self.bump();
        let mut ate_newline = false;
        loop {
            if multiline_comment {
                if current.is_none() {
                    return Err(LexError::UnexpectedEOS);
                }
                if self.matches(b"/*") {
                    level += 1;
                } else if self.matches(b"*/") {
                    level -= 1;
                }

                if level == 0 {
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
    fn integer_literal(&mut self) -> Result<LexState, LexError> {
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
            return Err(LexError::IncompleteIntegerLiteral);
        }
        if let Some('.') = self.current() {
            return Err(LexError::NonDecimalFloatingPointLiteral);
        }

        self.token = Token {
            kind: TokenKind::Literal(literal, LiteralKind::IntNumber(mode)),
            span: self.make_span(span_start, self.position() - 1)
        };

        goto!(End);
    }

    fn lex(&mut self) -> Result<Token<'a>, LexError> {
        let mut state = LexState::Initial;
        let states = [
            Self::initial,
            Self::comment_or_punct,
            Self::char_or_string_literal,
            Self::symbol_or_keyword,
            Self::number_literal,
            Self::punct_or_error,
            Self::comment,
            Self::integer_literal,
        ];

        while state != LexState::End {
            state = states[state as usize](self)?;
        }
        Ok(self.token)
    }

    fn eat_newline(&mut self) -> bool {
        let Some('\r' | '\n') = self.current() else {
            return false;
        };
        let next = self.bump();
        self.bol = self.position;
        if let Some('\n') = next { // hanlde windows: \r\n
            self.bump();
            self.bol += 1;
        }
        true
    }

    fn lookahead(&mut self) -> Option<char> {
        if let None = self.lookahead_map {
            self.lookahead_map = self.cursor.bump();
        }
        self.lookahead_map
    }

    fn bump(&mut self) -> Option<char> {
        self.current = self.lookahead_map
            .take()
            .or_else(|| self.cursor.bump());
        self.current
    }

    fn current(&self) -> Option<char> {
        self.current
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

pub fn tokenize<'a>(source_file: &'a File) -> TokenStream<'a> {
    let cursor = SourceCursor::new(source_file.contents());
    Tokenizer::tokenize_relative_source(cursor, source_file.relative_start())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, LexFromString)]
pub enum Punctuator {
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
}

impl Punctuator {
    const MAX_LENGTH: usize = 3;
}

impl ParseToken for Punctuator {
    fn peek(cursor: TokenCursor) -> bool {
        cursor.punct().is_some()
    }
}

#[derive(Debug, Clone, Copy, LexFromString)]
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

impl ParseToken for Keyword {
    fn peek(cursor: TokenCursor) -> bool {
        cursor.keyword().is_some()
    }
}

trait LexFromString: Sized {
    fn try_from_string(str: &str) -> Option<Self>;
}

#[derive(Clone, Copy, Operator)]
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
    BinaryAnd,
    #[precedence = 7]
    #[token = "^"]
    BinaryXor,
    #[precedence = 6]
    #[token = "|"]
    BinaryOr,

    #[precedence = 5]
    #[token = "=="]
    Eqals,
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

#[derive(Clone, Copy, Operator)]
pub enum AssignmentOp {
    #[token = "="]
    Assign,
    #[token = ":="]
    WalrusAssign,

    #[token = "+="]
    PlusAssign,
    #[token = "-="]
    MinusAssing,
    #[token = "*="]
    MulAssign,
    #[token = "/="]
    DivAssign,
    #[token = "%="]
    ModAssign,

    #[token = "||="]
    BinaryOrAssign,
    #[token = "&&="]
    BinaryAndAssign,
    #[token = "^="]
    BinaryXorAssign,

    #[token = "<<="]
    ShlAssign,
    #[token = ">>="]
    ShrAssign,

    #[token = "&="]
    AndAssign,
    #[token = "|="]
    OrAssign,
}

#[derive(Clone, Copy, Operator)]
pub enum UnaryOp {
    #[token = "~"]
    BitwiseNot,
    #[token = "!"]
    Not,
    #[token = "+"]
    Plus,
    #[token = "-"]
    Minus,
    #[token = "*"]
    Deref,
}



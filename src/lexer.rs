use crate::{symbol::Symbol, parser::Cursor};
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

#[derive(Clone, Copy)]
pub struct Span {
    start: u32,
    end: u32
}

pub struct Token<'a> {
    pub kind: TokenKind<'a>,
    pub span: Span
}

pub enum TokenKind<'a> {
    Keyword(Keyword),
    Punctuator(Punctuator),
    Literal(&'a str),
    Symbol(Symbol),
}

trait LexFromString: Sized {
    fn try_from_string(str: &str) -> Option<Self>;
}

pub trait ParseToken {
    fn peek(cursor: Cursor) -> bool;
}

#[derive(Clone, Copy, PartialEq, Eq, LexFromString)]
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

pub struct TokenStream<'a> {
    tokens: &'a [Token<'a>]
}

impl ParseToken for Punctuator {
    fn peek(cursor: Cursor) -> bool {
        cursor.punct().is_some()
    }
}

#[derive(Clone, Copy, LexFromString)]
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
    fn peek(cursor: Cursor) -> bool {
        cursor.keyword().is_some()
    }
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



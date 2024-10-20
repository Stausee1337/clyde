use crate::symbol::Symbol;
use clyde_macros::LexFromString;

macro_rules! Token {
    [*] => { crate::lexer::Star };
}

pub enum TokenKind {
    Keyword(Keyword),
    Punctuation(Punctuation),
    Literal(String),
    Symbol(Symbol),
}

pub struct Token {
    kind: TokenKind,
    span: Span
}

pub struct Span {
    start: u32,
    end: u32
}

#[derive(Clone, Copy, LexFromString)]
pub enum Punctuation {
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

mod operators {
    use clyde_macros::Operator;

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
}


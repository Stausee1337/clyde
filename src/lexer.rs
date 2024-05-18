use std::ops::Range;
use logos::Logos;
use logos_display::Display;

#[derive(Logos, Debug, Display, PartialEq, Clone)]
#[logos(skip r"[ \t\n\f]+")] // Ignore this regex pattern between tokens
pub enum TokenKind {
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token("::")]
    DoubleColon,
    #[token(";")]
    Semicolon,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("{")]
    LCurly,
    #[token("}")]
    RCurly,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(":=")]
    Walrus,
    #[token("..")]
    DotDot,
    #[token("...")]
    DotDotDot,
    #[token("!")]
    Bang,
    #[token("->")]
    Arrow,
    #[token("$")]
    Dollar,
    #[token("@")]
    At,

    #[token("&")]
    Ampersand,
    #[token("|")]
    VBar,
    #[token("^")]
    Circumflex,
    #[token("~")]
    Tilde,

    #[token("<<")]
    LDoubleChevron,
    #[token(">>")]
    RDoubleChevron,

    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,

    #[token("<")]
    LChevron,
    #[token("<=")]
    LChevronEq,
    #[token(">")]
    RChevron,
    #[token(">=")]
    RChevronEq,
    #[token("=")]
    Eq,
    #[token("<>")]
    DoubleChevron,

    #[token("and")]
    And,
    #[token("or")]
    Or,
    #[token("not")]
    Not,

    #[regex(r"[^\d\W]\w*", |lex| lex.slice().to_string())]
    Name(String),
    #[regex(r"(?:0(?:_?0)*|[1-9](?:_?[0-9])*)", |lex| lex.slice().parse().ok())]
    Intnumber(u64),
    #[regex(r"#[^\n]*")]
    Comment,
    #[regex("\"[^\\n\"\\\\]*(?:\\\\.[^\\n\"\\\\]*)*\"", |lex| lex.slice().to_string())]
    String(String),

    #[token("const")]
    Const,
    #[token("use")]
    Use,
    #[token("with")]
    With,
    #[token("var")]
    Var,
    #[token("static")]
    Static,
    #[token("as")]
    As,
    #[token("out")]
    Out,
    #[token("is")]
    Is,
    #[token("extern")]
    Extern,
    #[token("proc")]
    Proc,
    #[token("while")]
    While,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("do")]
    Do,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("elif")]
    ElIf,
    #[token("else")]
    Else,
    #[token("end")]
    End,
    #[token("record")]
    Record,
    #[token("ref")]
    Ref,
    #[token("return")]
    Return,
    #[token("break")]
    Break,
    #[token("continue")]
    Continue,
    #[token("template")]
    Template,
    #[token("interface")]
    Interface,
    #[token("closure")]
    Closure,

    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("None")]
    None
}

impl TokenKind {
    pub fn is_keyword(&self) -> bool {
        match self {
            TokenKind::Const | TokenKind::Use | TokenKind::With | TokenKind::Var | TokenKind::Static | TokenKind::As | TokenKind::Out | TokenKind::Is | TokenKind::Extern | TokenKind::Proc | TokenKind::While | TokenKind::For | TokenKind::In | TokenKind::Do | TokenKind::If | TokenKind::Then | TokenKind::ElIf | TokenKind::Else | TokenKind::End | TokenKind::Record | TokenKind::Ref | TokenKind::Return | TokenKind::Break | TokenKind::Continue | TokenKind::Closure | 
    TokenKind::True | TokenKind::False | TokenKind::None => true,
            _ => false
        }
    }
}

#[derive(Debug, Clone)]
pub struct Token(pub TokenKind, pub Range<usize>);

#[derive(Debug, Clone)]
pub struct LexError(pub Range<usize>, pub String);

pub fn lex_input_string(source: &str) -> Result<Vec<Token>, LexError> {
    let mut lexer = TokenKind::lexer(source);
    let mut result = Vec::new();
    loop {
        let Some(token) = lexer.next() else {
            break;
        };
        let span = lexer.span();
        let mut token = token
            .map_err(|_|
                LexError(span.clone(), format!("Invalid character `{}` in input stream", &source[span.clone()])))?;
        match &mut token {
            TokenKind::Comment => {
                continue;
            }
            TokenKind::String(s) => {
                *s = snailquote::unescape(s).map_err(|err| LexError(span.clone(), err.to_string()))?;
            }
            _ => ()
        }
        result.push(Token(token, span));
    }
    Ok(result)
}



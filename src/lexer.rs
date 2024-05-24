use std::ops::Range;
use logos::Logos;
use logos_display::Display;

#[derive(Logos, Debug, Display, PartialEq, Clone)]
#[logos(error = LexError)]
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
    #[token("=")]
    Assign,
    #[token("..")]
    DotDot,
    #[token("->")]
    Arrow,
    #[token("^")]
    Circumflex,
    #[token("?")]
    Question,

    #[token("&")]
    Ampersand,
    #[token("|")]
    VBar,
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
    #[token("==")]
    DoubleEq,
    #[token("!=")]
    BangEq,

    #[token("&&")]
    DoubleAmpersand,
    #[token("||")]
    DoubleVBar,
    #[token("!")]
    Bang,

    #[regex(r"[^\d\W]\w*", |lex| lex.slice().to_string())]
    Name(String),
    #[regex(r"(?:0(?:_?0)*|[1-9](?:_?[0-9])*)", |lex| lex.slice().parse().ok())]
    Intnumber(u64),
    #[regex(r"//[^\n]*")]
    Comment,
    #[regex("\"[^\\n\"\\\\]*(?:\\\\.[^\\n\"\\\\]*)*\"", |lex| lex.slice().to_string())]
    String(String),
    #[regex("\'[^\\n\'\\\\](?:\\\\.[^\\n\'\\\\]*)*\'", to_character)]
    Char(char),

    #[token("const")]
    Const,
    #[token("use")]
    Use,
    #[token("unit")]
    Unit,
    #[token("with")]
    With,
    #[token("var")]
    Var,
    #[token("static")]
    Static,
    #[token("cast")]
    Cast,
    #[token("pun")]
    Pun,
    #[token("out")]
    Out,
    #[token("is")]
    Is,
    #[token("extern")]
    Extern,
    #[token("fn")]
    Fn,
    #[token("while")]
    While,
    #[token("for")]
    For,
    #[token("in")]
    In,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    #[token("struct")]
    Struct,
    #[token("enum")]
    Enum,
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
    #[token("null")]
    Null
}


#[derive(Debug, Clone)]
pub struct Token(pub TokenKind, pub Range<usize>);

#[derive(Debug, Default, Clone, PartialEq)]
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

fn to_character<'a>(lex: &'a mut logos::Lexer<TokenKind>) -> Result<char, <TokenKind as Logos<'a>>::Error> {
    let span = lex.span(); 
    let res = snailquote::unescape(lex.slice()).map_err(|err| LexError(span.clone(), err.to_string()))?;

    if res.chars().count() > 1 {
        return Err(LexError(span.clone(), "Found multi-char character literal".to_string()));
    }

    Ok(res.chars().nth(0).unwrap())
}


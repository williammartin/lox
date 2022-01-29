#[derive(thiserror::Error, Debug)]
pub struct UsageError {
    pub msg: String,
}

impl std::fmt::Display for UsageError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "usage: ilox [script]\n\n{}", self.msg)
    }
}

mod config {
    #[derive(Debug)]
    pub struct Config {
        pub file_path: Option<String>,
    }

    impl Config {
        pub fn new(args: &[String]) -> anyhow::Result<Config> {
            if args.len() > 2 {
                Err(anyhow::anyhow!("expected to have zero or one arguments"))
            } else {
                Ok(Config {
                    file_path: args.get(1).map(|s| str::to_string(s)),
                })
            }
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let config = config::Config::new(&args).map_err(|msg| UsageError {
        msg: msg.to_string(),
    })?;

    interpreter::run(config)?;

    Ok(())
}

pub mod interpreter {

    #[derive(thiserror::Error, Debug)]
    pub enum InterpretingError {
        #[error(transparent)]
        Io(#[from] std::io::Error),
        #[error(transparent)]
        Lexing(#[from] lexer::LexingErrors),
    }

    enum InterpeterSource {
        File(String),
        Prompt,
    }

    impl From<&crate::config::Config> for InterpeterSource {
        fn from(config: &crate::config::Config) -> Self {
            config
                .file_path
                .clone()
                .map_or(InterpeterSource::Prompt, |path| {
                    InterpeterSource::File(path)
                })
        }
    }

    pub fn run(config: crate::config::Config) -> Result<(), InterpretingError> {
        match InterpeterSource::from(&config) {
            InterpeterSource::File(path) => run_file(&path),
            InterpeterSource::Prompt => run_prompt(),
        }
    }

    fn run_file(path: &str) -> Result<(), InterpretingError> {
        let source = std::fs::read_to_string(path)?;
        let tokens = lexer::lex(source)?;

        dbg!(tokens);
        Ok(())
    }

    fn run_prompt() -> Result<(), InterpretingError> {
        use std::io::BufRead;
        for line in std::io::stdin().lock().lines() {
            let tokens = lexer::lex(line?)?;
            dbg!(tokens);
        }
        Ok(())
    }

    pub mod lexer {
        use itertools::Itertools;

        #[derive(thiserror::Error, Debug, PartialEq, Eq)]
        pub struct LexingErrors(Vec<LexingError>);

        impl std::fmt::Display for LexingErrors {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "Lexing Errors:")?;
                for v in &self.0 {
                    writeln!(f, "\t{}", v)?;
                }
                Ok(())
            }
        }

        #[derive(thiserror::Error, Debug, PartialEq, Eq)]
        pub struct LexingError {
            pub line_number: u8,
            // location is a bad name
            pub location: String,
            pub msg: String,
        }

        impl std::fmt::Display for LexingError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(
                    f,
                    "[line {}] Error {}: {}",
                    self.line_number, self.location, self.msg
                )
            }
        }

        #[derive(Debug, PartialEq)]
        pub struct Token {
            kind: TokenKind,
            line_number: u8,
        }

        #[derive(Debug, PartialEq, Clone)]
        pub enum TokenKind {
            // Single chars
            EndOfFile,
            LeftParen,
            RightParen,
            LeftBrace,
            RightBrace,
            Comma,
            Dot,
            Minus,
            Plus,
            Semicolon,
            Star,
            Bang,
            Equal,
            Less,
            Greater,
            Slash,

            // Multi Chars
            BangEqual,
            EqualEqual,
            LessEqual,
            GreaterEqual,

            // Literals
            String(String),
            Number(f64),

            // Identifiers and Reserved
            Identifier(String),
            And,
            Class,
            Else,
            False,
            For,
            Fun,
            If,
            Nil,
            Or,
            Print,
            Return,
            Super,
            This,
            True,
            Var,
            While,
        }

        lazy_static::lazy_static! {
            pub static ref KEYWORDS: std::collections::HashMap<& 'static str, TokenKind> = {
                let mut m = std::collections::HashMap::new();
                m.insert("and", TokenKind::And);
                m.insert("class", TokenKind::Class);
                m.insert("else", TokenKind::Else);
                m.insert("false", TokenKind::False);
                m.insert("for", TokenKind::For);
                m.insert("fun", TokenKind::Fun);
                m.insert("if", TokenKind::If);
                m.insert("nil", TokenKind::Nil);
                m.insert("or", TokenKind::Or);
                m.insert("print", TokenKind::Print);
                m.insert("return", TokenKind::Return);
                m.insert("super", TokenKind::Super);
                m.insert("this", TokenKind::This);
                m.insert("true", TokenKind::True);
                m.insert("var", TokenKind::Var);
                m.insert("while", TokenKind::While);
                m
            };
        }

        pub fn lex(source: String) -> Result<Vec<Token>, LexingErrors> {
            let mut source_chars = source.chars().peekable();
            let mut tokens = Vec::<Token>::new();
            let mut lexing_errors = Vec::<LexingError>::new();

            // let mut start = 0;
            let mut current_line_number = 1;

            while let Some(char) = source_chars.next() {
                let mut chars_to_consume = 0;

                let parsed_token_kind = match char {
                    // Unambiguous
                    '(' => Ok(Some(TokenKind::LeftParen)),
                    ')' => Ok(Some(TokenKind::RightParen)),
                    '{' => Ok(Some(TokenKind::LeftBrace)),
                    '}' => Ok(Some(TokenKind::RightBrace)),
                    ',' => Ok(Some(TokenKind::Comma)),
                    '.' => Ok(Some(TokenKind::Dot)),
                    '-' => Ok(Some(TokenKind::Minus)),
                    '+' => Ok(Some(TokenKind::Plus)),
                    ';' => Ok(Some(TokenKind::Semicolon)),
                    '*' => Ok(Some(TokenKind::Star)),

                    // Single or Double
                    '!' => match source_chars.peek() {
                        Some(char) if *char == '=' => {
                            chars_to_consume += 1;
                            Ok(Some(TokenKind::BangEqual))
                        }
                        _ => Ok(Some(TokenKind::Bang)),
                    },

                    '=' => match source_chars.peek() {
                        Some(char) if *char == '=' => {
                            chars_to_consume += 1;
                            Ok(Some(TokenKind::EqualEqual))
                        }
                        _ => Ok(Some(TokenKind::Equal)),
                    },

                    '<' => match source_chars.peek() {
                        Some(char) if *char == '=' => {
                            chars_to_consume += 1;
                            Ok(Some(TokenKind::LessEqual))
                        }
                        _ => Ok(Some(TokenKind::Less)),
                    },

                    '>' => match source_chars.peek() {
                        Some(char) if *char == '=' => {
                            chars_to_consume += 1;
                            Ok(Some(TokenKind::GreaterEqual))
                        }
                        _ => Ok(Some(TokenKind::Greater)),
                    },

                    // Single or Line
                    '/' => match source_chars.peek() {
                        Some(char) if *char == '/' => {
                            source_chars
                                .peeking_take_while(|char| *char != '\n')
                                .for_each(|_c| {
                                    chars_to_consume += 1;
                                });
                            // One more to consume the trailing \n
                            source_chars.next();
                            Ok(None)
                        }
                        _ => Ok(Some(TokenKind::Slash)),
                    },

                    // Whitespace
                    ' ' | '\r' | '\t' => Ok(None),

                    '\n' => {
                        current_line_number += 1;
                        Ok(None)
                    }

                    // Literals
                    '"' => {
                        let str_lit: String = source_chars
                            .peeking_take_while(|char| *char != '"')
                            .collect();

                        if source_chars.peek().is_none() {
                            Err(LexingError {
                                line_number: current_line_number,
                                location: str_lit,
                                msg: "unterminated string".to_string(),
                            })
                        } else {
                            // One more to consume the trailing "
                            source_chars.next();
                            Ok(Some(TokenKind::String(str_lit)))
                        }
                    }

                    '0'..='9' => {
                        // Note that we might panic here but it would be very surprising. It would mean that we got a char that was between
                        // 0 and 9 inclusive, but that didn't parse...
                        // WARNING: This doesn't prevent 123....4 but I can't really be bothered.
                        // WARNING: THIS IS FUCKING GROSS
                        let numeric_literal: f64 = format!(
                            "{}{}",
                            char,
                            source_chars
                                .peeking_take_while(
                                    |char| *char > '0' && *char < '9' || *char == '.'
                                )
                                .collect::<String>()
                        )
                        .parse::<f64>()
                        .unwrap();

                        Ok(Some(TokenKind::Number(numeric_literal)))
                    }

                    // Identifiers
                    'a'..='z' | 'A'..='Z' | '_' => {
                        let identifier_or_keyword: String = format!(
                            "{}{}",
                            char,
                            source_chars
                                .peeking_take_while(|char| (*char >= 'a' && *char <= 'z')
                                    || (*char >= 'A' && *char <= 'Z')
                                    || *char == '_')
                                .collect::<String>()
                        );

                        Ok(Some(KEYWORDS.get(identifier_or_keyword.as_str()).map_or(
                            TokenKind::Identifier(identifier_or_keyword),
                            |token_type| token_type.clone(),
                        )))
                    }

                    _ => {
                        // In this case we have to be smarter than character matching...

                        Err(LexingError {
                            line_number: current_line_number,
                            location: char.to_string(),
                            msg: "unexpected character".to_string(),
                        })
                    }
                };

                match parsed_token_kind {
                    Ok(optional_token_kind) => {
                        if let Some(kind) = optional_token_kind {
                            tokens.push(Token {
                                kind,
                                line_number: current_line_number,
                            })
                        }
                    }
                    Err(err) => lexing_errors.push(err),
                }

                // OMG disgusting.
                if chars_to_consume > 0 {
                    source_chars.nth(chars_to_consume - 1);
                }
            }

            if !lexing_errors.is_empty() {
                Err(LexingErrors(lexing_errors))
            } else {
                Ok(tokens)
            }
        }

        #[cfg(test)]
        mod test {
            use super::*;

            fn s(s: &str) -> String {
                s.to_string()
            }

            #[test]
            fn test_left_paren() {
                let lex_result = lex(s("("));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::LeftParen,
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_bang() {
                let lex_result = lex(s("!"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Bang,
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_bang_equal() {
                let lex_result = lex(s("!="));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::BangEqual,
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_slash() {
                let lex_result = lex(s("/"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Slash,
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_comment() {
                let lex_result = lex(s("// comment till end of line\n"));

                assert_eq!(lex_result, Ok(vec![]));
            }

            #[test]
            fn test_comment_no_new_line() {
                let lex_result = lex(s("// comment till end of line"));

                assert_eq!(lex_result, Ok(vec![]));
            }

            #[test]
            fn test_on_second_line() {
                let lex_result = lex(s("\n!"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Bang,
                        line_number: 2,
                    }])
                );
            }

            #[test]
            fn test_string_lit() {
                let lex_result = lex(s("\"my string\""));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::String(s("my string")),
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_unclosed_string_lit() {
                let lex_result = lex(s("\"my string"));

                assert_eq!(
                    lex_result,
                    Err(LexingErrors(vec![LexingError {
                        line_number: 1,
                        location: s("my string"),
                        msg: s("unterminated string"),
                    }]))
                );
            }

            #[test]
            fn test_numeric_lit() {
                let lex_result = lex(s("1234"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Number(1234.0),
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_numeric_lit_decimal() {
                let lex_result = lex(s("12.34"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Number(12.34),
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_identifier() {
                let lex_result = lex(s("foobar"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::Identifier(s("foobar")),
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_keyword() {
                let lex_result = lex(s("and"));

                assert_eq!(
                    lex_result,
                    Ok(vec![Token {
                        kind: TokenKind::And,
                        line_number: 1,
                    }])
                );
            }

            #[test]
            fn test_single_lex_error() {
                let lex_result = lex(s("#"));

                assert_eq!(
                    lex_result,
                    Err(LexingErrors(vec![LexingError {
                        line_number: 1,
                        location: s("#"),
                        msg: s("unexpected character"),
                    }]))
                );
            }

            #[test]
            fn test_multi_lex_error() {
                let lex_result = lex(s("#@"));

                assert_eq!(
                    lex_result,
                    Err(LexingErrors(vec![
                        LexingError {
                            line_number: 1,
                            location: s("#"),
                            msg: s("unexpected character"),
                        },
                        LexingError {
                            line_number: 1,
                            location: s("@"),
                            msg: s("unexpected character"),
                        }
                    ]))
                );
            }
        }
    }
}

//! Quick and easy lexing for C-like languages.
//!
//! This crate provides a highly general lexer for a C-like language, as well as
//! simple span support. This library is based off of a specific kind of parser
//! I have re-written many times over in my career.

mod driver;
mod file;
mod lexer;
mod token;

pub mod report;
pub use byteyarn;

pub use crate::driver::main;
pub use crate::file::File;
pub use crate::file::FileCtx;
pub use crate::file::FileMut;
pub use crate::file::Span;
pub use crate::file::Spanned;
pub use crate::lexer::spec;
pub use crate::report::error;
pub use crate::report::warn;
pub use crate::token::Content;
pub use crate::token::Cursor;
pub use crate::token::Ident;
pub use crate::token::Number;
pub use crate::token::Quoted;
pub use crate::token::Token;
pub use crate::token::TokenStream;
pub use crate::token::Tokenish;

//! Utils used with different lalrpop parsers

use std::{
    fmt::{self, Debug, Formatter},
    hash::Hash,
    sync::Arc,
};

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Clone, Default, Serialize, Deserialize, JsonSchema)]
/// A reference to a location in a source file.
///
/// Important note: in order to facilitate comparison of AST nodes, all instances of SourceRef are considered equal.
/// Any tests that expect instances whose fields differ not to be equal must use custom comparison logic.
pub struct SourceRef {
    pub file_name: Option<Arc<str>>,
    pub file_contents: Option<Arc<str>>,
    pub start: usize,
    pub end: usize,
}

impl Ord for SourceRef {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for SourceRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for SourceRef {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == std::cmp::Ordering::Equal
    }
}

impl Eq for SourceRef {}

impl Hash for SourceRef {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}

impl SourceRef {
    pub fn unknown() -> Self {
        Default::default()
    }

    /// Returns a new Error for this source reference.
    pub fn with_error(&self, message: String) -> Error {
        Error {
            source_ref: self.clone(),
            message,
        }
    }
}

impl Debug for SourceRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}-{}",
            self.file_name.as_deref().unwrap_or(""),
            self.start,
            self.end
        )
    }
}

#[derive(Debug)]
pub struct Error {
    source_ref: SourceRef,
    message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {:?}", self.message, self.source_ref)
    }
}

impl Error {
    pub fn output_to_stderr(&self) {
        use codespan_reporting::diagnostic::{Diagnostic, Label};
        use codespan_reporting::files::SimpleFiles;
        use codespan_reporting::term;
        use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

        let config = term::Config::default();
        let mut files = SimpleFiles::new();
        let file_name = self.source_ref.file_name.as_deref().unwrap_or("input");
        let contents = self.source_ref.file_contents.as_deref().unwrap_or_default();
        let file_id = files.add(file_name, contents);
        let diagnostic = Diagnostic::error()
            .with_message(&self.message)
            .with_labels(vec![Label::primary(
                file_id,
                self.source_ref.start..self.source_ref.end,
            )]);
        let mut writer = StandardStream::stderr(ColorChoice::Always);
        term::emit(&mut writer, &config, &files, &diagnostic).unwrap()
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn source_ref(&self) -> &SourceRef {
        &self.source_ref
    }

    pub fn extend_message<F>(&self, f: F) -> Error
    where
        F: FnOnce(&str) -> String,
    {
        self.source_ref().with_error(f(self.message()))
    }
}

pub fn handle_parse_error(
    err: lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token, Error>,
    file_name: Option<&str>,
    input: &str,
) -> Error {
    let (start, end) = match err {
        lalrpop_util::ParseError::InvalidToken { location } => (location, location),
        lalrpop_util::ParseError::UnrecognizedEOF {
            location,
            expected: _,
        } => (location, location),
        lalrpop_util::ParseError::UnrecognizedToken {
            token: (start, _, end),
            expected: _,
        } => (start, end),
        lalrpop_util::ParseError::ExtraToken {
            token: (start, _, end),
        } => (start, end),
        lalrpop_util::ParseError::User { error } => {
            return error;
        }
    };
    Error {
        source_ref: SourceRef {
            start,
            end,
            file_name: file_name.map(Into::into),
            file_contents: Some(input.into()),
        },
        message: err.to_string(),
    }
}

/// Convenience trait that outputs parser errors to stderr and panics.
/// Should be used mostly in tests.
pub trait UnwrapErrToStderr {
    type Inner;
    fn unwrap_err_to_stderr(self) -> Self::Inner;
}

impl<T> UnwrapErrToStderr for Result<T, Error> {
    type Inner = T;

    fn unwrap_err_to_stderr(self) -> Self::Inner {
        match self {
            Ok(r) => r,
            Err(err) => {
                err.output_to_stderr();
                panic!("Parse error.");
            }
        }
    }
}

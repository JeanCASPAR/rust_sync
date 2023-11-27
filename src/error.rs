use proc_macro2::{Ident, Span};
use proc_macro_error::abort;

use crate::parser::Type;

pub struct Error {
    kind: Box<ErrorKind>,
    span: Span,
}

impl Error {
    pub fn undef_var(ident: &Ident) -> Self {
        Self {
            kind: Box::new(ErrorKind::UndefinedVariable {
                variable: ident.to_string(),
            }),
            span: ident.span(),
        }
    }

    pub fn non_bool_cond(span: Span) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::NonBoolCond),
        }
    }

    pub fn external_symbol_not_toplevel(span: Span, symbol: String) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::ExternalSymbolNotToplevel { symbol }),
        }
    }

    pub fn type_mismatch(span: Span, left_type: Type, right_type: Type) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::TypeMismatch {
                left_type,
                right_type,
            }),
        }
    }

    pub fn twice_var(name: String, def_span: Span, found_span: Span) -> Self {
        Self {
            span: found_span.clone(),
            kind: Box::new(ErrorKind::TwiceVar { name, def_span }),
        }
    }

    pub fn negative_first_index(span: Span) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::NegativeFirstIndex),
        }
    }

    pub fn then_type_mismatch(span: Span, left_type: Type, right_type: Type) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::ThenTypeMismatch {
                left_type,
                right_type,
            }),
        }
    }

    pub fn bool_arithmetic(span: Span) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::BoolArithmetic),
        }
    }

    pub fn number_logic(span: Span) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::NumberLogic),
        }
    }

    pub fn float_cast(span: Span, ty: Type) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::FloatCast { ty }),
        }
    }

    pub fn raise(self) -> ! {
        match *self.kind {
            ErrorKind::TwiceVar { name, def_span } => {
                abort!(
                    self.span, "variable `{}` is defined twice", name;
                    hint = def_span => "the variable was previously defined here"
                );
            }
            ErrorKind::UndefinedVariable { variable } => {
                abort!(self.span, "Variable `{}` is undefined.", variable);
            }
            ErrorKind::NegativeFirstIndex => {
                abort!(
                    self.span,
                    "this expression will cause an access to an undefined value"
                );
            }
            ErrorKind::ThenTypeMismatch {
                left_type,
                right_type,
            } => {
                abort!(
                    self.span,
                    "type mismatch: `{}` and `{}`",
                    left_type,
                    right_type
                )
            }
            ErrorKind::BoolArithmetic => {
                abort!(
                    self.span,
                    "type mismatch: expected `{number}`, found `bool`"
                )
            }
            ErrorKind::NumberLogic => {
                abort!(
                    self.span,
                    "type mismatch: expected `bool`, found `{number}`"
                )
            }
            ErrorKind::FloatCast { ty } => {
                abort!(
                    self.span,
                    "type mismatch: `{}` is not castable to float",
                    ty
                )
            }
            ErrorKind::TypeMismatch {
                left_type,
                right_type,
            } => {
                abort!(
                    self.span,
                    "type mismatch: left has type `{}`, right has type `{}`",
                    left_type,
                    right_type,
                )
            }
            ErrorKind::NonBoolCond => abort!(
                self.span,
                "type error: a condition should have type `{bool}`"
            ),
            ErrorKind::ExternalSymbolNotToplevel { symbol } => abort!(
                self.span,
                "Rust function call expressions should be assigned to a variable right away"
            ),
        }
    }
}

pub enum ErrorKind {
    UndefinedVariable { variable: String },
    TwiceVar { name: String, def_span: Span },
    NegativeFirstIndex,
    BoolArithmetic,
    NumberLogic,
    FloatCast { ty: Type },
    ThenTypeMismatch { left_type: Type, right_type: Type },
    TypeMismatch { left_type: Type, right_type: Type },
    NonBoolCond,
    ExternalSymbolNotToplevel { symbol: String },
}

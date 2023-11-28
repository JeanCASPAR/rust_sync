use itertools::Itertools;
use proc_macro2::{Ident, Span};
use proc_macro_error::abort;
use smallvec::smallvec as types;

use crate::parser::{ClockType, Type, Types, TypesFmt};

#[derive(Debug)]
pub struct Error {
    kind: Box<ErrorKind>,
    span: Span,
}

impl Error {
    #[inline]
    pub fn new(kind: ErrorKind, span: Span) -> Self {
        Self {
            kind: Box::new(kind),
            span,
        }
    }

    pub fn undef_var(ident: &Ident) -> Self {
        Self::new(
            ErrorKind::UndefinedVariable {
                variable: ident.to_string(),
            },
            ident.span(),
        )
    }

    pub fn non_bool_cond(span: Span) -> Self {
        Self::new(ErrorKind::NonBoolCond, span)
    }

    pub fn external_symbol_not_toplevel(span: Span, symbol: String) -> Self {
        Self::new(ErrorKind::ExternalSymbolNotToplevel { symbol }, span)
    }

    pub fn types_mismatch(span: Span, left_types: Types, right_types: Types) -> Self {
        Self::new(
            ErrorKind::TypesMismatch {
                left_types,
                right_types,
            },
            span,
        )
    }

    pub fn type_mismatch(span: Span, left_type: Type, right_type: Type) -> Self {
        Self::types_mismatch(span, types![left_type], types![right_type])
    }

    pub fn twice_var(name: String, def_span: Span, found_span: Span) -> Self {
        Self::new(ErrorKind::TwiceVar { name, def_span }, found_span.clone())
    }

    pub fn negative_first_index(span: Span) -> Self {
        Self::new(ErrorKind::NegativeFirstIndex, span)
    }

    pub fn then_type_mismatch(span: Span, left_type: Types, right_type: Types) -> Self {
        Self::new(
            ErrorKind::ThenTypeMismatch {
                left_type,
                right_type,
            },
            span,
        )
    }

    pub fn bool_arithmetic(span: Span) -> Self {
        Self::new(ErrorKind::BoolArithmetic, span)
    }

    pub fn number_logic(span: Span) -> Self {
        Self::new(ErrorKind::NumberLogic, span)
    }

    pub fn float_cast(span: Span, ty: Type) -> Self {
        Self::new(ErrorKind::FloatCast { ty }, span)
    }

    pub fn no_tuples(span: Span, types: Types) -> Self {
        Self::new(ErrorKind::NoTuples { types }, span)
    }

    pub fn merge_branch_on_base_clock(
        span: Span,
        true_branch: bool,
        clock_base_type: Vec<ClockType>,
        clock: Ident,
    ) -> Self {
        Self::new(
            ErrorKind::MergeBranchOnBaseClock {
                true_branch,
                expected_base_type: clock_base_type,
                clock,
            },
            span,
        )
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
                    left_type.type_format(),
                    right_type.type_format()
                )
            }
            ErrorKind::BoolArithmetic => {
                abort!(self.span, "type mismatch: expected `int`, found `bool`")
            }
            ErrorKind::NumberLogic => {
                abort!(self.span, "type mismatch: expected `bool`, found `int`")
            }
            ErrorKind::FloatCast { ty } => {
                abort!(
                    self.span,
                    "type mismatch: `{}` is not castable to float",
                    ty
                )
            }
            ErrorKind::TypesMismatch {
                left_types,
                right_types,
            } => {
                abort!(
                    self.span,
                    "type mismatch: left has type `{}`, right has type `{}`",
                    left_types.type_format(),
                    right_types.type_format(),
                )
            }
            ErrorKind::NonBoolCond => abort!(
                self.span,
                "type error: a condition should have type `{bool}`"
            ),
            ErrorKind::ExternalSymbolNotToplevel { symbol } => abort!(
                self.span,
                "Rust function call expressions should be assigned to a variable right away";
                help = "`{}` is an external Rust symbol", symbol
            ),
            ErrorKind::NoTuples { types } => abort!(
                self.span,
                "tuples don't exist: {} is not a valid type...",
                types.type_format(),
            ),
            ErrorKind::MergeBranchOnBaseClock {
                true_branch,
                expected_base_type,
                clock,
            } => abort!(
                self.span,
                "clock error: the expression of the {} branch in a merge has the base clock",
                true_branch;
                // note = "Rustre has not clock subtyping.";
                help = "Try adding `{} when{} {}`.",
                expected_base_type.iter().map(ClockType::format_as_expr).format(" "),
                if true_branch { "" } else { "not" },
                clock
            ),
        }
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    UndefinedVariable {
        variable: String,
    },
    TwiceVar {
        name: String,
        def_span: Span,
    },
    NegativeFirstIndex,
    BoolArithmetic,
    NumberLogic,
    FloatCast {
        ty: Type,
    },
    ThenTypeMismatch {
        left_type: Types,
        right_type: Types,
    },
    TypesMismatch {
        left_types: Types,
        right_types: Types,
    },
    NonBoolCond,
    ExternalSymbolNotToplevel {
        symbol: String,
    },
    NoTuples {
        types: Types,
    },
    MergeBranchOnBaseClock {
        true_branch: bool,
        expected_base_type: Vec<ClockType>,
        clock: Ident,
    },
}

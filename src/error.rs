use std::iter::once;

use itertools::Itertools;
use proc_macro2::{Ident, Span};
use proc_macro_error::abort;
use smallvec::smallvec as types;

use crate::parser::{BaseType, ClockType, Type, Types, TypesFmt};

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

    pub fn argument_type_mismatch(span: Span, expected_type: Type, found_type: Type) -> Self {
        Self::new(
            ErrorKind::ArgumentTypeMismatch {
                expected_type,
                found_type,
            },
            span,
        )
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

    pub fn merge_branch_different_base(
        span: Span,
        true_branch: bool,
        branch_clock: Vec<ClockType>,
        clock: Ident,
        clock_clock: Vec<ClockType>,
    ) -> Self {
        Self::new(
            ErrorKind::MergeBranchDifferentBase {
                true_branch,
                clock_clock,
                clock,
                branch_clock,
            },
            span,
        )
    }

    pub fn cyclic_equation(span: Span, cycle: Vec<Span>) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::CyclicEquation { cycle }),
        }
    }

    pub fn cyclic_node(span: Span, cycle: Vec<Ident>) -> Self {
        Self {
            span,
            kind: Box::new(ErrorKind::CyclicNode { cycle }),
        }
    }

    pub fn merge_branch_wrong_positivity(span: Span, true_branch: bool, clock: String) -> Self {
        Self::new(
            ErrorKind::MergeBranchWrongPositivity { true_branch, clock },
            span,
        )
    }

    pub fn merge_branch_wrong_clock(
        span: Span,
        true_branch: bool,
        expected_clock: String,
        expected_clock_span: Span,
        branch_clock: String,
    ) -> Self {
        Self::new(
            ErrorKind::MergeBranchWrongClock {
                true_branch,
                expected_clock,
                expected_clock_span,
                branch_clock,
            },
            span,
        )
    }

    pub fn clock_not_boolean(
        span: Span,
        clock: String,
        found_type: BaseType,
        decl_span: Span,
    ) -> Self {
        Self::new(
            ErrorKind::ClockNotBoolean {
                clock,
                found_type,
                decl_span,
            },
            span,
        )
    }

    pub fn wrong_number_of_arguments(
        span: Span,
        node: String,
        expected: usize,
        found: usize,
    ) -> Self {
        Self::new(
            ErrorKind::WrongNumberOfArgument {
                expected,
                found,
                node,
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
            ErrorKind::MergeBranchDifferentBase {
                true_branch,
                clock_clock,
                clock,
                branch_clock,
            } => abort!(
                self.span,
                "clock error: the expression of the {} branch has an incompatible clock type",
                true_branch;
                note = "its clock type starts with `{}`",
                once(String::from("base"))
                    .chain(branch_clock.iter().map(ToString::to_string))
                    .format(" on ");
                note = clock.span() => "the clock type of {} is `{}`",
                clock.to_string(),
                once(String::from("base"))
                    .chain(clock_clock.iter().map(ToString::to_string))
                    .format(" on ");
            ),
            ErrorKind::CyclicEquation { cycle } => {
                abort!(
                    self.span,
                    "scheduling error: the following expressions form a cycle : {}",
                    cycle.iter().filter_map(Span::source_text).join(", ")
                )
            }
            ErrorKind::CyclicNode { cycle } => {
                abort!(
                    self.span,
                    "scheduling error: the following nodes form a cycle : {}",
                    cycle.iter().join(", ")
                )
            }
            ErrorKind::MergeBranchWrongPositivity { true_branch, clock } => abort!(
                self.span,
                "clock error: the {} should be on {} {}",
                true_branch,
                if true_branch { "positive" } else { "negative" },
                clock,
            ),
            ErrorKind::MergeBranchWrongClock {
                true_branch,
                expected_clock,
                expected_clock_span,
                branch_clock,
            } => abort!(
                self.span,
                "clock error: the {} branch isn't merged on the right clock",
                true_branch;
                note = "the last clock of the {} branch is {}",
                true_branch,
                branch_clock;
                help = expected_clock_span => "the clock to be merged on is {}",
                expected_clock
            ),
            ErrorKind::ClockNotBoolean {
                clock,
                found_type,
                decl_span,
            } => abort!(
                self.span,
                "type error: the clock `{}` should have type `bool`, found `{}`",
                clock,
                found_type;
                help = decl_span => "`{}` was declared here with type `{}`",
                clock,
                found_type
            ),
            ErrorKind::ArgumentTypeMismatch {
                expected_type,
                found_type,
            } => abort!(
                self.span,
                "type error: this argument should have type `{}`, but it has type `{}`",
                expected_type,
                found_type,
            ),
            ErrorKind::WrongNumberOfArgument {
                expected,
                found,
                node,
            } => abort!(
                self.span,
                "node `{}` takes {} argument{}, but {} {} provided",
                node,
                expected,
                if expected == 1 { "" } else { "s" },
                found,
                if found == 1 { "was" } else { "were" },
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
    MergeBranchDifferentBase {
        true_branch: bool,
        // The clock type of the clock, ie. if the clock is `c`, and has type `bool on c'`, then
        // `clock_clock` is `vec![c']`, and `clock` is `c`
        clock_clock: Vec<ClockType>,
        clock: Ident,
        branch_clock: Vec<ClockType>,
    },
    CyclicEquation {
        cycle: Vec<Span>,
    },
    CyclicNode {
        cycle: Vec<Ident>,
    },
    MergeBranchWrongPositivity {
        true_branch: bool,
        clock: String,
    },
    MergeBranchWrongClock {
        true_branch: bool,
        expected_clock: String,
        expected_clock_span: Span,
        branch_clock: String,
    },
    ClockNotBoolean {
        clock: String,
        found_type: BaseType,
        decl_span: Span,
    },
    ArgumentTypeMismatch {
        expected_type: Type,
        found_type: Type,
    },
    WrongNumberOfArgument {
        expected: usize,
        found: usize,
        node: String,
    },
}

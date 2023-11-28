use itertools::Itertools;
use proc_macro2::Span;
use smallvec::SmallVec;
use std::fmt::Display;

use patricia_tree::StringPatriciaMap;
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::{Pair, Punctuated},
    spanned::Spanned as SynSpanned,
    token::Paren,
    Attribute, Ident, LitBool, LitFloat, LitInt, Meta, Token, Visibility,
};

use crate::error::Error;

mod kw {
    use syn::custom_keyword;

    custom_keyword!(node);
    custom_keyword!(pre);
    custom_keyword!(merge);
    custom_keyword!(when);
    custom_keyword!(whennot);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseType {
    Unit,
    Int64,
    Float64,
    Bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClockType {
    pub positive: bool,
    pub clock: Ident,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub base: BaseType,
    /// `clock = vec![a, b, c]` means `base on a on b on c`, where `a`, `b` and `c` are
    /// `ClockType`s.
    pub clocks: Vec<ClockType>,
}

pub type Types = SmallVec<[Type; 1]>;

#[derive(Debug)]
pub struct TypesFormat<'a>(&'a Types);

impl<'a> Display for TypesFormat<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.iter().format(" * ").fmt(f)
    }
}

pub trait TypesFmt {
    fn type_format(&self) -> TypesFormat<'_>;
}

impl TypesFmt for Types {
    fn type_format(&self) -> TypesFormat<'_> {
        TypesFormat(self)
    }
}

impl From<BaseType> for Type {
    fn from(base: BaseType) -> Self {
        Self {
            base,
            clocks: Vec::new(),
        }
    }
}

impl Parse for Type {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(input.parse::<Spanned<Type>>()?.inner())
    }
}

#[derive(Debug)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    fn span(&self) -> Span {
        self.span
    }

    fn inner(self) -> T {
        self.inner
    }
}

impl Parse for Spanned<Type> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ty_name = input.parse::<Ident>()?;
        let base_type = match &ty_name.to_string() as &str {
            "int" => BaseType::Int64,
            "float" => BaseType::Float64,
            "bool" => BaseType::Bool,
            s => return Err(input.error(format!("Expected type int, float or bool, got {}", s))),
        };
        Ok(Spanned {
            inner: base_type.into(),
            span: ty_name.span(),
        })
    }
}

impl Display for BaseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BaseType::Unit => write!(f, "unit"),
            BaseType::Int64 => write!(f, "int"),
            BaseType::Float64 => write!(f, "float"),
            BaseType::Bool => write!(f, "bool"),
        }
    }
}

impl Display for ClockType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.positive {
            write!(f, "!")?;
        }
        write!(f, "{}", self.clock)
    }
}

impl ClockType {
    pub fn format_as_expr(&self) -> ClockTypeAsExpression<'_> {
        ClockTypeAsExpression(self)
    }
}

#[derive(Debug)]
pub struct ClockTypeAsExpression<'a>(&'a ClockType);

impl<'a> Display for ClockTypeAsExpression<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "when")?;
        if !self.0.positive {
            write!(f, "not")?;
        }
        write!(f, " {}", self.0.clock)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.base)?;
        for clock in self.clocks.iter() {
            write!(f, " on {clock}")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct NodeParam {
    pub id: Ident,
    pub ty: Type,
    pub span: Span,
}

impl Parse for NodeParam {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let span = input.span();
        let ty = input.parse::<Type>()?;
        let span = id.span().join(span).unwrap();
        Ok(NodeParam { id, ty, span })
    }
}

#[derive(Debug)]
pub struct NodeParams(pub Vec<NodeParam>);

impl Parse for NodeParams {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        parenthesized!(content in input);
        Ok(NodeParams(
            content
                .parse_terminated(NodeParam::parse, Token![,])?
                .into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated(t, _) | Pair::End(t) => t,
                })
                .collect(),
        ))
    }
}

#[derive(Debug)]
pub struct NodeReturn(pub Vec<Ident>);

impl Parse for NodeReturn {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        parenthesized!(content in input);
        let ret: Vec<_> = content
            .parse_terminated(Ident::parse, Token![,])?
            .into_pairs()
            .map(|pair| match pair {
                Pair::Punctuated(t, _) | Pair::End(t) => t,
            })
            .collect();
        Ok(NodeReturn(ret))
    }
}

#[derive(Debug)]
pub enum MathBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

pub enum BoolBinOp {
    And,
    Or,
}

pub enum CompOp {
    Ge,
    Gt,
    Le,
    Lt,
    Eq,
    NEq,
}

/// Expression grammar :
/// E0 -> E1 when var | E1 whennot var | E1
/// E1 -> E2 -> E1 | E2
/// E2 -> E2 + E3 | E1 - E3 | E3
/// E3 -> E3 * E4 | E2 / E4 | E2 % E4 | E4
/// E4 -> -E5 | pre E5 | E5
/// E5 -> E6 as float | E6
/// E6 -> E7 >= E7 | E7 > E7 | E7 <= E7 | E7 == E7 | E7 != E7 | E7
/// E7 -> !E8 | E8
/// E8 -> E8 && E9 | E8
/// E9 -> E9 || E10 | E10
/// E10 -> lit
///     | var
///     | fun ( E0, ..., E0 )
///     | if E0 { E0 } else { E0 }
///     | (E0)
/// <=========================>
///  E0 -> E1 when var
///      | E1 whennot var
///      | E1
///  E1 -> E2 => E1
///      | E2
///  E2 -> E3 E2'
///  E3 -> E4 E3'
///  E4 -> -E5
///      | pre E5
///      | E5
///  E5 -> E6 as float
///      | E6
///  E6 -> E7 >= E7
///      | E7 > E7
///      | E7 <= E7
///      | E7 < E7
///      | E7 == E7
///      | E7 != E7
///      | E7
///  E7 -> !E8
///      | E8
///  E8 -> E9 E8'
///  E9 -> E10 E9'
///  E10 -> lit
///      | var
///      | fun ( E0, ..., E0 )
///      | if E0 { E0 } else { E0 }
///      | (E0)
///      | ()
///      | merge var { true => E0, false => E0 }
/// E2' -> + E3 E2'
///      | - E3 E2'
///      | ε
/// E3' -> * E4 E3'
///      | / E4 E3'
///      | % E4 E3'
///      | ε
/// E8' -> && E9 E8'
///      | ε
/// E9' -> || E10 E9'
///      | ε
///  ===================
///
/// E -> E0
/// after each -, we must check that there is no >, because -> is not a real token
/// and it makes the grammar ambiguous

/// spans correspond to operators and constants
#[derive(Debug)]
pub enum Expr {
    Var(Ident),
    Pre(Span, Box<Spanned<Expr>>),
    Then(Box<Spanned<Expr>>, Span, Box<Spanned<Expr>>),
    Minus(Span, Box<Spanned<Expr>>),
    Not(Span, Box<Spanned<Expr>>),
    MathBinOp(Box<Spanned<Expr>>, MathBinOp, Span, Box<Spanned<Expr>>),
    BoolBinOp(Box<Spanned<Expr>>, BoolBinOp, Span, Box<Spanned<Expr>>),
    CompOp(Box<Spanned<Expr>>, CompOp, Span, Box<Spanned<Expr>>),
    If(Box<Spanned<Expr>>, Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    /// cast an int to a float
    FloatCast(Box<Spanned<Expr>>),
    FunCall(Ident, Vec<Spanned<Expr>>),
    Unit,
    Merge(Ident, Box<Spanned<Expr>>, Box<Spanned<Expr>>),
    When(Box<Spanned<Expr>>, Span, Ident),
    WhenNot(Box<Spanned<Expr>>, Span, Ident),
}

mod expr_internals {
    use syn::spanned::Spanned as SynSpanned;

    use super::*;

    #[derive(Debug)]
    pub(super) enum Expr0 {
        When(Box<Expr1>, Span, Ident),
        WhenNot(Box<Expr1>, Span, Ident),
        Down(Box<Expr1>),
    }

    impl Parse for Expr0 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e = input.parse::<Expr1>()?;
            if input.peek(kw::when) {
                let sp = input.parse::<kw::when>()?.span();
                let id = input.parse::<Ident>()?;
                Ok(Expr0::When(Box::new(e), sp, id))
            } else if input.peek(kw::whennot) {
                let sp = input.parse::<kw::whennot>()?.span();
                let id = input.parse::<Ident>()?;
                Ok(Expr0::WhenNot(Box::new(e), sp, id))
            } else {
                Ok(Expr0::Down(Box::new(e)))
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr0 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::When(e, sp, id) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = e.span().join(sp).unwrap().join(id.span()).unwrap();
                    Spanned {
                        inner: Expr::When(Box::new(e), sp, id),
                        span,
                    }
                }
                Self::WhenNot(e, sp, id) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = e.span().join(sp).unwrap().join(id.span()).unwrap();
                    Spanned {
                        inner: Expr::WhenNot(Box::new(e), sp, id),
                        span,
                    }
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr1 {
        Then(Box<Expr2>, Span, Box<Expr1>),
        Down(Box<Expr2>),
    }

    impl Parse for Expr1 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e1 = input.parse::<Expr2>()?;
            if input.peek(Token![->]) {
                let sp = input.span();
                let _ = input.parse::<Token![->]>()?;
                let e2 = input.parse::<Expr1>()?;
                Ok(Expr1::Then(Box::new(e1), sp, Box::new(e2)))
            } else {
                Ok(Expr1::Down(Box::new(e1)))
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr1 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::Then(e1, sp, e2) => {
                    let e1: Spanned<Expr> = (*e1).into();
                    let e2: Spanned<Expr> = (*e2).into();
                    let span = e1.span().join(e2.span()).unwrap();
                    Spanned {
                        inner: Expr::Then(Box::new(e1), sp, Box::new(e2)),
                        span,
                    }
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    #[derive(Debug)]
    pub(super) struct Expr2(Box<Expr3>, Box<Expr2bis>);

    impl Parse for Expr2 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e1 = input.parse::<Expr3>()?;
            let e2 = input.parse::<Expr2bis>()?;
            Ok(Expr2(Box::new(e1), Box::new(e2)))
        }
    }

    impl Into<Spanned<Expr>> for Expr2 {
        fn into(self) -> Spanned<Expr> {
            let e = (*self.0).into();
            self.1.into_with_ctx(e)
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr2bis {
        Add(Span, Box<Expr3>, Box<Expr2bis>),
        Sub(Span, Box<Expr3>, Box<Expr2bis>),
        Empty,
    }

    impl Parse for Expr2bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![+]) {
                let opspan = input.span();
                let _ = input.parse::<Token![+]>()?;
                let e1 = input.parse::<Expr3>()?;
                let e2 = input.parse::<Expr2bis>()?;
                Ok(Expr2bis::Add(opspan, Box::new(e1), Box::new(e2)))
            } else if input.peek(Token![-]) && !input.peek2(Token![>]) {
                let opspan = input.span();
                let _ = input.parse::<Token![-]>()?;
                let e1 = input.parse::<Expr3>()?;
                let e2 = input.parse::<Expr2bis>()?;
                Ok(Expr2bis::Sub(opspan, Box::new(e1), Box::new(e2)))
            } else {
                Ok(Expr2bis::Empty)
            }
        }
    }

    impl Expr2bis {
        fn into_with_ctx(self, e: Spanned<Expr>) -> Spanned<Expr> {
            match self {
                Self::Add(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: Spanned<Expr> = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(Spanned {
                        inner: Expr::MathBinOp(Box::new(e), MathBinOp::Add, sp, Box::new(e1)),
                        span: spe.join(sp1).unwrap(),
                    })
                }
                Self::Sub(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: Spanned<Expr> = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(Spanned {
                        inner: Expr::MathBinOp(Box::new(e), MathBinOp::Sub, sp, Box::new(e1)),
                        span: spe.join(sp1).unwrap(),
                    })
                }
                Self::Empty => e,
            }
        }
    }

    #[derive(Debug)]
    pub(super) struct Expr3(Box<Expr4>, Box<Expr3bis>);

    impl Parse for Expr3 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e1 = input.parse::<Expr4>()?;
            let e2 = input.parse::<Expr3bis>()?;
            Ok(Expr3(Box::new(e1), Box::new(e2)))
        }
    }

    impl Into<Spanned<Expr>> for Expr3 {
        fn into(self) -> Spanned<Expr> {
            let e = (*self.0).into();
            self.1.into_with_ctx(e)
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr3bis {
        Mul(Span, Box<Expr4>, Box<Expr3bis>),
        Div(Span, Box<Expr4>, Box<Expr3bis>),
        Rem(Span, Box<Expr4>, Box<Expr3bis>),
        Empty,
    }

    impl Parse for Expr3bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![*]) {
                let opspan = input.span();
                let _ = input.parse::<Token![*]>()?;
                let e1 = input.parse::<Expr4>()?;
                let e2 = input.parse::<Expr3bis>()?;
                Ok(Expr3bis::Mul(opspan, Box::new(e1), Box::new(e2)))
            } else if input.peek(Token![/]) {
                let opspan = input.span();
                let _ = input.parse::<Token![/]>()?;
                let e1 = input.parse::<Expr4>()?;
                let e2 = input.parse::<Expr3bis>()?;
                Ok(Expr3bis::Div(opspan, Box::new(e1), Box::new(e2)))
            } else if input.peek(Token![%]) {
                let opspan = input.span();
                let _ = input.parse::<Token![%]>()?;
                let e1 = input.parse::<Expr4>()?;
                let e2 = input.parse::<Expr3bis>()?;
                Ok(Expr3bis::Rem(opspan, Box::new(e1), Box::new(e2)))
            } else {
                Ok(Expr3bis::Empty)
            }
        }
    }

    impl Expr3bis {
        fn into_with_ctx(self, e: Spanned<Expr>) -> Spanned<Expr> {
            match self {
                Self::Mul(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: Spanned<Expr> = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(Spanned {
                        inner: Expr::MathBinOp(Box::new(e), MathBinOp::Mul, sp, Box::new(e1)),
                        span: spe.join(sp1).unwrap(),
                    })
                }
                Self::Div(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: Spanned<Expr> = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(Spanned {
                        inner: Expr::MathBinOp(Box::new(e), MathBinOp::Div, sp, Box::new(e1)),
                        span: spe.join(sp1).unwrap(),
                    })
                }
                Self::Rem(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: Spanned<Expr> = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(Spanned {
                        inner: Expr::MathBinOp(Box::new(e), MathBinOp::Rem, sp, Box::new(e1)),
                        span: spe.join(sp1).unwrap(),
                    })
                }
                Self::Empty => e,
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr4 {
        Minus(Span, Box<Expr5>),
        Pre(Span, Box<Expr5>),
        Down(Box<Expr5>),
    }

    impl Parse for Expr4 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![-]) && !input.peek2(Token![>]) {
                let opspan = input.span();
                let _ = input.parse::<Token![-]>()?;
                let e = input.parse::<Expr5>()?;
                Ok(Expr4::Minus(opspan, Box::new(e)))
            } else if input.peek(kw::pre) {
                let opspan = input.parse::<kw::pre>()?.span;
                let e = input.parse::<Expr5>()?;
                Ok(Expr4::Pre(opspan, Box::new(e)))
            } else {
                let e = input.parse::<Expr5>()?;
                Ok(Expr4::Down(Box::new(e)))
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr4 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::Minus(opspan, e) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    Spanned {
                        inner: Expr::Minus(opspan, Box::new(e)),
                        span,
                    }
                }
                Self::Pre(opspan, e) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    Spanned {
                        inner: Expr::Pre(opspan, Box::new(e)),
                        span,
                    }
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr5 {
        FloatCast(Box<Expr6>, Span),
        Down(Box<Expr6>),
    }

    impl Parse for Expr5 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e = input.parse::<Expr6>()?;
            if input.peek(Token![as]) {
                let _ = input.parse::<Token![as]>()?;
                let ty = input.parse::<Spanned<Type>>()?;
                let span = ty.span();
                match ty.inner().base {
                    BaseType::Float64 => Ok(Expr5::FloatCast(Box::new(e), span)),
                    _ => Err(input.error("You can only cast to float")),
                }
            } else {
                Ok(Expr5::Down(Box::new(e)))
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr5 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::FloatCast(e, sp) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = e.span().join(sp).unwrap();
                    Spanned {
                        inner: Expr::FloatCast(Box::new(e)),
                        span,
                    }
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr6 {
        Ge(Box<Expr7>, Span, Box<Expr7>),
        Gt(Box<Expr7>, Span, Box<Expr7>),
        Le(Box<Expr7>, Span, Box<Expr7>),
        Lt(Box<Expr7>, Span, Box<Expr7>),
        Eq(Box<Expr7>, Span, Box<Expr7>),
        NEq(Box<Expr7>, Span, Box<Expr7>),
        Down(Box<Expr7>),
    }

    impl Parse for Expr6 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e0 = input.parse::<Expr7>()?;
            let lookahead = input.lookahead1();
            let (op, opspan): (fn(_, _, _) -> _, _) = if lookahead.peek(Token![>=]) {
                let span = input.parse::<Token![>=]>()?.span();
                (Expr6::Ge, span)
            } else if lookahead.peek(Token![>]) {
                let span = input.parse::<Token![>]>()?.span();
                (Expr6::Gt, span)
            } else if lookahead.peek(Token![<=]) {
                let span = input.parse::<Token![<=]>()?.span();
                (Expr6::Le, span)
            } else if lookahead.peek(Token![<]) {
                let span = input.parse::<Token![<]>()?.span();
                (Expr6::Lt, span)
            } else if lookahead.peek(Token![==]) {
                let span = input.parse::<Token![==]>()?.span();
                (Expr6::Eq, span)
            } else if lookahead.peek(Token![!=]) {
                let span = input.parse::<Token![!=]>()?.span();
                (Expr6::NEq, span)
            } else {
                return Ok(Expr6::Down(Box::new(e0)));
            };
            let e1 = input.parse::<Expr7>()?;
            Ok(op(Box::new(e0), opspan, Box::new(e1)))
        }
    }

    impl Into<Spanned<Expr>> for Expr6 {
        fn into(self) -> Spanned<Expr> {
            let (e0, op, opspan, e1) = match self {
                Self::Ge(e0, opspan, e1) => (e0, CompOp::Ge, opspan, e1),
                Self::Gt(e0, opspan, e1) => (e0, CompOp::Gt, opspan, e1),
                Self::Le(e0, opspan, e1) => (e0, CompOp::Le, opspan, e1),
                Self::Lt(e0, opspan, e1) => (e0, CompOp::Lt, opspan, e1),
                Self::Eq(e0, opspan, e1) => (e0, CompOp::Eq, opspan, e1),
                Self::NEq(e0, opspan, e1) => (e0, CompOp::NEq, opspan, e1),
                Self::Down(e) => return (*e).into(),
            };
            let e0: Spanned<Expr> = (*e0).into();
            let e1: Spanned<Expr> = (*e1).into();
            let span = e0.span().join(e1.span()).unwrap();
            Spanned {
                inner: Expr::CompOp(Box::new(e0), op, opspan, Box::new(e1)),
                span,
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr7 {
        Not(Span, Box<Expr8>),
        Down(Box<Expr8>),
    }

    impl Parse for Expr7 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![!]) {
                let span = input.parse::<Token![!]>()?.span();
                Ok(Expr7::Not(span, Box::new(input.parse()?)))
            } else {
                Ok(Expr7::Down(Box::new(input.parse()?)))
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr7 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::Not(opspan, e) => {
                    let e: Spanned<Expr> = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    Spanned {
                        inner: Expr::Not(opspan, Box::new(e)),
                        span,
                    }
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    #[derive(Debug)]
    pub(super) struct Expr8(Box<Expr9>, Box<Expr8bis>);

    impl Parse for Expr8 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr8(Box::new(input.parse()?), Box::new(input.parse()?)))
        }
    }

    impl Into<Spanned<Expr>> for Expr8 {
        fn into(self) -> Spanned<Expr> {
            let e0: Spanned<Expr> = (*self.0).into();
            self.1.into_with_ctx(e0)
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr8bis {
        And(Span, Box<Expr9>, Box<Expr8bis>),
        Empty,
    }

    impl Parse for Expr8bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![&&]) {
                let opspan = input.parse::<Token![&&]>()?.span();
                let e0 = input.parse::<Expr9>()?;
                let e1 = input.parse::<Expr8bis>()?;
                Ok(Expr8bis::And(opspan, Box::new(e0), Box::new(e1)))
            } else {
                Ok(Expr8bis::Empty)
            }
        }
    }

    impl Expr8bis {
        fn into_with_ctx(self, e: Spanned<Expr>) -> Spanned<Expr> {
            match self {
                Self::And(opspan, e1, e2) => {
                    let e1: Spanned<Expr> = (*e1).into();
                    let span = e.span().join(e1.span()).unwrap();
                    e2.into_with_ctx(Spanned {
                        inner: Expr::BoolBinOp(Box::new(e), BoolBinOp::And, opspan, Box::new(e1)),
                        span,
                    })
                }
                Self::Empty => e,
            }
        }
    }

    #[derive(Debug)]
    pub(super) struct Expr9(Box<Expr10>, Box<Expr9bis>);

    impl Parse for Expr9 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr9(Box::new(input.parse()?), Box::new(input.parse()?)))
        }
    }

    impl Into<Spanned<Expr>> for Expr9 {
        fn into(self) -> Spanned<Expr> {
            let e0 = (*self.0).into();
            self.1.into_with_ctx(e0)
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr9bis {
        Or(Span, Box<Expr10>, Box<Expr9bis>),
        Empty,
    }

    impl Parse for Expr9bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![||]) {
                let span = input.parse::<Token![||]>()?.span();
                let e0 = input.parse::<Expr10>()?;
                let e1 = input.parse::<Expr9bis>()?;
                Ok(Expr9bis::Or(span, Box::new(e0), Box::new(e1)))
            } else {
                Ok(Expr9bis::Empty)
            }
        }
    }

    impl Expr9bis {
        fn into_with_ctx(self, e: Spanned<Expr>) -> Spanned<Expr> {
            match self {
                Self::Or(opspan, e1, e2) => {
                    let e1: Spanned<Expr> = (*e1).into();
                    let span = e.span().join(e1.span()).unwrap();
                    e2.into_with_ctx(Spanned {
                        inner: Expr::BoolBinOp(Box::new(e), BoolBinOp::Or, opspan, Box::new(e1)),
                        span,
                    })
                }
                Self::Empty => e,
            }
        }
    }

    #[derive(Debug)]
    pub(super) enum Expr10 {
        If(Span, Box<Expr0>, Box<Expr0>, Box<Expr0>, Span),
        Paren(Span, Box<Expr0>, Span),
        Unit(Span),
        Int(i64, Span),
        Float(f64, Span),
        Bool(bool, Span),
        Var(Ident),
        FunCall(Ident, Vec<Expr0>, Span),
        Merge(Ident, Box<Expr0>, Box<Expr0>, Span),
    }

    impl Parse for Expr10 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![if]) {
                let sp1 = input.parse::<Token![if]>()?.span();
                let cond = input.parse::<Expr0>()?;
                let then_branch;
                braced!(then_branch in input);
                let e1 = then_branch.parse::<Expr0>()?;
                let _ = input.parse::<Token![else]>()?;
                let else_branch;
                let sp2 = braced!(else_branch in input).span.close();
                let e2 = else_branch.parse::<Expr0>()?;
                Ok(Expr10::If(
                    sp1,
                    Box::new(cond),
                    Box::new(e1),
                    Box::new(e2),
                    sp2,
                ))
            } else if lookahead.peek(kw::merge) {
                let sp1 = input.parse::<kw::merge>()?.span();
                let cond = input.parse::<Ident>()?;
                let body;
                let sp2 = braced!(body in input).span.join();
                let b1 = body.parse::<LitBool>()?;
                let _ = body.parse::<Token![=>]>()?;
                let e1 = body.parse::<Expr0>()?;
                let _ = body.parse::<Token![,]>()?;
                let b2 = body.parse::<LitBool>()?;
                let _ = body.parse::<Token![=>]>()?;
                let e2 = body.parse::<Expr0>()?;
                let _ = body.parse::<Option<Token![,]>>()?;

                if !body.is_empty() {
                    return Err(body.error("Expected token }"));
                }
                if b1.value() == b2.value() {
                    return Err(body.error(format!("Found two {} branches in merge", b1.value())));
                }
                let (e1, e2) = if b1.value() { (e1, e2) } else { (e2, e1) };

                Ok(Expr10::Merge(
                    cond,
                    Box::new(e1),
                    Box::new(e2),
                    sp1.join(sp2).unwrap(),
                ))
            } else if lookahead.peek(Paren) {
                let content;
                let span = parenthesized!(content in input).span;
                if content.is_empty() {
                    Ok(Expr10::Unit(span.join()))
                } else {
                    let e = content.parse::<Expr0>()?;
                    Ok(Expr10::Paren(span.open(), Box::new(e), span.close()))
                }
            } else if lookahead.peek(LitInt) {
                let n_parse = input.parse::<LitInt>()?;
                let n = n_parse.base10_parse::<i64>()?;
                Ok(Expr10::Int(n, n_parse.span()))
            } else if lookahead.peek(LitFloat) {
                let x_parse = input.parse::<LitFloat>()?;
                let x = x_parse.base10_parse::<f64>()?;
                Ok(Expr10::Float(x, x_parse.span()))
            } else if lookahead.peek(LitBool) {
                let b_parse = input.parse::<LitBool>()?;
                let b = b_parse.value();
                Ok(Expr10::Bool(b, b_parse.span()))
            } else if lookahead.peek(Ident) {
                let id = input.parse::<Ident>()?;
                if input.peek(Paren) {
                    let content;
                    let span = parenthesized!(content in input).span.close();
                    let args: Vec<Expr0> = content
                        .parse_terminated(Expr0::parse, Token![,])?
                        .into_pairs()
                        .map(|pair| match pair {
                            Pair::Punctuated(t, _) | Pair::End(t) => t,
                        })
                        .collect();
                    Ok(Expr10::FunCall(id, args, span))
                } else {
                    Ok(Expr10::Var(id))
                }
            } else {
                Err(lookahead.error())
            }
        }
    }

    impl Into<Spanned<Expr>> for Expr10 {
        fn into(self) -> Spanned<Expr> {
            match self {
                Self::If(sp1, cond, e1, e2, sp2) => {
                    let cond = (*cond).into();
                    let e1: Spanned<Expr> = (*e1).into();
                    let e2: Spanned<Expr> = (*e2).into();

                    Spanned {
                        inner: Expr::If(Box::new(cond), Box::new(e1), Box::new(e2)),
                        span: sp1.join(sp2).unwrap(),
                    }
                }
                Self::Paren(sp1, e, sp2) => {
                    let e: Spanned<Expr> = (*e).into();
                    Spanned {
                        span: sp1.join(sp2).unwrap(),
                        ..e
                    }
                }
                Self::Int(n, sp) => Spanned {
                    inner: Expr::Int(n, sp),
                    span: sp,
                },
                Self::Float(x, sp) => Spanned {
                    inner: Expr::Float(x, sp),
                    span: sp,
                },
                Self::Bool(b, sp) => Spanned {
                    inner: Expr::Bool(b, sp),
                    span: sp,
                },
                Self::Var(id) => {
                    let span = id.span();
                    Spanned {
                        inner: Expr::Var(id),
                        span,
                    }
                }
                Self::FunCall(id, args, sp) => {
                    let span = id.span().join(sp).unwrap();
                    Spanned {
                        inner: Expr::FunCall(id, args.into_iter().map(Into::into).collect()),
                        span,
                    }
                }
                Self::Unit(span) => Spanned {
                    inner: Expr::Unit,
                    span,
                },
                Self::Merge(id, e1, e2, span) => Spanned {
                    inner: Expr::Merge(id, Box::new((*e1).into()), Box::new((*e2).into())),
                    span,
                },
            }
        }
    }
}

impl Parse for Spanned<Expr> {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let e = input.parse::<expr_internals::Expr0>()?;

        Ok(e.into())
    }
}

#[derive(Debug)]
pub struct DeclVar {
    pub id: Ident,
    pub ty: Type,
}

impl Parse for DeclVar {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<Type>()?;
        Ok(DeclVar { id, ty })
    }
}

#[derive(Debug)]
pub struct Decl {
    pub vars: Vec<DeclVar>,
    pub expr: Spanned<Expr>,
}

impl Parse for Decl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let vars = if input.peek(Paren) {
            let content;
            parenthesized!(content in input);

            content
                .parse_terminated(DeclVar::parse, Token![,])?
                .into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated(t, _) | Pair::End(t) => t,
                })
                .collect()
        } else {
            Punctuated::<DeclVar, Token![,]>::parse_separated_nonempty(input)?
                .into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated(t, _) | Pair::End(t) => t,
                })
                .collect()
        };

        let _ = input.parse::<Token![=]>()?;
        let expr = input.parse::<Spanned<Expr>>()?;

        Ok(Decl { vars, expr })
    }
}

#[derive(Debug)]
pub struct Body(pub Vec<Decl>);

impl Parse for Body {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(Token![where]) {
            let _ = input.parse::<Token![where]>()?;
            let decls: Vec<_> = Punctuated::<Decl, Token![,]>::parse_separated_nonempty(input)?
                .into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated(t, _) | Pair::End(t) => t,
                })
                .collect();
            if decls.is_empty() {
                return Err(input.error("A node with a `where` can't have an empty body"));
            }
            Ok(Body(decls))
        } else {
            Ok(Body(Vec::new()))
        }
    }
}

#[derive(Debug)]
pub struct Node {
    pub vis: Visibility,
    pub attrs: Vec<Attribute>,
    pub name: Ident,
    pub params: NodeParams,
    pub ret: NodeReturn,
    pub body: Body,
}

#[derive(Debug)]
pub struct NodeType {
    pub arg_types: Types,
    pub ret_types: Types,
}

impl Node {
    pub fn return_types(&self) -> Result<NodeType, Error> {
        let mut types = StringPatriciaMap::new();
        for equation in self.body.0.iter() {
            for var in equation.vars.iter() {
                types.insert(var.id.to_string(), var.ty.clone());
            }
        }
        for var in self.params.0.iter() {
            types.insert(var.id.to_string(), var.ty.clone());
        }
        let ret_types = self
            .ret
            .0
            .iter()
            .map(|ident| {
                types
                    .get(ident.to_string())
                    .cloned()
                    .ok_or_else(|| Error::undef_var(ident))
            })
            .collect::<Result<_, _>>()?;
        let arg_types = self.params.0.iter().map(|arg| arg.ty.clone()).collect();
        Ok(NodeType {
            arg_types,
            ret_types,
        })
    }
}

impl Parse for Node {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;
        let mut export = None;
        for (i, attr) in attrs.iter().enumerate() {
            let Meta::Path(meta) = &attr.meta else {
                continue;
            };
            let Some(id) = meta.get_ident() else {
                continue;
            };
            if id.to_string() == "export" {
                match export {
                    None => export = Some((i, attr.span())),
                    Some((_, span)) => {
                        return Err(input.error(format!(
                            "Multiple #[export] attribute found at {:?} and {:?}",
                            span,
                            attr.span()
                        )))
                    }
                }
            }
        }

        let export = export.map(|(i, _)| attrs.remove(i));

        let span = input.parse::<kw::node>()?.span;
        let vis = export
            .and(Some(Visibility::Public(Token![pub](span))))
            .unwrap_or(Visibility::Inherited);

        let name = input.parse::<Ident>()?;
        let params = input.parse::<NodeParams>()?;
        let _ = input.parse::<Token![=]>()?;
        let ret = input.parse::<NodeReturn>()?;
        let body = input.parse::<Body>()?;
        Ok(Node {
            vis,
            attrs,
            name,
            params,
            ret,
            body,
        })
    }
}

#[derive(Debug)]
pub struct Module {
    // TODO: remove when dev is finished
    pub pass: u32,
    pub nodes: Vec<Node>,
}

impl Parse for Module {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // TODO: remove when dev is finished
        let mut attrs = input.call(Attribute::parse_inner)?;
        if attrs.len() > 1 {
            panic!("Max une seule passe")
        }

        let pass = if let Some(attr) = attrs.pop() {
            let Meta::List(meta) = attr.meta else {
                panic!("Tu sais pas écrire")
            };
            let id = meta.path.require_ident()?;
            assert_eq!(id.to_string(), "pass");
            syn::parse2::<LitInt>(meta.tokens)?.base10_parse()?
        } else {
            u32::MAX
        };

        let nodes = input
            .parse_terminated(Node::parse, Token![;])?
            .into_pairs()
            .map(|pair| match pair {
                Pair::Punctuated(t, _) | Pair::End(t) => t,
            })
            .collect();

        Ok(Module { pass, nodes })
    }
}

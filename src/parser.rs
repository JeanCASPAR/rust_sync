use proc_macro2::Span;
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::{Pair, Punctuated},
    token::Paren,
    Ident, LitBool, LitFloat, LitInt, Token,
};

mod kw {
    use syn::custom_keyword;

    custom_keyword!(node);
    custom_keyword!(pre);
    custom_keyword!(merge);
    custom_keyword!(when);
}

enum Type {
    Int64,
    Float64,
    Bool,
}

impl Parse for Type {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(input.parse::<TypeSpan>()?.inner())
    }
}

struct TypeSpan {
    inner: Type,
    span: Span,
}

impl TypeSpan {
    fn span(&self) -> Span {
        self.span
    }

    fn inner(self) -> Type {
        self.inner
    }
}

impl Parse for TypeSpan {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ty_name = input.parse::<Ident>()?;
        let ty = match &ty_name.to_string() as &str {
            "int" => Type::Int64,
            "float" => Type::Float64,
            "bool" => Type::Bool,
            s => return Err(input.error(format!("Expected type int, float or bool, got {}", s))),
        };
        Ok(TypeSpan {
            inner: ty,
            span: ty_name.span(),
        })
    }
}

pub struct NodeParam {
    id: Ident,
    ty: Type,
    span: Span,
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

pub struct NodeParams(Vec<NodeParam>);

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

pub struct NodeReturn(Vec<Ident>);

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

pub enum MathBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Ge,
    Gt,
    Le,
    Lt,
    Eq,
    NEq,
    And,
    Or,
}

/// Expression grammar :
/// E0 -> E1 when var | E1
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
pub enum Expr {
    Var(Ident),
    Pre(Span, Box<ExprSpan>),
    Then(Box<ExprSpan>, Span, Box<ExprSpan>),
    Minus(Span, Box<ExprSpan>),
    Not(Span, Box<ExprSpan>),
    MathBinOp(Box<ExprSpan>, MathBinOp, Span, Box<ExprSpan>),
    If(Box<ExprSpan>, Box<ExprSpan>, Box<ExprSpan>),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    /// cast an int to a float
    FloatCast(Box<ExprSpan>),
    FunCall(Ident, Vec<ExprSpan>),
    Unit,
    Merge(Ident, Box<ExprSpan>, Box<ExprSpan>),
    When(Box<ExprSpan>, Span, Ident),
}
pub struct ExprSpan(Expr, Span);

impl ExprSpan {
    fn expr(self) -> Expr {
        self.0
    }
    fn span(&self) -> Span {
        self.1
    }
}

mod expr_internals {
    use syn::spanned::Spanned;

    use super::*;

    pub(super) enum Expr0 {
        When(Box<Expr1>, Span, Ident),
        Down(Box<Expr1>),
    }

    impl Parse for Expr0 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e = input.parse::<Expr1>()?;
            if input.peek(kw::when) {
                let sp = input.parse::<kw::when>()?.span();
                let id = input.parse::<Ident>()?;
                Ok(Expr0::When(Box::new(e), sp, id))
            } else {
                Ok(Expr0::Down(Box::new(e)))
            }
        }
    }

    impl Into<ExprSpan> for Expr0 {
        fn into(self) -> ExprSpan {
            match self {
                Self::When(e, sp, id) => {
                    let e: ExprSpan = (*e).into();
                    let sp = e.span().join(sp).unwrap().join(id.span()).unwrap();
                    ExprSpan(Expr::When(Box::new(e), sp, id), sp)
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

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

    impl Into<ExprSpan> for Expr1 {
        fn into(self) -> ExprSpan {
            match self {
                Self::Then(e1, sp, e2) => {
                    let e1: ExprSpan = (*e1).into();
                    let e2: ExprSpan = (*e2).into();
                    let span = e1.span().join(e2.span()).unwrap();
                    ExprSpan(Expr::Then(Box::new(e1), sp, Box::new(e2)), span)
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    pub(super) struct Expr2(Box<Expr3>, Box<Expr2bis>);

    impl Parse for Expr2 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e1 = input.parse::<Expr3>()?;
            let e2 = input.parse::<Expr2bis>()?;
            Ok(Expr2(Box::new(e1), Box::new(e2)))
        }
    }

    impl Into<ExprSpan> for Expr2 {
        fn into(self) -> ExprSpan {
            let e = (*self.0).into();
            self.1.into_with_ctx(e)
        }
    }

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
        fn into_with_ctx(self, e: ExprSpan) -> ExprSpan {
            match self {
                Self::Add(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: ExprSpan = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Add, sp, Box::new(e1)),
                        spe.join(sp1).unwrap(),
                    ))
                }
                Self::Sub(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: ExprSpan = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Sub, sp, Box::new(e1)),
                        spe.join(sp1).unwrap(),
                    ))
                }
                Self::Empty => e,
            }
        }
    }

    pub(super) struct Expr3(Box<Expr4>, Box<Expr3bis>);

    impl Parse for Expr3 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e1 = input.parse::<Expr4>()?;
            let e2 = input.parse::<Expr3bis>()?;
            Ok(Expr3(Box::new(e1), Box::new(e2)))
        }
    }

    impl Into<ExprSpan> for Expr3 {
        fn into(self) -> ExprSpan {
            let e = (*self.0).into();
            self.1.into_with_ctx(e)
        }
    }

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
        fn into_with_ctx(self, e: ExprSpan) -> ExprSpan {
            match self {
                Self::Mul(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: ExprSpan = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Mul, sp, Box::new(e1)),
                        spe.join(sp1).unwrap(),
                    ))
                }
                Self::Div(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: ExprSpan = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Div, sp, Box::new(e1)),
                        spe.join(sp1).unwrap(),
                    ))
                }
                Self::Rem(sp, e1, e2) => {
                    let spe = e.span();
                    let e1: ExprSpan = (*e1).into();
                    let sp1 = e1.span();
                    (*e2).into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Rem, sp, Box::new(e1)),
                        spe.join(sp1).unwrap(),
                    ))
                }
                Self::Empty => e,
            }
        }
    }

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

    impl Into<ExprSpan> for Expr4 {
        fn into(self) -> ExprSpan {
            match self {
                Self::Minus(opspan, e) => {
                    let e: ExprSpan = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    ExprSpan(Expr::Minus(opspan, Box::new(e)), span)
                }
                Self::Pre(opspan, e) => {
                    let e: ExprSpan = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    ExprSpan(Expr::Pre(opspan, Box::new(e)), span)
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    pub(super) enum Expr5 {
        FloatCast(Box<Expr6>, Span),
        Down(Box<Expr6>),
    }

    impl Parse for Expr5 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e = input.parse::<Expr6>()?;
            if input.peek(Token![as]) {
                let _ = input.parse::<Token![as]>()?;
                let ty = input.parse::<TypeSpan>()?;
                let span = ty.span();
                match ty.inner() {
                    Type::Float64 => Ok(Expr5::FloatCast(Box::new(e), span)),
                    _ => Err(input.error("You can only cast to float")),
                }
            } else {
                Ok(Expr5::Down(Box::new(e)))
            }
        }
    }

    impl Into<ExprSpan> for Expr5 {
        fn into(self) -> ExprSpan {
            match self {
                Self::FloatCast(e, sp) => {
                    let e: ExprSpan = (*e).into();
                    let span = e.span().join(sp).unwrap();
                    ExprSpan(Expr::FloatCast(Box::new(e)), span)
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

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

    impl Into<ExprSpan> for Expr6 {
        fn into(self) -> ExprSpan {
            let (e0, op, opspan, e1) = match self {
                Self::Ge(e0, opspan, e1) => (e0, MathBinOp::Ge, opspan, e1),
                Self::Gt(e0, opspan, e1) => (e0, MathBinOp::Gt, opspan, e1),
                Self::Le(e0, opspan, e1) => (e0, MathBinOp::Le, opspan, e1),
                Self::Lt(e0, opspan, e1) => (e0, MathBinOp::Lt, opspan, e1),
                Self::Eq(e0, opspan, e1) => (e0, MathBinOp::Eq, opspan, e1),
                Self::NEq(e0, opspan, e1) => (e0, MathBinOp::NEq, opspan, e1),
                Self::Down(e) => return (*e).into(),
            };
            let e0: ExprSpan = (*e0).into();
            let e1: ExprSpan = (*e1).into();
            let span = e0.span().join(e1.span()).unwrap();
            ExprSpan(
                Expr::MathBinOp(Box::new(e0), op, opspan, Box::new(e1)),
                span,
            )
        }
    }

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

    impl Into<ExprSpan> for Expr7 {
        fn into(self) -> ExprSpan {
            match self {
                Self::Not(opspan, e) => {
                    let e: ExprSpan = (*e).into();
                    let span = opspan.join(e.span()).unwrap();
                    ExprSpan(Expr::Not(opspan, Box::new(e)), span)
                }
                Self::Down(e) => (*e).into(),
            }
        }
    }

    pub(super) struct Expr8(Box<Expr9>, Box<Expr8bis>);

    impl Parse for Expr8 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr8(Box::new(input.parse()?), Box::new(input.parse()?)))
        }
    }

    impl Into<ExprSpan> for Expr8 {
        fn into(self) -> ExprSpan {
            let e0: ExprSpan = (*self.0).into();
            self.1.into_with_ctx(e0)
        }
    }

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
        fn into_with_ctx(self, e: ExprSpan) -> ExprSpan {
            match self {
                Self::And(opspan, e1, e2) => {
                    let e1: ExprSpan = (*e1).into();
                    let span = e.span().join(e1.span()).unwrap();
                    e2.into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::And, opspan, Box::new(e1)),
                        span,
                    ))
                }
                Self::Empty => e,
            }
        }
    }

    pub(super) struct Expr9(Box<Expr10>, Box<Expr9bis>);

    impl Parse for Expr9 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr9(Box::new(input.parse()?), Box::new(input.parse()?)))
        }
    }

    impl Into<ExprSpan> for Expr9 {
        fn into(self) -> ExprSpan {
            let e0 = (*self.0).into();
            self.1.into_with_ctx(e0)
        }
    }

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
        fn into_with_ctx(self, e: ExprSpan) -> ExprSpan {
            match self {
                Self::Or(opspan, e1, e2) => {
                    let e1: ExprSpan = (*e1).into();
                    let span = e.span().join(e1.span()).unwrap();
                    e2.into_with_ctx(ExprSpan(
                        Expr::MathBinOp(Box::new(e), MathBinOp::Or, opspan, Box::new(e1)),
                        span,
                    ))
                }
                Self::Empty => e,
            }
        }
    }

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

    impl Into<ExprSpan> for Expr10 {
        fn into(self) -> ExprSpan {
            match self {
                Self::If(sp1, cond, e1, e2, sp2) => {
                    let cond = (*cond).into();
                    let e1: ExprSpan = (*e1).into();
                    let e2: ExprSpan = (*e2).into();

                    ExprSpan(
                        Expr::If(Box::new(cond), Box::new(e1), Box::new(e2)),
                        sp1.join(sp2).unwrap(),
                    )
                }
                Self::Paren(sp1, e, sp2) => {
                    let e: ExprSpan = (*e).into();
                    ExprSpan(e.expr(), sp1.join(sp2).unwrap())
                }
                Self::Int(n, sp) => ExprSpan(Expr::Int(n, sp), sp),
                Self::Float(x, sp) => ExprSpan(Expr::Float(x, sp), sp),
                Self::Bool(b, sp) => ExprSpan(Expr::Bool(b, sp), sp),
                Self::Var(id) => {
                    let span = id.span();
                    ExprSpan(Expr::Var(id), span)
                }
                Self::FunCall(id, args, sp) => {
                    let span = id.span().join(sp).unwrap();
                    ExprSpan(
                        Expr::FunCall(id, args.into_iter().map(Into::into).collect()),
                        span,
                    )
                }
                Self::Unit(span) => ExprSpan(Expr::Unit, span),
                Self::Merge(id, e1, e2, span) => ExprSpan(
                    Expr::Merge(id, Box::new((*e1).into()), Box::new((*e2).into())),
                    span,
                ),
            }
        }
    }
}

impl Parse for ExprSpan {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let e = input.parse::<expr_internals::Expr0>()?;

        Ok(e.into())
    }
}

pub struct DeclVar {
    id: Ident,
    ty: Type,
}

impl Parse for DeclVar {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<Type>()?;
        Ok(DeclVar { id, ty })
    }
}

pub struct Decl {
    vars: Vec<DeclVar>,
    expr: ExprSpan,
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
        let expr = input.parse::<ExprSpan>()?;

        Ok(Decl { vars, expr })
    }
}

pub struct Body(Vec<Decl>);

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

pub struct Node {
    name: Ident,
    params: NodeParams,
    ret: NodeReturn,
    body: Body,
}

impl Parse for Node {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<kw::node>()?;
        let name = input.parse::<Ident>()?;
        let params = input.parse::<NodeParams>()?;
        let _ = input.parse::<Token![=]>()?;
        let ret = input.parse::<NodeReturn>()?;
        let body = input.parse::<Body>()?;
        Ok(Node {
            name,
            params,
            ret,
            body,
        })
    }
}

pub struct Nodes(Vec<Node>);

impl Parse for Nodes {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Nodes(
            input
                .parse_terminated(Node::parse, Token![;])?
                .into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated(t, _) | Pair::End(t) => t,
                })
                .collect(),
        ))
    }
}

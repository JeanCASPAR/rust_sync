use syn::{
    braced, parenthesized,
    parse::{discouraged::AnyDelimiter, Parse, ParseStream},
    punctuated::{Pair, Punctuated},
    token::Paren,
    Ident, LitBool, LitFloat, LitInt, Token,
};

mod kw {
    use syn::custom_keyword;

    custom_keyword!(node);
    custom_keyword!(pre);
}

enum Type {
    Int64,
    Float64,
    Bool,
}

impl Parse for Type {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ty_name = input.parse::<Ident>()?;
        match &ty_name.to_string() as &str {
            "int" => Ok(Type::Int64),
            "float" => Ok(Type::Float64),
            "bool" => Ok(Type::Bool),
            s => Err(input.error(format!("Expected type int, float or bool, got {}", s))),
        }
    }
}

pub struct NodeParam {
    id: Ident,
    ty: Type,
}

impl Parse for NodeParam {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<Type>()?;
        Ok(NodeParam { id, ty })
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
        if ret.is_empty() {
            return Err(input.error("Can't return no value"));
        }
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
    Not,
}

/// Expression grammar :
/// E0 -> E1 -> E0 | E1
/// E1 -> E1 + E2 | E1 - E2 | E2
/// E2 -> E2 * E3 | E2 / E3 | E2 % E3 | E3
/// E3 -> -E4 | pre E4 | E4
/// E4 -> E5 as float | E5
/// E5 -> E6 >= E6 | E6 > E6 | E6 <= E6 | E6 == E6 | E6 != E6 | E6
/// E6 -> !E7 | E7
/// E7 -> E7 && E8 | E7
/// E8 -> E8 || E9 | E9
/// E9 -> lit
///     | var
///     | fun ( E0, ..., E0 )
///     | if E0 { E0 } else { E0 }
///     | (E0)
/// <=========================>
///  E0 -> E1 => E0
///      | E1
///  E1 -> E2 E1'
///  E2 -> E3 E2'
///  E3 -> -E4
///      | pre E4
///      | E4
///  E4 -> E5 as float
///      | E5
///  E5 -> E6 >= E6
///      | E6 > E6
///      | E6 <= E6
///      | E6 < E6
///      | E6 == E6
///      | E6 != E6
///      | E6
///  E6 -> !E7
///      | E7
///  E7 -> E8 E7'
///  E8 -> E9 E8'
///  E9 -> lit
///      | var
///      | fun ( E0, ..., E0 )
///      | if E0 { E0 } else { E0 }
///      | (E0)
/// E1' -> + E2 E1'
///      | - E2 E1'
///      | ε
/// E2' -> * E3 E2'
///      | / E3 E2'
///      | % E3 E2'
///      | ε
/// E7' -> && E8 E7'
///      | ε
/// E8' -> || E9 E8'
///      | ε
///  ===================
///
/// E -> E0
/// after each -, we must check that there is no >, because -> is not a real token
/// and it makes the grammar ambiguous

pub enum Expr {
    Var(Ident),
    Pre(Box<Expr>),
    Then(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>),
    Not(Box<Expr>),
    MathBinOp(Box<Expr>, MathBinOp, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Int(i64),
    Float(f64),
    Bool(bool),
    /// cast an int to a float
    FloatCast(Box<Expr>),
    FunCall(Ident, Vec<Expr>),
}

mod expr_internals {
    use super::*;

    pub enum Expr0 {
        Then(Expr1, Box<Expr0>),
        Down(Expr1),
    }

    impl Parse for Expr0 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            println!("before : {}", input);
            let e1 = input.parse::<Expr1>()?;
            println!("after : {}", input);
            if input.peek(Token![->]) {
                let _ = input.parse::<Token![->]>()?;
                let e2 = input.parse::<Expr0>()?;
                Ok(Expr0::Then(e1, Box::new(e2)))
            } else {
                Ok(Expr0::Down(e1))
            }
        }
    }

    impl Into<Expr> for Expr0 {
        fn into(self) -> Expr {
            match self {
                Self::Then(e1, e2) => Expr::Then(Box::new(e1.into()), Box::new((*e2).into())),
                Self::Down(e) => e.into(),
            }
        }
    }

    struct Expr1(Expr2, Expr1bis);

    impl Parse for Expr1 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr1(input.parse::<Expr2>()?, input.parse::<Expr1bis>()?))
        }
    }

    impl Into<Expr> for Expr1 {
        fn into(self) -> Expr {
            let e = self.0.into();
            self.1.into_with_ctx(e)
        }
    }

    enum Expr1bis {
        Add(Expr2, Box<Expr1bis>),
        Sub(Expr2, Box<Expr1bis>),
        Empty,
    }

    impl Parse for Expr1bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![+]) {
                let _ = input.parse::<Token![+]>()?;
                let e1 = input.parse::<Expr2>()?;
                let e2 = input.parse::<Expr1bis>()?;
                Ok(Expr1bis::Add(e1, Box::new(e2)))
            } else if input.peek(Token![-]) && !input.peek2(Token![>]) {
                let _ = input.parse::<Token![-]>()?;
                let e1 = input.parse::<Expr2>()?;
                let e2 = input.parse::<Expr1bis>()?;
                Ok(Expr1bis::Sub(e1, Box::new(e2)))
            } else {
                Ok(Expr1bis::Empty)
            }
        }
    }

    impl Expr1bis {
        fn into_with_ctx(self, e: Expr) -> Expr {
            match self {
                Self::Add(e1, e2) => (*e2).into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Add,
                    Box::new(e1.into()),
                )),
                Self::Sub(e1, e2) => (*e2).into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Sub,
                    Box::new(e1.into()),
                )),
                Self::Empty => e,
            }
        }
    }

    struct Expr2(Expr3, Expr2bis);

    impl Parse for Expr2 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr2(input.parse::<Expr3>()?, input.parse::<Expr2bis>()?))
        }
    }

    impl Into<Expr> for Expr2 {
        fn into(self) -> Expr {
            let e = self.0.into();
            self.1.into_with_ctx(e)
        }
    }

    enum Expr2bis {
        Mul(Expr3, Box<Expr2bis>),
        Div(Expr3, Box<Expr2bis>),
        Rem(Expr3, Box<Expr2bis>),
        Empty,
    }

    impl Parse for Expr2bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![*]) {
                let _ = input.parse::<Token![*]>()?;
                let e1 = input.parse::<Expr3>()?;
                let e2 = input.parse::<Expr2bis>()?;
                Ok(Expr2bis::Mul(e1, Box::new(e2)))
            } else if input.peek(Token![/]) {
                let _ = input.parse::<Token![/]>()?;
                let e1 = input.parse::<Expr3>()?;
                let e2 = input.parse::<Expr2bis>()?;
                Ok(Expr2bis::Div(e1, Box::new(e2)))
            } else if input.peek(Token![%]) {
                let _ = input.parse::<Token![%]>()?;
                let e1 = input.parse::<Expr3>()?;
                let e2 = input.parse::<Expr2bis>()?;
                Ok(Expr2bis::Rem(e1, Box::new(e2)))
            } else {
                Ok(Expr2bis::Empty)
            }
        }
    }

    impl Expr2bis {
        fn into_with_ctx(self, e: Expr) -> Expr {
            match self {
                Self::Mul(e1, e2) => (*e2).into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Mul,
                    Box::new(e1.into()),
                )),
                Self::Div(e1, e2) => (*e2).into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Div,
                    Box::new(e1.into()),
                )),
                Self::Rem(e1, e2) => (*e2).into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Rem,
                    Box::new(e1.into()),
                )),
                Self::Empty => e,
            }
        }
    }

    enum Expr3 {
        Minus(Expr4),
        Pre(Expr4),
        Down(Expr4),
    }

    impl Parse for Expr3 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![-]) && !input.peek2(Token![>]) {
                let _ = input.parse::<Token![-]>()?;
                let e = input.parse::<Expr4>()?;
                Ok(Expr3::Minus(e))
            } else if input.peek(kw::pre) {
                let _ = input.parse::<kw::pre>()?;
                let e = input.parse::<Expr4>()?;
                Ok(Expr3::Pre(e))
            } else {
                let e = input.parse::<Expr4>()?;
                Ok(Expr3::Down(e))
            }
        }
    }

    impl Into<Expr> for Expr3 {
        fn into(self) -> Expr {
            match self {
                Self::Minus(e) => Expr::Minus(Box::new(e.into())),
                Self::Pre(e) => Expr::Pre(Box::new(e.into())),
                Self::Down(e) => e.into(),
            }
        }
    }

    enum Expr4 {
        FloatCast(Expr5),
        Down(Expr5),
    }

    impl Parse for Expr4 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e = input.parse::<Expr5>()?;
            if input.peek(Token![as]) {
                let _ = input.parse::<Token![as]>()?;
                let ty = input.parse::<Type>()?;
                match ty {
                    Type::Float64 => Ok(Expr4::FloatCast(e)),
                    _ => Err(input.error("You can only cast to float")),
                }
            } else {
                Ok(Expr4::Down(e))
            }
        }
    }

    impl Into<Expr> for Expr4 {
        fn into(self) -> Expr {
            match self {
                Self::FloatCast(e) => Expr::FloatCast(Box::new(e.into())),
                Self::Down(e) => e.into(),
            }
        }
    }

    enum Expr5 {
        Ge(Expr6, Expr6),
        Gt(Expr6, Expr6),
        Le(Expr6, Expr6),
        Lt(Expr6, Expr6),
        Eq(Expr6, Expr6),
        NEq(Expr6, Expr6),
        Down(Expr6),
    }

    impl Parse for Expr5 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let e0 = input.parse::<Expr6>()?;
            let lookahead = input.lookahead1();
            let op = if lookahead.peek(Token![>=]) {
                let _ = input.parse::<Token![>=]>()?;
                Expr5::Ge
            } else if lookahead.peek(Token![>]) {
                let _ = input.parse::<Token![>]>()?;
                Expr5::Gt
            } else if lookahead.peek(Token![<=]) {
                let _ = input.parse::<Token![<=]>()?;
                Expr5::Le
            } else if lookahead.peek(Token![<]) {
                let _ = input.parse::<Token![<]>()?;
                Expr5::Lt
            } else if lookahead.peek(Token![==]) {
                let _ = input.parse::<Token![==]>()?;
                Expr5::Eq
            } else if lookahead.peek(Token![!=]) {
                let _ = input.parse::<Token![==]>()?;
                Expr5::NEq
            } else {
                return Ok(Expr5::Down(e0));
            };
            let e1 = input.parse::<Expr6>()?;
            Ok(op(e0, e1))
        }
    }

    impl Into<Expr> for Expr5 {
        fn into(self) -> Expr {
            match self {
                Self::Ge(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::Ge, Box::new(e1.into()))
                }
                Self::Gt(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::Gt, Box::new(e1.into()))
                }
                Self::Le(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::Le, Box::new(e1.into()))
                }
                Self::Lt(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::Lt, Box::new(e1.into()))
                }
                Self::Eq(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::Eq, Box::new(e1.into()))
                }
                Self::NEq(e0, e1) => {
                    Expr::MathBinOp(Box::new(e0.into()), MathBinOp::NEq, Box::new(e1.into()))
                }
                Self::Down(e) => e.into(),
            }
        }
    }

    enum Expr6 {
        Not(Expr7),
        Down(Expr7),
    }

    impl Parse for Expr6 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![!]) {
                let _ = input.parse::<Token![!]>()?;
                Ok(Expr6::Not(input.parse()?))
            } else {
                Ok(Expr6::Down(input.parse()?))
            }
        }
    }

    impl Into<Expr> for Expr6 {
        fn into(self) -> Expr {
            match self {
                Self::Not(e) => Expr::Not(Box::new(e.into())),
                Self::Down(e) => e.into(),
            }
        }
    }

    struct Expr7(Expr8, Expr7bis);

    impl Parse for Expr7 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr7(input.parse()?, input.parse()?))
        }
    }

    impl Into<Expr> for Expr7 {
        fn into(self) -> Expr {
            let e0 = self.0.into();
            self.1.into_with_ctx(e0)
        }
    }

    enum Expr7bis {
        And(Expr8, Box<Expr7bis>),
        Empty,
    }

    impl Parse for Expr7bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![&&]) {
                let _ = input.parse::<Token![&&]>()?;
                let e0 = input.parse::<Expr8>()?;
                let e1 = input.parse::<Expr7bis>()?;
                Ok(Expr7bis::And(e0, Box::new(e1)))
            } else {
                Ok(Expr7bis::Empty)
            }
        }
    }

    impl Expr7bis {
        fn into_with_ctx(self, e: Expr) -> Expr {
            match self {
                Self::And(e0, e1) => e1.into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::And,
                    Box::new(e0.into()),
                )),
                Self::Empty => e,
            }
        }
    }

    struct Expr8(Expr9, Expr8bis);

    impl Parse for Expr8 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            Ok(Expr8(input.parse()?, input.parse()?))
        }
    }

    impl Into<Expr> for Expr8 {
        fn into(self) -> Expr {
            let e0 = self.0.into();
            self.1.into_with_ctx(e0)
        }
    }

    enum Expr8bis {
        Or(Expr9, Box<Expr8bis>),
        Empty,
    }

    impl Parse for Expr8bis {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            if input.peek(Token![||]) {
                let _ = input.parse::<Token![||]>()?;
                let e0 = input.parse::<Expr9>()?;
                let e1 = input.parse::<Expr8bis>()?;
                Ok(Expr8bis::Or(e0, Box::new(e1)))
            } else {
                Ok(Expr8bis::Empty)
            }
        }
    }

    impl Expr8bis {
        fn into_with_ctx(self, e: Expr) -> Expr {
            match self {
                Self::Or(e0, e1) => e1.into_with_ctx(Expr::MathBinOp(
                    Box::new(e),
                    MathBinOp::Or,
                    Box::new(e0.into()),
                )),
                Self::Empty => e,
            }
        }
    }

    enum Expr9 {
        If(Box<Expr0>, Box<Expr0>, Box<Expr0>),
        Paren(Box<Expr0>),
        Int(i64),
        Float(f64),
        Bool(bool),
        Var(Ident),
        FunCall(Ident, Vec<Expr0>),
    }

    impl Parse for Expr9 {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let lookahead = input.lookahead1();
            if lookahead.peek(Token![if]) {
                let _ = input.parse::<Token![if]>()?;
                let cond = input.parse::<Expr0>()?;
                let then_branch;
                braced!(then_branch in input);
                let e1 = then_branch.parse::<Expr0>()?;
                let _ = input.parse::<Token![else]>()?;
                let else_branch;
                braced!(else_branch in input);
                let e2 = else_branch.parse::<Expr0>()?;
                Ok(Expr9::If(Box::new(cond), Box::new(e1), Box::new(e2)))
            } else if lookahead.peek(Paren) {
                let content;
                parenthesized!(content in input);
                let e = content.parse::<Expr0>()?;
                Ok(Expr9::Paren(Box::new(e)))
            } else if lookahead.peek(LitInt) {
                let n = input.parse::<LitInt>()?.base10_parse::<i64>()?;
                Ok(Expr9::Int(n))
            } else if lookahead.peek(LitFloat) {
                let x = input.parse::<LitFloat>()?.base10_parse::<f64>()?;
                Ok(Expr9::Float(x))
            } else if lookahead.peek(LitBool) {
                let b = input.parse::<LitBool>()?.value();
                Ok(Expr9::Bool(b))
            } else if lookahead.peek(Ident) {
                let id = input.parse::<Ident>()?;
                if input.peek(Paren) {
                    let content;
                    parenthesized!(content in input);
                    let args: Vec<Expr0> = content
                        .parse_terminated(Expr0::parse, Token![,])?
                        .into_pairs()
                        .map(|pair| match pair {
                            Pair::Punctuated(t, _) | Pair::End(t) => t,
                        })
                        .collect();
                    Ok(Expr9::FunCall(id, args))
                } else {
                    Ok(Expr9::Var(id))
                }
            } else {
                Err(lookahead.error())
            }
        }
    }

    impl Into<Expr> for Expr9 {
        fn into(self) -> Expr {
            match self {
                Self::If(cond, e1, e2) => Expr::If(
                    Box::new((*cond).into()),
                    Box::new((*e1).into()),
                    Box::new((*e2).into()),
                ),
                Self::Paren(e) => (*e).into(),
                Self::Int(n) => Expr::Int(n),
                Self::Float(x) => Expr::Float(x),
                Self::Bool(b) => Expr::Bool(b),
                Self::Var(id) => Expr::Var(id),
                Self::FunCall(id, args) => {
                    Expr::FunCall(id, args.into_iter().map(Into::into).collect())
                }
            }
        }
    }
}

impl Parse for Expr {
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
    expr: Expr,
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
        let expr = input.parse::<Expr>()?;

        Ok(Decl { vars, expr })
    }
}

pub struct Body(Vec<Decl>);

impl Parse for Body {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let _ = input.parse::<Token![where]>()?;
        let decls: Vec<_> = Punctuated::<Decl, Token![,]>::parse_separated_nonempty(input)?
            .into_pairs()
            .map(|pair| match pair {
                Pair::Punctuated(t, _) | Pair::End(t) => t,
            })
            .collect();
        if decls.is_empty() {
            return Err(input.error("A node can't have an empty body"));
        }
        Ok(Body(decls))
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

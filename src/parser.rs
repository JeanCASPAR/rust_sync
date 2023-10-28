use std::thread::LocalKey;

use quote::ToTokens;
use syn::{
    braced, parenthesized,
    parse::{Parse, ParseStream},
    punctuated::{Pair, Punctuated},
    token::Paren,
    Ident, Lit, LitBool, LitFloat, LitInt, Token,
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
}

pub enum Expr {
    Var(Ident),
    Pre(Box<Expr>),
    Then(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>),
    MathBinOp(Box<Expr>, MathBinOp, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl Parse for Expr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        enum Expr0 {
            Then(Expr1, Box<Expr0>),
            Down(Expr1),
        }

        impl Parse for Expr0 {
            fn parse(input: ParseStream) -> syn::Result<Self> {
                let e1 = input.parse::<Expr1>()?;
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

        enum Expr1 {
            Add(Expr2, Box<Expr0>),
            Sub(Expr2, Box<Expr0>),
            Down(Expr2),
        }

        impl Parse for Expr1 {
            fn parse(input: ParseStream) -> syn::Result<Self> {
                let e1 = input.parse::<Expr2>()?;
                if input.peek(Token![+]) {
                    let _ = input.parse::<Token![+]>()?;
                    let e2 = input.parse::<Expr0>()?;
                    Ok(Expr1::Add(e1, Box::new(e2)))
                } else if input.peek(Token![-]) {
                    let _ = input.parse::<Token![-]>()?;
                    let e2 = input.parse::<Expr0>()?;
                    Ok(Expr1::Sub(e1, Box::new(e2)))
                } else {
                    Ok(Expr1::Down(e1))
                }
            }
        }

        impl Into<Expr> for Expr1 {
            fn into(self) -> Expr {
                match self {
                    Self::Add(e1, e2) => Expr::MathBinOp(
                        Box::new(e1.into()),
                        MathBinOp::Add,
                        Box::new(((*e2).into())),
                    ),
                    Self::Sub(e1, e2) => Expr::MathBinOp(
                        Box::new(e1.into()),
                        MathBinOp::Sub,
                        Box::new(((*e2).into())),
                    ),
                    Self::Down(e) => e.into(),
                }
            }
        }

        enum Expr2 {
            Mul(Expr3, Box<Expr0>),
            Div(Expr3, Box<Expr0>),
            Rem(Expr3, Box<Expr0>),
            Down(Expr3),
        }

        impl Parse for Expr2 {
            fn parse(input: ParseStream) -> syn::Result<Self> {
                let e1 = input.parse::<Expr3>()?;
                if input.peek(Token![*]) {
                    let _ = input.parse::<Token![*]>()?;
                    let e2 = input.parse::<Expr0>()?;
                    Ok(Expr2::Mul(e1, Box::new(e2)))
                } else if input.peek(Token![/]) {
                    let _ = input.parse::<Token![/]>()?;
                    let e2 = input.parse::<Expr0>()?;
                    Ok(Expr2::Div(e1, Box::new(e2)))
                } else if input.peek(Token![%]) {
                    let _ = input.parse::<Token![%]>()?;
                    let e2 = input.parse::<Expr0>()?;
                    Ok(Expr2::Rem(e1, Box::new(e2)))
                } else {
                    Ok(Expr2::Down(e1))
                }
            }
        }

        impl Into<Expr> for Expr2 {
            fn into(self) -> Expr {
                match self {
                    Self::Mul(e1, e2) => Expr::MathBinOp(
                        Box::new(e1.into()),
                        MathBinOp::Mul,
                        Box::new(((*e2).into())),
                    ),
                    Self::Div(e1, e2) => Expr::MathBinOp(
                        Box::new(e1.into()),
                        MathBinOp::Div,
                        Box::new(((*e2).into())),
                    ),
                    Self::Rem(e1, e2) => Expr::MathBinOp(
                        Box::new(e1.into()),
                        MathBinOp::Rem,
                        Box::new(((*e2).into())),
                    ),
                    Self::Down(e) => e.into(),
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
                if input.peek(Token![-]) {
                    let _ = input.parse::<Token![-]>()?;
                    let e = input.parse::<Expr4>()?;
                    Ok(Expr3::Minus(e))
                } else if input.peek(kw::pre) {
                    let _ = input.parse::<kw::pre>()?;
                    let e = input.parse::<Expr4>()?;
                    Ok(Expr3::Minus(e))
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
            If(Box<Expr0>, Box<Expr0>, Box<Expr0>),
            Paren(Box<Expr0>),
            Int(i64),
            Float(f64),
            Bool(bool),
            Var(Ident),
        }

        impl Parse for Expr4 {
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
                    Ok(Expr4::If(Box::new(cond), Box::new(e1), Box::new(e2)))
                } else if lookahead.peek(Paren) {
                    let content;
                    parenthesized!(content in input);
                    let e = content.parse::<Expr0>()?;
                    Ok(Expr4::Paren(Box::new(e)))
                } else if lookahead.peek(LitInt) {
                    let n = input.parse::<LitInt>()?.base10_parse::<i64>()?;
                    Ok(Expr4::Int(n))
                } else if lookahead.peek(LitFloat) {
                    let x = input.parse::<LitFloat>()?.base10_parse::<f64>()?;
                    Ok(Expr4::Float(x))
                } else if lookahead.peek(LitBool) {
                    let b = input.parse::<LitBool>()?.value();
                    Ok(Expr4::Bool(b))
                } else if lookahead.peek(Ident) {
                    let id = input.parse::<Ident>()?;
                    Ok(Expr4::Var(id))
                } else {
                    Err(lookahead.error())
                }
            }
        }

        impl Into<Expr> for Expr4 {
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
                }
            }
        }

        let e = input.parse::<Expr0>()?;

        // Ok(Expr::Lit(input.parse::<Literal>()?))
        Ok(e.into())
    }
}

pub struct Decl {
    id: Ident,
    ty: Type,
    expr: Expr,
}

impl Parse for Decl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let id = input.parse::<Ident>()?;
        let _ = input.parse::<Token![:]>()?;
        let ty = input.parse::<Type>()?;
        let _ = input.parse::<Token![=]>()?;
        let expr = input.parse::<Expr>()?;
        Ok(Decl { id, ty, expr })
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

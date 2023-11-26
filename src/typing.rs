use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use proc_macro_error::OptionExt;
use syn::Ident;

use crate::{
    error::Error,
    parser::{
        Decl as PDecl, Expr as PExpr, ExprSpan as PExprSpan, MathBinOp, Node as PNode, NodeParams,
        NodeType, Nodes, Type,
    },
};

pub struct Ast {
    nodes: Vec<Node>,
}

type Map<T> = StringPatriciaMap<T>;

impl TryFrom<Nodes> for Ast {
    type Error = Error;
    fn try_from(nodes: Nodes) -> Result<Self, Self::Error> {
        let mut node_types = Map::new();
        for node in nodes.0.iter() {
            node_types.insert(node.name.to_string(), node.return_types()?);
        }
        Ok(Self {
            nodes: nodes
                .0
                .into_iter()
                .map(|node| Node::from_untyped(node, &node_types))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }
}

pub struct Node {
    pub name: Ident,
    pub params: NodeParams,
    pub ret: Vec<(Ident, Type)>,
    pub body: Vec<Decl>,
}

impl Node {
    fn from_untyped(node: PNode, node_types: &Map<NodeType>) -> Result<Self, Error> {
        // Create the context of the node, that is, the type of every declared variable.
        let mut context: Map<(Type, Span)> = Map::new();
        // Register all the variable declarations, starting with formal arguments and then the
        // equation declarations. This ensures that duplicate variables are reported in the same
        // order they appear in the code.
        for (var_name, var_span, var_type) in node
            .params
            .0
            .iter()
            .map(|param| (param.id.to_string(), param.id.span(), param.ty.clone()))
            .chain(
                node.body
                    .0
                    .iter()
                    .flat_map(|equation| equation.vars.iter())
                    .map(|var| (var.id.to_string(), var.id.span(), var.ty.clone())),
            )
        {
            if let Some((_, def_span)) = context.insert(&var_name, (var_type, var_span)) {
                return Err(Error::twice_var(var_name, def_span, var_span));
            }
        }
        Ok(Self {
            params: node.params,
            ret: node
                .ret
                .0
                .into_iter()
                .zip(
                    node_types
                        .get(node.name.to_string())
                        .unwrap()
                        .ret_types
                        .iter()
                        .cloned(),
                )
                .collect(),
            name: node.name,
            body: node
                .body
                .0
                .into_iter()
                .map(|decl| Decl::from_untyped(decl, &context, node_types))
                .collect::<Result<_, _>>()?,
        })
    }
}

pub struct Decl {
    id: Ident,
    ty: Type,
    expr: Expr,
}

impl Decl {
    fn from_untyped(
        decl: PDecl,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
    ) -> Result<Self, Error> {
        let (id, ty) = match &decl.vars[..] {
            [var] => (var.id.clone(), var.ty.clone()),
            _ => todo!("Destructuring tuples is not implemented yet..."),
        };
        let expr = Expr::from_untyped(decl.expr, context, node_types, Some(ty.clone()))?;
        if expr.ty != ty {
            return Err(Error::type_mismatch(id.span(), ty, expr.ty));
        }
        Ok(Self { id, ty, expr })
    }
}

pub struct Expr {
    ty: Type,
    kind: ExprKind,
}

impl Expr {
    fn from_untyped(
        expr: PExprSpan,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
        toplevel_type: Option<Type>,
    ) -> Result<Self, Error> {
        Self::do_stuff(expr, context, node_types, 0, toplevel_type)
    }

    fn do_stuff(
        expr: PExprSpan,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
        first_index: u16,
        toplevel_type: Option<Type>,
    ) -> Result<Self, Error> {
        let span = expr.span();
        let expr = expr.inner();
        Ok(match expr {
            PExpr::Var(var) => {
                let var_name = var.to_string();
                let ty = context
                    .get(var_name)
                    .ok_or_else(|| Error::undef_var(&var))?
                    .0
                    .clone();
                Self {
                    ty,
                    kind: ExprKind::Var(var),
                }
            }
            PExpr::Unit => Self {
                ty: Type::Unit,
                kind: ExprKind::Unit,
            },
            PExpr::Pre(_, e) => {
                if first_index == 0 {
                    return Err(Error::negative_first_index(span));
                }
                let typed_e = Self::do_stuff(*e, context, node_types, first_index - 1, None)?;
                Self {
                    ty: typed_e.ty.clone(),
                    kind: ExprKind::Pre(Box::new(typed_e)),
                }
            }
            PExpr::Then(head, _, tail) => {
                let head_expr = Self::do_stuff(*head, context, node_types, first_index, None)?;
                let tail_expr = Self::do_stuff(*tail, context, node_types, first_index + 1, None)?;
                if head_expr.ty != tail_expr.ty {
                    return Err(Error::then_type_mismatch(span, head_expr.ty, tail_expr.ty));
                }
                Self {
                    ty: head_expr.ty.clone(),
                    kind: ExprKind::Then(Box::new(head_expr), Box::new(tail_expr)),
                }
            }
            PExpr::Minus(_, e) => {
                let typed_e = Self::do_stuff(*e, context, node_types, first_index, None)?;
                if typed_e.ty == Type::Bool {
                    return Err(Error::bool_arithmetic(span));
                }
                Self {
                    ty: typed_e.ty.clone(),
                    kind: ExprKind::Minus(Box::new(typed_e)),
                }
            }
            PExpr::Not(_, e) => {
                let typed_e = Self::do_stuff(*e, context, node_types, first_index, None)?;
                if typed_e.ty != Type::Bool {
                    return Err(Error::number_logic(span));
                }
                Self {
                    ty: typed_e.ty.clone(),
                    kind: ExprKind::Not(Box::new(typed_e)),
                }
            }
            PExpr::MathBinOp(left, op, _, right) => {
                let typed_left = Self::do_stuff(*left, context, node_types, first_index, None)?;
                let typed_right = Self::do_stuff(*right, context, node_types, first_index, None)?;
                if typed_left.ty != typed_right.ty {
                    return Err(Error::type_mismatch(span, typed_left.ty, typed_right.ty));
                }

                let ty = typed_left.ty.clone();
                if ty == Type::Bool {
                    return Err(Error::bool_arithmetic(span));
                }
                Self {
                    ty,
                    kind: ExprKind::BinOp(Box::new(typed_left), op, Box::new(typed_right)),
                }
            }
            PExpr::If(cond, then_branch, else_branch) => {
                let typed_then =
                    Self::do_stuff(*then_branch, context, node_types, first_index, None)?;
                let typed_else =
                    Self::do_stuff(*else_branch, context, node_types, first_index, None)?;
                let typed_cond = Self::do_stuff(*cond, context, node_types, first_index, None)?;
                if typed_then.ty != typed_else.ty {
                    return Err(Error::type_mismatch(span, typed_then.ty, typed_else.ty));
                }
                if typed_cond.ty != Type::Bool {
                    return Err(Error::non_bool_cond(span));
                }

                let ty = typed_then.ty.clone();

                Self {
                    ty,
                    kind: ExprKind::If(
                        Box::new(typed_cond),
                        Box::new(typed_then),
                        Box::new(typed_else),
                    ),
                }
            }
            PExpr::Int(i, _) => Self {
                ty: Type::Int64,
                kind: ExprKind::Int(i),
            },
            PExpr::Float(f, _) => Self {
                ty: Type::Float64,
                kind: ExprKind::Float(f),
            },
            PExpr::Bool(b, _) => Self {
                ty: Type::Bool,
                kind: ExprKind::Bool(b),
            },
            PExpr::FloatCast(casted) => {
                let typed_casted = Self::do_stuff(*casted, context, node_types, first_index, None)?;
                fn unroll_when(ty: Type) -> Option<Type> {
                    match ty {
                        Type::Int64 => Some(Type::Int64),
                        Type::When(ty, id) => Some(Type::When(Box::new(unroll_when(*ty)?), id)),
                        Type::WhenNot(ty, id) => {
                            Some(Type::WhenNot(Box::new(unroll_when(*ty)?), id))
                        }
                        Type::Bool | Type::Unit | Type::Float64 => None,
                    }
                }
                let Some(ty) = unroll_when(typed_casted.ty.clone()) else {
                    return Err(Error::float_cast(span, typed_casted.ty));
                };
                Self {
                    ty,
                    kind: ExprKind::FloatCast(Box::new(typed_casted)),
                }
            }
            PExpr::When(e, _, id) => {
                // TODO: check that the expected type is a when and replace None by the correct type
                // when implemented
                let e = Self::do_stuff(*e, context, node_types, first_index, None)?;
                Self {
                    ty: Type::When(Box::new(e.ty.clone()), id.clone()),
                    kind: ExprKind::When(Box::new(e), id),
                }
            }
            PExpr::WhenNot(e, _, id) => {
                // TODO: check that the expected type is a whennot and replace None by the correct type
                // when implemented
                let e = Self::do_stuff(*e, context, node_types, first_index, None)?;
                Self {
                    ty: Type::WhenNot(Box::new(e.ty.clone()), id.clone()),
                    kind: ExprKind::WhenNot(Box::new(e), id),
                }
            }
            PExpr::Merge(id, e_when, e_whennot) => {
                let e_when = Self::do_stuff(
                    *e_when,
                    context,
                    node_types,
                    first_index,
                    toplevel_type
                        .clone()
                        .map(|ty| Type::When(Box::new(ty), id.clone())),
                )?;
                let e_whennot = Self::do_stuff(
                    *e_whennot,
                    context,
                    node_types,
                    first_index,
                    toplevel_type
                        .clone()
                        .map(|ty| Type::WhenNot(Box::new(ty), id.clone())),
                )?;

                // TODO: I assume here than e_when and e_whennot have the good types
                Self {
                    ty: toplevel_type.unwrap(),
                    kind: ExprKind::Merge(id, Box::new(e_when), Box::new(e_whennot)),
                }
            }
            PExpr::FunCall(f, args) => {
                let f_symb = f.to_string();
                let typed_args = args
                    .into_iter()
                    .map(|arg| Self::do_stuff(arg, context, node_types, first_index, None))
                    .collect::<Result<_, _>>()?;
                let ty = if let Some(node_type) = node_types.get(&f_symb) {
                    match &node_type.ret_types[..] {
                        [ty] => ty.clone(),
                        _ => todo!("Destructuring tuples is not implemented yet..."),
                    }
                } else if let Some(ty) = toplevel_type {
                    ty
                } else {
                    // Raise error
                    return Err(Error::external_symbol_not_toplevel(f.span(), f.to_string()));
                };

                Self {
                    ty,
                    kind: ExprKind::FunCall {
                        function: f,
                        arguments: typed_args,
                    },
                }
            }
        })
    }
}

pub enum ExprKind {
    Var(Ident),
    Unit,
    Pre(Box<Expr>),
    Then(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>),
    Not(Box<Expr>),
    BinOp(Box<Expr>, MathBinOp, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Int(i64),
    Float(f64),
    Bool(bool),
    FloatCast(Box<Expr>),
    When(Box<Expr>, Ident),
    WhenNot(Box<Expr>, Ident),
    Merge(Ident, Box<Expr>, Box<Expr>),
    FunCall {
        function: Ident,
        arguments: Vec<Expr>,
    },
}

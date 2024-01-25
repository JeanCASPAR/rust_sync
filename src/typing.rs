use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use smallvec::smallvec as types;
use syn::{Ident, Visibility};

use crate::{
    error::Error,
    parser::{
        BaseType, BoolBinOp, ClockType, CompOp, Decl as PDecl, DeclVar, Expr as PExpr, MathBinOp,
        Module, Node as PNode, NodeParams, NodeType, Spanned, Type, Types,
    },
};

#[derive(Debug)]
pub struct Ast {
    pub nodes: Vec<Node>,
    pub extern_functions: Vec<Ident>,
}

type Map<T> = StringPatriciaMap<T>;

impl TryFrom<Module> for Ast {
    type Error = Error;
    fn try_from(module: Module) -> Result<Self, Self::Error> {
        let mut node_types = Map::new();
        let mut extern_functions = Vec::new();
        for node in module.nodes.iter() {
            node_types.insert(node.name.to_string(), node.return_types()?);
        }
        let nodes = module
            .nodes
            .into_iter()
            .map(|node| Node::from_untyped(node, &node_types, &mut extern_functions))
            .collect::<Result<Vec<_>, _>>()?;

        extern_functions.sort_unstable();
        extern_functions.dedup();

        Ok(Self {
            nodes,
            extern_functions,
        })
    }
}

#[derive(Debug)]
pub struct Node {
    pub vis: Visibility,
    pub name: Ident,
    pub params: NodeParams,
    pub ret: Vec<(Ident, Type)>,
    pub body: Vec<Decl>,
}

impl Node {
    fn from_untyped(
        node: PNode,
        node_types: &Map<NodeType>,
        extern_functions: &mut Vec<Ident>,
    ) -> Result<Self, Error> {
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
            vis: node.vis,
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
                .map(|decl| Decl::from_untyped(decl, &context, node_types, extern_functions))
                .collect::<Result<_, _>>()?,
        })
    }
}

trait Singleton {
    fn singleton(&self, span: Span) -> Result<&Type, Error>;
    fn into_singleton(self, span: Span) -> Result<Type, Error>;
}

impl Singleton for Types {
    #[inline]
    fn singleton(&self, span: Span) -> Result<&Type, Error> {
        let [ref r#type] = self[..] else {
            return Err(Error::no_tuples(span, self.clone()));
        };
        Ok(r#type)
    }

    #[inline]
    fn into_singleton(mut self, span: Span) -> Result<Type, Error> {
        if self.len() != 1 {
            return Err(Error::no_tuples(span, self.clone()));
        };
        Ok(self.swap_remove(0))
    }
}

#[derive(Debug)]
pub struct Decl {
    pub vars: Vec<DeclVar>,
    pub expr: Spanned<Expr>,
}

impl Decl {
    fn from_untyped(
        decl: PDecl,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
        extern_functions: &mut Vec<Ident>,
    ) -> Result<Self, Error> {
        let decl_span = decl.expr.span;
        let expr = Expr::from_untyped(
            decl.expr,
            context,
            node_types,
            Some(decl.vars.iter().map(|var| var.ty.clone()).collect()),
            extern_functions,
        )?;

        if expr.types.len() != decl.vars.len() {
            return Err(Error::types_mismatch(
                expr.span,
                expr.types,
                decl.vars.iter().map(|var| var.ty.clone()).collect(),
            ));
        }

        if let Some((_, expected_type, found_type)) = expr
            .types
            .iter()
            .zip(decl.vars.iter())
            .map(|(found_type, var)| (&var.id, &var.ty, found_type))
            .find(|(_, expected_type, found_type)| expected_type != found_type)
        {
            return Err(Error::type_mismatch(
                expr.span,
                expected_type.clone(),
                found_type.clone(),
            ));
        }
        Ok(Self {
            vars: decl.vars,
            expr: Spanned {
                span: decl_span,
                inner: expr,
            },
        })
    }
}

#[derive(Debug)]
pub struct Expr {
    pub types: Types,
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    fn from_untyped(
        expr: Spanned<PExpr>,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
        toplevel_types: Option<Types>,
        extern_functions: &mut Vec<Ident>,
    ) -> Result<Self, Error> {
        Self::do_stuff(
            expr,
            context,
            node_types,
            0,
            toplevel_types,
            extern_functions,
        )
    }

    fn do_stuff(
        spanned_expr: Spanned<PExpr>,
        context: &Map<(Type, Span)>,
        node_types: &Map<NodeType>,
        first_index: u16,
        toplevel_type: Option<Types>,
        extern_functions: &mut Vec<Ident>,
    ) -> Result<Self, Error> {
        let span = spanned_expr.span;
        Ok(match spanned_expr.inner {
            PExpr::Var(var) => {
                let var_name = var.to_string();
                let ty = context
                    .get(var_name)
                    .ok_or_else(|| Error::undef_var(&var))?
                    .0
                    .clone();
                Self {
                    types: types![ty],
                    kind: ExprKind::Var(var),
                    span,
                }
            }
            PExpr::Unit => Self {
                types: types![BaseType::Unit.into()],
                kind: ExprKind::Unit,
                span,
            },
            PExpr::Pre(_, e) => {
                if first_index == 0 {
                    return Err(Error::negative_first_index(span));
                }
                let typed_e = Self::do_stuff(
                    *e,
                    context,
                    node_types,
                    first_index - 1,
                    None,
                    extern_functions,
                )?;
                Self {
                    types: typed_e.types.clone(),
                    kind: ExprKind::Pre(Box::new(typed_e)),
                    span,
                }
            }
            PExpr::Then(head, _, tail) => {
                let head_expr = Self::do_stuff(
                    *head,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let tail_expr = Self::do_stuff(
                    *tail,
                    context,
                    node_types,
                    first_index + 1,
                    None,
                    extern_functions,
                )?;
                if head_expr.types != tail_expr.types {
                    return Err(Error::then_type_mismatch(
                        span,
                        head_expr.types,
                        tail_expr.types,
                    ));
                }

                Self {
                    types: head_expr.types.clone(),
                    kind: ExprKind::Then(Box::new(head_expr), Box::new(tail_expr)),
                    span,
                }
            }
            PExpr::Minus(_, e) => {
                let e_span = e.span;
                let typed_e =
                    Self::do_stuff(*e, context, node_types, first_index, None, extern_functions)?;
                let e_type = typed_e.types.singleton(e_span)?;
                if e_type.base == BaseType::Bool {
                    return Err(Error::bool_arithmetic(span));
                }
                Self {
                    types: typed_e.types.clone(),
                    kind: ExprKind::Minus(Box::new(typed_e)),
                    span,
                }
            }
            PExpr::Not(_, e) => {
                let e_span = e.span;
                let typed_e =
                    Self::do_stuff(*e, context, node_types, first_index, None, extern_functions)?;
                let e_type = typed_e.types.singleton(e_span)?;
                if e_type.base != BaseType::Bool {
                    return Err(Error::number_logic(span));
                }
                Self {
                    types: typed_e.types.clone(),
                    kind: ExprKind::Not(Box::new(typed_e)),
                    span,
                }
            }
            PExpr::MathBinOp(left, op, _, right) => {
                let left_span = left.span;
                let right_span = right.span;
                let typed_left = Self::do_stuff(
                    *left,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let left_type = typed_left.types.singleton(left_span)?;
                let typed_right = Self::do_stuff(
                    *right,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let right_type = typed_right.types.singleton(right_span)?;
                if left_type != right_type {
                    return Err(Error::type_mismatch(
                        span,
                        left_type.clone(),
                        right_type.clone(),
                    ));
                }

                if left_type.base == BaseType::Bool {
                    return Err(Error::bool_arithmetic(span));
                }
                Self {
                    types: typed_left.types.clone(),
                    kind: ExprKind::MathBinOp(Box::new(typed_left), op, Box::new(typed_right)),
                    span,
                }
            }
            PExpr::If(cond, then_branch, else_branch) => {
                let then_branch_span = then_branch.span;
                let typed_then = Self::do_stuff(
                    *then_branch,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let then_type = typed_then.types.singleton(then_branch_span)?;
                let else_branch_span = else_branch.span;
                let typed_else = Self::do_stuff(
                    *else_branch,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let else_type = typed_else.types.singleton(else_branch_span)?;
                let cond_span = cond.span;
                let typed_cond = Self::do_stuff(
                    *cond,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let cond_type = typed_cond.types.singleton(cond_span)?;
                if then_type != else_type {
                    return Err(Error::type_mismatch(
                        span,
                        then_type.clone(),
                        else_type.clone(),
                    ));
                }
                if cond_type.base != BaseType::Bool {
                    return Err(Error::non_bool_cond(span));
                }

                Self {
                    types: typed_then.types.clone(),
                    kind: ExprKind::If(
                        Box::new(typed_cond),
                        Box::new(typed_then),
                        Box::new(typed_else),
                    ),
                    span,
                }
            }
            PExpr::Int(i, _) => Self {
                types: types![BaseType::Int64.into()],
                kind: ExprKind::Int(i),
                span,
            },
            PExpr::Float(f, _) => Self {
                types: types![BaseType::Float64.into()],
                kind: ExprKind::Float(f),
                span,
            },
            PExpr::Bool(b, _) => Self {
                types: types![BaseType::Bool.into()],
                kind: ExprKind::Bool(b),
                span,
            },
            PExpr::FloatCast(casted) => {
                let typed_casted = Self::do_stuff(
                    *casted,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let clocks = match typed_casted.types.singleton(span)? {
                    Type {
                        base: BaseType::Int64,
                        clocks,
                    } => clocks,
                    ty => return Err(Error::float_cast(span, ty.clone())),
                };
                Self {
                    types: types![Type {
                        base: BaseType::Float64,
                        clocks: clocks.clone(),
                    }],
                    kind: ExprKind::FloatCast(Box::new(typed_casted)),
                    span,
                }
            }
            PExpr::When(e, _, clock) => {
                let clock_id = clock.to_string();
                let Some((clock_type, clock_span)) = context.get(&clock_id) else {
                    return Err(Error::undef_var(&clock));
                };
                if clock_type.base != BaseType::Bool {
                    return Err(Error::clock_not_boolean(
                        clock.span(),
                        clock_id,
                        clock_type.base,
                        *clock_span,
                    ));
                }
                let typed_e =
                    Self::do_stuff(*e, context, node_types, first_index, None, extern_functions)?;
                let mut types = typed_e.types.clone();
                for e_type in types.iter_mut() {
                    e_type.clocks.push(ClockType {
                        positive: true,
                        clock: clock.clone(),
                    })
                }
                Self {
                    types,
                    kind: ExprKind::When(Box::new(typed_e), clock),
                    span,
                }
            }
            PExpr::WhenNot(e, _, clock) => {
                let clock_id = clock.to_string();
                let Some((clock_type, clock_span)) = context.get(&clock_id) else {
                    return Err(Error::undef_var(&clock));
                };
                if clock_type.base != BaseType::Bool {
                    return Err(Error::clock_not_boolean(
                        clock.span(),
                        clock_id,
                        clock_type.base,
                        *clock_span,
                    ));
                }
                let typed_e =
                    Self::do_stuff(*e, context, node_types, first_index, None, extern_functions)?;
                let mut types = typed_e.types.clone();
                for e_type in types.iter_mut() {
                    e_type.clocks.push(ClockType {
                        positive: false,
                        clock: clock.clone(),
                    })
                }
                Self {
                    types,
                    kind: ExprKind::WhenNot(Box::new(typed_e), clock),
                    span,
                }
            }
            PExpr::Merge(clock, e_true, e_false) => {
                let clock_id = clock.to_string();
                let e_true_span = e_true.span;
                let typed_e_true = Self::do_stuff(
                    *e_true,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let e_false_span = e_false.span;
                let typed_e_false = Self::do_stuff(
                    *e_false,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let e_true_type = typed_e_true.types.singleton(e_true_span)?;
                let e_false_type = typed_e_false.types.singleton(e_false_span)?;

                if e_true_type.base != e_false_type.base {
                    return Err(Error::type_mismatch(
                        span,
                        e_true_type.clone(),
                        e_false_type.clone(),
                    ));
                }

                let Some((clock_type, _clock_type_span)) = context.get(&clock_id) else {
                    return Err(Error::undef_var(&clock));
                };

                let [true_start @ .., true_last] = &e_true_type.clocks[..] else {
                    return Err(Error::merge_branch_on_base_clock(
                        e_true_span,
                        true,
                        clock_type.clocks.clone(),
                        clock,
                    ));
                };

                let [false_start @ .., false_last] = &e_false_type.clocks[..] else {
                    return Err(Error::merge_branch_on_base_clock(
                        e_false_span,
                        false,
                        clock_type.clocks.clone(),
                        clock,
                    ));
                };

                if true_start != clock_type.clocks {
                    return Err(Error::merge_branch_different_base(
                        e_true_span,
                        true,
                        true_start.to_vec(),
                        clock,
                        clock_type.clocks.clone(),
                    ));
                }

                if false_start != clock_type.clocks {
                    return Err(Error::merge_branch_different_base(
                        e_false_span,
                        false,
                        false_start.to_vec(),
                        clock,
                        clock_type.clocks.clone(),
                    ));
                }

                if !true_last.positive {
                    return Err(Error::merge_branch_wrong_positivity(
                        e_true_span,
                        true,
                        clock_id,
                    ));
                }

                if false_last.positive {
                    return Err(Error::merge_branch_wrong_positivity(
                        e_false_span,
                        false,
                        clock_id,
                    ));
                }

                if true_last.clock.to_string() != clock_id {
                    return Err(Error::merge_branch_wrong_clock(
                        e_true_span,
                        true,
                        clock_id,
                        clock.span(),
                        true_last.clock.to_string(),
                    ));
                }

                if false_last.clock.to_string() != clock_id {
                    return Err(Error::merge_branch_wrong_clock(
                        e_false_span,
                        false,
                        clock_id,
                        clock.span(),
                        false_last.clock.to_string(),
                    ));
                }

                let merge_type = Type {
                    base: e_true_type.base,
                    clocks: clock_type.clocks.clone(),
                };
                let clock = PExpr::Var(clock);
                let clock = Self::do_stuff(
                    Spanned { inner: clock, span },
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )
                .unwrap(); // we check above that this is correct
                Self {
                    types: types![merge_type],
                    kind: ExprKind::If(
                        Box::new(clock),
                        Box::new(typed_e_true),
                        Box::new(typed_e_false),
                    ),
                    span,
                }
            }
            PExpr::FunCall(f, args, spawn) => {
                let first_index = if spawn {
                    if first_index == 0 {
                        return Err(Error::negative_first_index(span));
                    } else {
                        first_index - 1
                    }
                } else {
                    first_index
                };
                let f_symb = f.to_string();
                let typed_args = args
                    .into_iter()
                    .map(|arg| {
                        Ok({
                            let arg_span = arg.span;
                            (
                                Self::do_stuff(
                                    arg,
                                    context,
                                    node_types,
                                    first_index,
                                    None,
                                    extern_functions,
                                )?,
                                arg_span,
                            )
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let (ty, extern_symbol) = if let Some(node_type) = node_types.get(&f_symb) {
                    if typed_args.len() != node_type.arg_types.len() {
                        return Err(Error::wrong_number_of_arguments(
                            span,
                            f_symb,
                            node_type.arg_types.len(),
                            typed_args.len(),
                        ));
                    }

                    if let Some(((expr, expr_span), typ)) = typed_args
                        .iter()
                        .zip(node_type.arg_types.iter())
                        .find(|&((found_expr, _), expected_type)| {
                            found_expr.types.len() != 1 || found_expr.types[0] != *expected_type
                        })
                    {
                        let expr_type = expr.types.singleton(*expr_span)?;
                        return Err(Error::argument_type_mismatch(
                            *expr_span,
                            typ.clone(),
                            expr_type.clone(),
                        ));
                    }

                    (node_type.ret_types.clone(), false)
                } else if let Some(ty) = toplevel_type {
                    (ty, true)
                } else {
                    return Err(Error::external_symbol_not_toplevel(f.span(), f_symb));
                };

                if extern_symbol {
                    extern_functions.push(f.clone());
                }

                if extern_symbol && spawn {
                    return Err(Error::spawn_extern_func(f.span(), f_symb));
                }

                Self {
                    types: ty,
                    kind: ExprKind::FunCall {
                        function: f,
                        arguments: typed_args.into_iter().map(|(x, _)| x).collect(),
                        extern_symbol,
                        spawn,
                    },
                    span,
                }
            }
            PExpr::BoolBinOp(left, op, _op_span, right) => {
                let left_span = left.span;
                let right_span = right.span;
                let typed_left = Self::do_stuff(
                    *left,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let typed_right = Self::do_stuff(
                    *right,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let left_type = typed_left.types.singleton(left_span)?;
                let right_type = typed_right.types.singleton(right_span)?;

                if left_type.base != BaseType::Bool {
                    return Err(Error::number_logic(left_span))?;
                }

                if right_type.base != BaseType::Bool {
                    return Err(Error::number_logic(right_span))?;
                }

                if left_type.clocks != right_type.clocks {
                    return Err(Error::type_mismatch(
                        span,
                        left_type.clone(),
                        right_type.clone(),
                    ));
                }

                Self {
                    types: types![left_type.clone()],
                    kind: ExprKind::BoolBinOp(Box::new(typed_left), op, Box::new(typed_right)),
                    span,
                }
            }
            PExpr::CompOp(left, op, _op_span, right) => {
                let generic_op = matches!(op, CompOp::Eq | CompOp::NEq);
                let left_span = left.span;
                let right_span = right.span;
                let typed_left = Self::do_stuff(
                    *left,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let typed_right = Self::do_stuff(
                    *right,
                    context,
                    node_types,
                    first_index,
                    None,
                    extern_functions,
                )?;
                let left_type = typed_left.types.singleton(left_span)?;
                let right_type = typed_right.types.singleton(right_span)?;

                if left_type != right_type {
                    return Err(Error::type_mismatch(
                        span,
                        left_type.clone(),
                        right_type.clone(),
                    ));
                }

                if !generic_op && matches!(left_type.base, BaseType::Bool | BaseType::Unit) {
                    return Err(Error::bool_arithmetic(span));
                }

                Self {
                    types: types![Type {
                        base: BaseType::Bool,
                        clocks: left_type.clocks.clone(),
                    }],
                    kind: ExprKind::CompOp(Box::new(typed_left), op, Box::new(typed_right)),
                    span,
                }
            }
        })
    }
}

#[derive(Debug)]
pub enum ExprKind {
    Var(Ident),
    Unit,
    Pre(Box<Expr>),
    Then(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>),
    Not(Box<Expr>),
    MathBinOp(Box<Expr>, MathBinOp, Box<Expr>),
    BoolBinOp(Box<Expr>, BoolBinOp, Box<Expr>),
    CompOp(Box<Expr>, CompOp, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Int(i64),
    Float(f64),
    Bool(bool),
    FloatCast(Box<Expr>),
    When(Box<Expr>, Ident),
    WhenNot(Box<Expr>, Ident),
    /// a spawned funcall cannot be extern
    FunCall {
        extern_symbol: bool,
        spawn: bool,
        function: Ident,
        arguments: Vec<Expr>,
    },
}

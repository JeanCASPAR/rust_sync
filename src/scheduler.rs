use std::fmt::format;

use patricia_tree::StringPatriciaMap;
use syn::Ident;

use crate::{
    parser::{MathBinOp, Type},
    typing::{Expr as TExpr, ExprKind as TExprKind, Node as TNode},
};

pub type SIdent = (usize, usize);

pub struct Ast {
    nodes: Vec<Node>,
}

pub struct Node {
    pub name: Ident,
    pub params: Vec<Type>,
    pub ret: Vec<(SIdent, Type)>,
    pub equations: Vec<(Vec<Type>, EqType)>,
    pub deps: Vec<Vec<usize>>,
    pub order: Vec<usize>,
}

pub enum EqType {
    Input,
    NodeCall,
    Expr(Expr),
}

pub struct Expr {
    ty: Type,
    kind: ExprKind,
}

pub enum ExprKind {
    Var(SIdent),
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
    When(Box<Expr>, SIdent),
    WhenNot(Box<Expr>, SIdent),
    Merge(SIdent, Box<Expr>, Box<Expr>),
    FunCall {
        function: Ident,
        arguments: Vec<Expr>,
    },
}

struct Context {
    equations: Vec<(Vec<Type>, EqType)>,
    /// n € deps[m] if the equation m depends on the equation n
    deps: Vec<Vec<usize>>,
    /// we replace all idents by a pair whose first element is the number
    /// of the equation introducing it (0 if it is an input) and whose
    /// second element is the number of the ident in the declaration
    store: StringPatriciaMap<SIdent>,
}

impl Context {
    fn new() -> Self {
        Context {
            equations: Vec::new(),
            deps: Vec::new(),
            store: StringPatriciaMap::new(),
        }
    }

    fn schedule_eq(&mut self, node: TNode) {
        self.equations.push((Vec::new(), EqType::Input));
        self.deps.push(Vec::new());
        for (i, param) in node.params.0.iter().enumerate() {
            self.equations[0].0.push(param.ty.clone());
            self.store.insert(param.id.to_string(), (0, i));
        }

        for decl in node.body.iter() {
            let i = self.deps.len();
            self.deps.push(Vec::new());
            // dummy EqType::Input here because we cannot yet translate the expression
            self.equations.push((Vec::new(), EqType::Input));
            for (j, decl) in [decl].iter().enumerate() {
                self.equations.last_mut().unwrap().0.push(decl.ty.clone());
                self.store.insert(decl.id.to_string(), (i, j));
            }
        }

        for (i, decl) in node.body.into_iter().enumerate() {
            let i = i + 1;
            match decl.expr.kind {
                // TODO: separate node call from other expressions
                _ => (),
            };
            let e = self.normalize_expr(decl.expr, i, true);
            self.equations[i].1 = EqType::Expr(e);
        }
    }

    fn normalize_expr(&mut self, e: TExpr, eq: usize, depends: bool) -> Expr {
        let mut add_dep = |i: usize| {
            if depends && i != eq && !self.deps[eq].contains(&i) {
                self.deps[eq].push(i);
            }
        };
        let ty = e.ty;
        let kind = match e.kind {
            TExprKind::Var(id) => {
                let (i, j) = self.store.get(id.to_string()).unwrap().clone();
                //self.deps[eq].push(i);
                add_dep(i);
                ExprKind::Var((i, j))
            }
            TExprKind::Unit => ExprKind::Unit,
            TExprKind::Pre(e) => {
                let s = format!("#{}", self.equations.len());
                let i = self.equations.len();
                let ty = e.ty.clone();
                self.store.insert(s.clone(), (i, 0));
                self.deps.push(Vec::new());

                self.equations.push((vec![ty.clone()], EqType::Input));
                let e = self.normalize_expr(*e, i, true);
                self.equations[i].1 = EqType::Expr(e);

                //TODO: cell for pre
                ExprKind::Pre(Box::new(Expr {
                    ty,
                    kind: ExprKind::Var((i, 0)),
                }))
            }
            TExprKind::Then(_, _) => todo!(),
            TExprKind::Minus(e) => {
                let e = self.normalize_expr(*e, eq, depends);
                ExprKind::Minus(Box::new(e))
            }
            TExprKind::Not(e) => {
                let e = self.normalize_expr(*e, eq, depends);
                ExprKind::Not(Box::new(e))
            }
            TExprKind::BinOp(e1, op, e2) => {
                let e1 = self.normalize_expr(*e1, eq, depends);
                let e2 = self.normalize_expr(*e2, eq, depends);

                ExprKind::BinOp(Box::new(e1), op, Box::new(e2))
            }
            TExprKind::If(b, e_then, e_else) => {
                let b = self.normalize_expr(*b, eq, depends);
                let e_then = self.normalize_expr(*e_then, eq, depends);
                let e_else = self.normalize_expr(*e_else, eq, depends);

                ExprKind::If(Box::new(b), Box::new(e_then), Box::new(e_else))
            }
            TExprKind::Int(n) => ExprKind::Int(n),
            TExprKind::Float(x) => ExprKind::Float(x),
            TExprKind::Bool(b) => ExprKind::Bool(b),
            TExprKind::FloatCast(e) => {
                let e = self.normalize_expr(*e, eq, depends);

                ExprKind::FloatCast(Box::new(e))
            }
            TExprKind::When(e, id) => {
                let e = self.normalize_expr(*e, eq, depends);
                let id = self.store.get(id.to_string()).unwrap().clone();

                ExprKind::When(Box::new(e), id)
            }
            TExprKind::WhenNot(e, id) => {
                let e = self.normalize_expr(*e, eq, depends);
                let id = self.store.get(id.to_string()).unwrap().clone();

                ExprKind::WhenNot(Box::new(e), id)
            }
            TExprKind::Merge(id, e_when, e_whennot) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                let e_when = self.normalize_expr(*e_when, eq, depends);
                let e_whennot = self.normalize_expr(*e_whennot, eq, depends);

                ExprKind::Merge(id, Box::new(e_when), Box::new(e_whennot))
            }
            TExprKind::FunCall {
                function,
                arguments,
            } => todo!(),
        };
        Expr { ty, kind }
    }
}

impl From<TNode> for Node {
    fn from(node: TNode) -> Self {
        let name = node.name.clone();
        let ret = node.ret.clone();

        let mut context = Context::new();
        context.schedule_eq(node);

        let params = context.equations[0].0.clone();

        let ret = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .collect();

        let order = todo!("topological order on deps");

        Node {
            name,
            params,
            ret,
            equations: context.equations,
            deps: context.deps,
            order,
        }
    }
}

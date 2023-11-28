use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use smallvec::SmallVec;
use syn::Ident;

use crate::{
    error::Error,
    parser::{MathBinOp, Type, Types},
    typing::{Expr as TExpr, ExprKind as TExprKind, Node as TNode},
};

pub type SIdent = (usize, usize);

pub struct Ast {
    nodes: Vec<Node>,
}

pub struct Node {
    pub name: Ident,
    pub params: Types,
    pub ret: Vec<(SIdent, Type)>,
    pub equations: Vec<(Types, EqType)>,
    pub deps: Vec<Vec<usize>>,
    pub order: Vec<usize>,
}

pub enum EqType {
    Input,
    NodeCall,
    Expr(Expr),
}

pub struct Expr {
    ty: Types,
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
    equations: Vec<(Types, EqType)>,
    /// n € deps[m] if the equation m depends on the equation n
    deps: Vec<Vec<usize>>,
    /// we replace all idents by a pair whose first element is the number
    /// of the equation introducing it (0 if it is an input) and whose
    /// second element is the number of the ident in the declaration
    store: StringPatriciaMap<SIdent>,
    order: Vec<usize>,
}

impl Context {
    fn new() -> Self {
        Context {
            equations: Vec::new(),
            deps: Vec::new(),
            store: StringPatriciaMap::new(),
            order: Vec::new(),
        }
    }

    fn schedule_eq(&mut self, node: TNode) -> Result<(), Error> {
        self.equations.push((SmallVec::new(), EqType::Input));
        self.deps.push(Vec::new());
        for (i, param) in node.params.0.iter().enumerate() {
            self.equations[0].0.push(param.ty.clone());
            self.store.insert(param.id.to_string(), (0, i));
        }

        for decl in node.body.iter() {
            let i = self.deps.len();
            self.deps.push(Vec::new());
            // dummy EqType::Input here because we cannot yet translate the expression
            self.equations
                .push((decl.expr.inner.types.clone(), EqType::Input));

            for (j, var) in decl.vars.iter().enumerate() {
                self.store.insert(var.id.to_string(), (i, j));
            }
        }

        for (i, decl) in node.body.into_iter().enumerate() {
            let i = i + 1;
            match decl.expr.inner.kind {
                // TODO: separate node call from other expressions
                _ => (),
            };
            let e = self.normalize_expr(decl.expr.inner, i, true);
            self.equations[i].1 = EqType::Expr(e);
        }

        self.topo_sort()?;

        Ok(())
    }

    fn normalize_expr(&mut self, e: TExpr, eq: usize, depends: bool) -> Expr {
        let mut add_dep = |i: usize| {
            if depends && i != eq && !self.deps[eq].contains(&i) {
                self.deps[eq].push(i);
            }
        };
        let ty = e.types;
        let kind = match e.kind {
            TExprKind::Var(id) => {
                let (i, j) = self.store.get(id.to_string()).unwrap().clone();
                add_dep(i);
                ExprKind::Var((i, j))
            }
            TExprKind::Unit => ExprKind::Unit,
            TExprKind::Pre(e) => {
                let s = format!("#{}", self.equations.len());
                let i = self.equations.len();
                let ty = ty.clone();
                self.store.insert(s.clone(), (i, 0));
                self.deps.push(Vec::new());

                self.equations.push((ty.clone(), EqType::Input));
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
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.0);
                let e = self.normalize_expr(*e, eq, depends);

                ExprKind::When(Box::new(e), id)
            }
            TExprKind::WhenNot(e, id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.0);
                let e = self.normalize_expr(*e, eq, depends);

                ExprKind::WhenNot(Box::new(e), id)
            }
            TExprKind::Merge(id, e_when, e_whennot) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.0);
                let e_when = self.normalize_expr(*e_when, eq, depends);
                let e_whennot = self.normalize_expr(*e_whennot, eq, depends);

                ExprKind::Merge(id, Box::new(e_when), Box::new(e_whennot))
            }
            TExprKind::FunCall {
                extern_symbol,
                function,
                arguments,
            } => todo!(),
        };
        Expr { ty, kind }
    }

    fn topo_sort(&mut self) -> Result<(), Error> {
        // 0 = not visited, 1 = visiting, 2 = visited
        let mut visited = vec![0u8; self.deps.len()];

        for i in 0..self.deps.len() {
            self.visit(i, &mut visited)?;
        }

        Ok(())
    }

    fn visit(&mut self, idx: usize, visited: &mut [u8]) -> Result<(), Error> {
        if visited[idx] == 1 {
            // TODO: real span
            return Err(Error::cyclic_equation(Span::call_site()));
        } else if visited[idx] == 2 {
            return Ok(());
        }
        self.order.push(idx);

        visited[idx] = 1;
        for j in 0..self.deps[idx].len() {
            self.visit(self.deps[idx][j], visited)?;
        }
        visited[idx] = 2;

        Ok(())
    }
}

impl TryFrom<TNode> for Node {
    type Error = Error;

    fn try_from(node: TNode) -> Result<Self, Error> {
        let name = node.name.clone();
        let ret = node.ret.clone();

        let mut context = Context::new();
        context.schedule_eq(node)?;

        let params = context.equations[0].0.clone();

        let ret = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .collect();

        let order = context.order;

        Ok(Node {
            name,
            params,
            ret,
            equations: context.equations,
            deps: context.deps,
            order,
        })
    }
}

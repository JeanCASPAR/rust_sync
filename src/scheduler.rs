use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use syn::Ident;

use crate::{
    error::Error,
    parser::{MathBinOp, Types},
    typing::{Expr as TExpr, ExprKind as TExprKind, Node as TNode},
};

pub type SIdent = (usize, usize);

pub struct Ast {
    nodes: Vec<Node>,
}

pub struct Node {
    pub name: Ident,
    pub params: Types,
    pub ret_vars: Vec<SIdent>,
    pub ret_type: Types,
    pub equations: Vec<Equation>,
    pub deps: Vec<Vec<usize>>,
    pub order: Vec<usize>,
}

pub enum EqKind {
    Input,
    NodeCall {
        ident: Ident,
        args: Vec<Expr>,
        cell: usize,
    },
    Expr(Expr),
    /// expression that is saved in a memory cell
    CellExpr(Expr, usize),
}

pub struct Expr {
    ty: Types,
    kind: ExprKind,
}

pub enum ExprKind {
    Var(SIdent),
    Unit,
    // cell number
    Pre(usize),
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
    Tuple(Vec<SIdent>),
}

pub struct Equation {
    pub types: Types,
    pub kind: EqKind,
}

impl Equation {
    pub fn new(types: Types, kind: EqKind) -> Self {
        Self { types, kind }
    }
}

struct Context {
    equations: Vec<(Equation, Option<Span>)>,
    /// n € deps[m] if the equation m depends on the equation n
    deps: Vec<Vec<usize>>,
    /// we replace all idents by a pair whose first element is the number
    /// of the equation introducing it (0 if it is an input) and whose
    /// second element is the number of the ident in the declaration
    store: StringPatriciaMap<SIdent>,
    order: Vec<usize>,
    cells: usize,
}

impl Context {
    fn new() -> Self {
        Context {
            equations: Vec::new(),
            deps: Vec::new(),
            store: StringPatriciaMap::new(),
            order: Vec::new(),
            cells: 0,
        }
    }

    fn schedule_eq(&mut self, node: TNode) -> Result<(), Error> {
        self.equations
            .push((Equation::new(Types::new(), EqKind::Input), None));
        self.deps.push(Vec::new());
        for (i, param) in node.params.0.iter().enumerate() {
            self.equations[0].0.types.push(param.ty.clone());
            self.store.insert(param.id.to_string(), (0, i));
        }

        for decl in node.body.iter() {
            let i = self.deps.len();
            self.deps.push(Vec::new());
            // dummy EqKind::Input here because we cannot yet translate the expression
            self.equations.push((
                Equation::new(decl.expr.inner.types.clone(), EqKind::Input),
                Some(decl.expr.span),
            ));

            for (j, var) in decl.vars.iter().enumerate() {
                self.store.insert(var.id.to_string(), (i, j));
            }
        }

        for (i, decl) in node.body.into_iter().enumerate() {
            let i = i + 1;
            let e = self.normalize_expr(decl.expr.inner, i, true);
            self.equations[i].0.kind = EqKind::Expr(e);
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
                if ty.len() <= 1 {
                    todo!("pre with tuple unimplemented yet")
                }
                self.store.insert(s.clone(), (i, 0));
                self.deps.push(Vec::new());

                self.equations
                    .push((Equation::new(ty.clone(), EqKind::Input), Some(e.span)));
                let cell = self.cells;
                self.cells += 1;
                let e = self.normalize_expr(*e, i, true);
                self.equations[i].0.kind = EqKind::CellExpr(e, cell);

                ExprKind::Pre(cell)
            }
            TExprKind::Then(e1, e2) => {
                let e1 = self.normalize_expr(*e1, eq, depends);
                let e2 = self.normalize_expr(*e2, eq, depends);
                ExprKind::Then(Box::new(e1), Box::new(e2))
            }
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
            } => {
                if extern_symbol {
                    let mut args = Vec::with_capacity(arguments.len());
                    for arg in arguments {
                        args.push(self.normalize_expr(arg, eq, depends));
                    }
                    ExprKind::FunCall {
                        function,
                        arguments: args,
                    }
                } else {
                    let s = format!("#{}", self.equations.len());
                    let i = self.equations.len();
                    let ty = ty.clone();
                    for j in 0..ty.len() {
                        self.store.insert(s.clone(), (i, j));
                    }
                    add_dep(i);

                    let cell = self.cells;
                    self.cells += 1;

                    self.deps.push(Vec::new());
                    // dumme EqKind::Input
                    self.equations
                        .push((Equation::new(ty.clone(), EqKind::Input), None));

                    let mut args = Vec::with_capacity(arguments.len());
                    for expr in arguments {
                        let e = self.normalize_expr(expr, eq, depends);
                        args.push(e);
                    }

                    self.equations[i].0.kind = EqKind::NodeCall {
                        ident: function,
                        args,
                        cell,
                    };

                    ExprKind::Tuple((0..ty.len()).into_iter().map(|j| (i, j)).collect())
                }
            }
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
            return Err(Error::cyclic_equation(self.equations[idx].1.unwrap()));
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

        let params = context.equations[0].0.types.clone();

        let (ret_vars, ret_type) = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .unzip();

        let order = context.order;
        let equations = context.equations.into_iter().map(|eq| eq.0).collect();

        Ok(Node {
            name,
            params,
            ret_vars,
            ret_type,
            equations,
            deps: context.deps,
            order,
        })
    }
}

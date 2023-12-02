use std::mem::MaybeUninit;

use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use syn::Ident;

use crate::{
    error::Error,
    parser::{BaseType, MathBinOp, Types},
    typing::{Ast as TAst, Expr as TExpr, ExprKind as TExprKind, Node as TNode},
};

#[derive(Debug, Clone, Copy)]
pub struct SIdent(pub usize, pub usize);

#[derive(Debug)]
pub struct Ast {
    pub nodes: Vec<Node>,
}

impl Ast {
    /// boolean : true if currently being visited
    fn visit(
        s: String,
        parent: Option<String>,
        dfs: &mut StringPatriciaMap<(bool, Option<String>)>,
        node_deps: &StringPatriciaMap<Vec<Ident>>,
        node_idents: &StringPatriciaMap<Ident>,
    ) -> Result<(), Error> {
        match dfs.get(&s) {
            Some((true, _)) => {
                let mut cycle = vec![s.clone()];
                let mut current = parent.clone().unwrap();
                loop {
                    cycle.push(current.clone());
                    current = match dfs.get(&current).unwrap().clone().1 {
                        Some(id) => id.to_string(),
                        None => {
                            cycle.pop();
                            break;
                        }
                    };
                    if &current == &s {
                        break;
                    }
                }

                let cycle = cycle
                    .into_iter()
                    .map(|s| node_idents.get(s).unwrap())
                    .cloned()
                    .collect::<Vec<_>>();

                return Err(Error::cyclic_node(cycle.last().unwrap().span(), cycle));
            }
            Some((false, _)) => return Ok(()),
            None => {
                dfs.insert(s.clone(), (true, parent));
                for n in node_deps.get(&s).unwrap() {
                    Self::visit(n.to_string(), Some(s.clone()), dfs, node_deps, node_idents)?;
                }
                dfs.get_mut(&s).unwrap().0 = false;
            }
        }

        Ok(())
    }

    fn assert_no_node_cycle(
        node_deps: StringPatriciaMap<Vec<Ident>>,
        node_idents: StringPatriciaMap<Ident>,
    ) -> Result<(), Error> {
        let mut dfs = StringPatriciaMap::new();

        for s in node_deps.keys() {
            Self::visit(s, None, &mut dfs, &node_deps, &node_idents)?;
        }

        Ok(())
    }
}

impl TryFrom<TAst> for Ast {
    type Error = Error;
    fn try_from(ast: TAst) -> Result<Self, Self::Error> {
        let mut node_deps = StringPatriciaMap::new();

        let nodes = ast
            .nodes
            .into_iter()
            .map(|node| Node::schedule(node, &mut node_deps))
            .collect::<Result<Vec<Node>, _>>()?;

        let mut node_idents = StringPatriciaMap::new();
        for node in nodes.iter() {
            node_idents.insert(node.name.to_string(), node.name.clone());
        }

        Self::assert_no_node_cycle(node_deps, node_idents)?;

        Ok(Ast { nodes })
    }
}

#[derive(Debug)]
pub struct Node {
    pub name: Ident,
    pub params: Types,
    pub ret_vars: Vec<SIdent>,
    pub ret_type: Types,
    pub equations: Vec<Equation>,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct Expr {
    pub ty: Types,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
    Var(SIdent),
    Unit,
    /// cell number
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
    FunCall {
        function: Ident,
        arguments: Vec<Expr>,
    },
    Tuple(Vec<SIdent>),
}

#[derive(Debug)]
pub struct Equation {
    pub types: Types,
    pub kind: EqKind,
}

impl Equation {
    pub fn new(types: Types, kind: EqKind) -> Self {
        Self { types, kind }
    }
}

#[derive(Debug)]
struct Context {
    equations: Vec<(Equation, Option<Span>)>,
    /// n in deps[m] if the equation m depends on the equation n
    deps: Vec<Vec<usize>>,
    /// we replace all idents by a pair whose first element is the number
    /// of the equation introducing it (0 if it is an input) and whose
    /// second element is the number of the ident in the declaration
    store: StringPatriciaMap<SIdent>,
    order: Vec<usize>,
    cells: usize,
    /// names of nodes that are instanciated in this node
    node_deps: Vec<Ident>,
}

impl Context {
    fn new() -> Self {
        Context {
            equations: Vec::new(),
            deps: Vec::new(),
            store: StringPatriciaMap::new(),
            order: Vec::new(),
            cells: 0,
            node_deps: Vec::new(),
        }
    }

    fn schedule_eq(&mut self, node: TNode) -> Result<(), Error> {
        self.equations
            .push((Equation::new(Types::new(), EqKind::Input), None));
        self.deps.push(Vec::new());
        for (i, param) in node.params.0.iter().enumerate() {
            self.equations[0].0.types.push(param.ty.clone());
            self.store.insert(param.id.to_string(), SIdent(0, i));
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
                self.store.insert(var.id.to_string(), SIdent(i, j));
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
            if depends && !self.deps[eq].contains(&i) {
                self.deps[eq].push(i);
            }
        };
        let ty = e.types;
        let kind = match e.kind {
            TExprKind::Var(id) => {
                let SIdent(i, j) = self.store.get(id.to_string()).unwrap().clone();
                add_dep(i);
                ExprKind::Var(SIdent(i, j))
            }
            TExprKind::Unit => ExprKind::Unit,
            TExprKind::Pre(e) => {
                let s = format!("#{}", self.equations.len());
                let i = self.equations.len();
                let ty = ty.clone();
                if ty.len() > 1 {
                    todo!("pre with tuple unimplemented yet")
                }
                self.store.insert(s.clone(), SIdent(i, 0));
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
                self.normalize_expr(*e, eq, depends).kind
            }
            TExprKind::WhenNot(e, id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.0);
                self.normalize_expr(*e, eq, depends).kind
            }
            TExprKind::Merge(id, e_when, e_whennot) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.0);
                let e_when = self.normalize_expr(*e_when, eq, depends);
                let e_whennot = self.normalize_expr(*e_whennot, eq, depends);

                ExprKind::If(
                    Box::new(Expr {
                        kind: ExprKind::Var(id),
                        ty: Types::from_elem(BaseType::Bool.into(), 1),
                    }),
                    Box::new(e_when),
                    Box::new(e_whennot),
                )
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
                    self.node_deps.push(function.clone());

                    let s = format!("#{}", self.equations.len());
                    let i = self.equations.len();
                    let ty = ty.clone();
                    for j in 0..ty.len() {
                        self.store.insert(s.clone(), SIdent(i, j));
                    }
                    add_dep(i);

                    let cell = self.cells;
                    self.cells += 1;

                    self.deps.push(Vec::new());
                    // dummy EqKind::Input
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

                    ExprKind::Tuple((0..ty.len()).into_iter().map(|j| SIdent(i, j)).collect())
                }
            }
        };
        Expr { ty, kind }
    }

    fn topo_sort(&mut self) -> Result<(), Error> {
        // 0 = not visited, 1 = visiting, 2 = visited
        // Option<usize> : idx of the parent in the DFS
        let mut visited = vec![(0u8, None); self.deps.len()];

        for i in 0..self.deps.len() {
            self.visit(i, None, &mut visited)?;
        }

        Ok(())
    }

    fn visit(
        &mut self,
        idx: usize,
        parent: Option<usize>,
        visited: &mut [(u8, Option<usize>)],
    ) -> Result<(), Error> {
        if visited[idx].0 == 1 {
            let mut cycle = vec![self.equations[idx].1.unwrap()];
            let mut current = parent.unwrap();
            loop {
                cycle.push(self.equations[current].1.unwrap());
                current = match visited[current].1 {
                    Some(curr) => curr,
                    None => {
                        // the first and last equations are the same but no other equations
                        // depend on this one
                        cycle.pop();
                        break;
                    }
                };

                if current == idx {
                    break;
                }
            }
            return Err(Error::cyclic_equation(
                self.equations[idx].1.unwrap(),
                cycle,
            ));
        } else if visited[idx].0 == 2 {
            return Ok(());
        }
        self.order.push(idx);

        visited[idx] = (1, parent);
        for j in 0..self.deps[idx].len() {
            self.visit(self.deps[idx][j], Some(idx), visited)?;
        }
        visited[idx].0 = 2;

        Ok(())
    }
}

fn permut(v: &mut Vec<Equation>, permutations: Vec<usize>) {
    assert_eq!(v.len(), permutations.len());

    let mut src = std::mem::replace(v, Vec::with_capacity(v.len()));

    unsafe {
        src.set_len(0);
    }

    let slice = v.spare_capacity_mut();
    let n = permutations.len();

    for (i, j) in permutations.into_iter().enumerate() {
        slice[j].write(unsafe { src.as_ptr().add(i).read() });
    }

    unsafe {
        v.set_len(n);
    }
}

impl Node {
    fn schedule(node: TNode, node_deps: &mut StringPatriciaMap<Vec<Ident>>) -> Result<Self, Error> {
        let name = node.name.clone();
        let ret = node.ret.clone();

        let mut context = Context::new();
        context.schedule_eq(node)?;
        node_deps.insert(name.to_string(), context.node_deps);

        let params = context.equations[0].0.types.clone();

        let (ret_vars, ret_type) = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .unzip();

        let mut equations = context.equations.into_iter().map(|eq| eq.0).collect();
        permut(&mut equations, context.order);

        Ok(Node {
            name,
            params,
            ret_vars,
            ret_type,
            equations,
        })
    }
}

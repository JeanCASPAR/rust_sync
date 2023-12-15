use patricia_tree::StringPatriciaMap;
use proc_macro2::Span;
use smallvec::SmallVec;
use syn::{Ident, Visibility};

use crate::{
    error::Error,
    parser::{BaseType, BoolBinOp, ClockType as PClockType, CompOp, MathBinOp, Types as PTypes},
    typing::{Ast as TAst, Expr as TExpr, ExprKind as TExprKind, Node as TNode},
};

#[derive(Debug, Clone, Copy)]
pub struct SIdent {
    pub eq: usize,
    pub idx: usize,
    pub wait: bool,
}

impl SIdent {
    pub fn new(eq: usize, idx: usize, wait: bool) -> Self {
        Self { eq, idx, wait }
    }
}

#[derive(Debug, Clone)]
pub struct ClockType {
    pub positive: bool,
    pub clock: SIdent,
}

impl ClockType {
    fn from(clock: PClockType, store: &mut StringPatriciaMap<SIdent>) -> Self {
        Self {
            positive: clock.positive,
            clock: store.get(clock.clock.to_string()).unwrap().clone(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Types {
    pub inner: SmallVec<[BaseType; 1]>,
    pub clocks: Vec<ClockType>,
}

impl Types {
    fn from(types: PTypes, store: &mut StringPatriciaMap<SIdent>) -> Self {
        let mut inner = SmallVec::with_capacity(types.len());
        let mut clocks = Vec::new();
        for ty in types {
            inner.push(ty.base);
            if !clocks.is_empty() {
                // we suppose that all types have the same clocks in a tuple
                // TODO: change when clocks are supported by types at typing
                clocks.extend(
                    ty.clocks
                        .into_iter()
                        .map(|clock| ClockType::from(clock, store)),
                );
            }
        }

        Self { inner, clocks }
    }

    fn permut(&mut self, permutations: &mut [usize]) {
        for clock in &mut self.clocks {
            clock.clock.idx = permutations[clock.clock.idx];
        }
    }
}

impl Types {
    pub fn new() -> Self {
        Self {
            inner: SmallVec::new(),
            clocks: Vec::new(),
        }
    }
}

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
    pub vis: Visibility,
    pub name: Ident,
    pub params: Types,
    pub ret_vars: Vec<SIdent>,
    pub ret_types: Types,
    pub equations: Vec<Equation>,
}

#[derive(Debug)]
pub enum EqKind {
    Input,
    NodeCall {
        ident: Ident,
        args: Vec<Expr>,
        cell: usize,
        spawn: bool,
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
    MathBinOp(Box<Expr>, MathBinOp, Box<Expr>),
    BoolBinOp(Box<Expr>, BoolBinOp, Box<Expr>),
    CompOp(Box<Expr>, CompOp, Box<Expr>),
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

impl Expr {
    fn permut(&mut self, permutations: &mut [usize]) {
        self.ty.permut(permutations);
        match &mut self.kind {
            ExprKind::Var(id) => id.eq = permutations[id.eq],
            ExprKind::Then(e1, e2) => {
                e1.permut(permutations);
                e2.permut(permutations);
            }
            ExprKind::Minus(e) => e.permut(permutations),
            ExprKind::Not(e) => e.permut(permutations),
            ExprKind::MathBinOp(e1, _, e2) => {
                e1.permut(permutations);
                e2.permut(permutations);
            }
            ExprKind::BoolBinOp(e1, _, e2) => {
                e1.permut(permutations);
                e2.permut(permutations);
            }
            ExprKind::CompOp(e1, _, e2) => {
                e1.permut(permutations);
                e2.permut(permutations);
            }
            ExprKind::If(cond, e_then, e_else) => {
                cond.permut(permutations);
                e_then.permut(permutations);
                e_else.permut(permutations);
            }
            ExprKind::Unit
            | ExprKind::Pre(_)
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Bool(_) => (),
            ExprKind::FloatCast(e) => e.permut(permutations),
            ExprKind::FunCall { arguments, .. } => {
                for arg in arguments {
                    arg.permut(permutations);
                }
            }
            ExprKind::Tuple(tuple) => {
                for id in tuple {
                    id.eq = permutations[id.eq];
                }
            }
        }
    }
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
            // we suppose that input types do not have a clock
            self.equations[0].0.types.inner.push(param.ty.base.clone());
            self.store
                .insert(param.id.to_string(), SIdent::new(0, i, false));
        }

        for decl in node.body.iter() {
            let i = self.deps.len();
            self.deps.push(Vec::new());
            // dummy EqKind::Input here because we cannot yet translate the expression
            self.equations.push((
                Equation::new(
                    Types::from(decl.expr.inner.types.clone(), &mut self.store),
                    EqKind::Input,
                ),
                Some(decl.expr.span),
            ));

            for (j, var) in decl.vars.iter().enumerate() {
                self.store
                    .insert(var.id.to_string(), SIdent::new(i, j, false));
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
        let ty = Types::from(e.types, &mut self.store);
        let kind = match e.kind {
            TExprKind::Var(id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);
                ExprKind::Var(id)
            }
            TExprKind::Unit => ExprKind::Unit,
            TExprKind::Pre(e) => {
                let i = self.equations.len();
                let s = format!("#{}", i);
                let ty = ty.clone();
                if ty.inner.len() > 1 {
                    todo!("pre with tuple unimplemented yet")
                }

                self.store.insert(s.clone(), SIdent::new(i, 0, false));
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
            TExprKind::MathBinOp(e1, op, e2) => {
                let e1 = self.normalize_expr(*e1, eq, depends);
                let e2 = self.normalize_expr(*e2, eq, depends);

                ExprKind::MathBinOp(Box::new(e1), op, Box::new(e2))
            }
            TExprKind::BoolBinOp(e1, op, e2) => {
                let e1 = self.normalize_expr(*e1, eq, depends);
                let e2 = self.normalize_expr(*e2, eq, depends);

                ExprKind::BoolBinOp(Box::new(e1), op, Box::new(e2))
            }
            TExprKind::CompOp(e1, op, e2) => {
                let e1 = self.normalize_expr(*e1, eq, depends);
                let e2 = self.normalize_expr(*e2, eq, depends);

                ExprKind::CompOp(Box::new(e1), op, Box::new(e2))
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
                add_dep(id.eq);
                self.normalize_expr(*e, eq, depends).kind
            }
            TExprKind::WhenNot(e, id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);
                self.normalize_expr(*e, eq, depends).kind
            }
            TExprKind::Merge(id, e_when, e_whennot) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);
                let e_when = self.normalize_expr(*e_when, eq, depends);
                let e_whennot = self.normalize_expr(*e_whennot, eq, depends);

                ExprKind::If(
                    Box::new(Expr {
                        kind: ExprKind::Var(id),
                        ty: Types::from(
                            PTypes::from_elem(BaseType::Bool.into(), 1),
                            &mut self.store,
                        ),
                    }),
                    Box::new(e_when),
                    Box::new(e_whennot),
                )
            }
            TExprKind::FunCall {
                extern_symbol,
                spawn,
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
                    let cell = self.cells;
                    self.cells += 1;

                    let s = format!("#{}", self.equations.len());
                    let i = self.equations.len();
                    let ty = ty.clone();
                    for j in 0..ty.inner.len() {
                        self.store.insert(s.clone(), SIdent::new(i, j, spawn));
                    }
                    add_dep(i);

                    self.deps.push(Vec::new());
                    // dummy EqKind::Input
                    self.equations
                        .push((Equation::new(ty.clone(), EqKind::Input), None));

                    let mut args = Vec::with_capacity(arguments.len());
                    for expr in arguments {
                        let e = self.normalize_expr(expr, i, depends);
                        args.push(e);
                    }

                    self.equations[i].0.kind = EqKind::NodeCall {
                        ident: function,
                        args,
                        cell,
                        spawn,
                    };

                    ExprKind::Tuple(
                        (0..ty.inner.len())
                            .into_iter()
                            .map(|j| SIdent::new(i, j, spawn))
                            .collect(),
                    )
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

        visited[idx] = (1, parent);
        for j in 0..self.deps[idx].len() {
            self.visit(self.deps[idx][j], Some(idx), visited)?;
        }
        visited[idx].0 = 2;

        self.order.push(idx);

        Ok(())
    }
}

/// permut v according to permutations, and change the SIdent in the expressions
/// contained in v
/// SAFETY: the mapping i -> permutations[i] should be a permutation of [0, v.len()]
unsafe fn permut(v: &mut Vec<Equation>, mut permutations: Vec<usize>) {
    assert_eq!(v.len(), permutations.len());

    for eq in v.iter_mut() {
        eq.types.permut(&mut permutations);
        match &mut eq.kind {
            EqKind::CellExpr(e, _) | EqKind::Expr(e) => e.permut(&mut permutations),
            EqKind::NodeCall { args, .. } => {
                for arg in args {
                    arg.permut(&mut permutations);
                }
            }
            EqKind::Input => (),
        }
    }

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
        let vis = node.vis.clone();
        let ret = node.ret.clone();

        let mut context = Context::new();
        context.schedule_eq(node)?;
        node_deps.insert(name.to_string(), context.node_deps);

        let params = context.equations[0].0.types.clone();

        let (ret_vars, ret_types) = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .unzip();
        let ret_types = Types::from(ret_types, &mut context.store);

        let mut equations = context.equations.into_iter().map(|eq| eq.0).collect();
        unsafe {
            permut(&mut equations, context.order);
        }

        Ok(Node {
            vis,
            name,
            params,
            ret_vars,
            ret_types,
            equations,
        })
    }
}

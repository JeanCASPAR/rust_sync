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
}

impl SIdent {
    pub fn new(eq: usize, idx: usize) -> Self {
        Self { eq, idx }
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
    pub time: Vec<TimeCounter>,
}

impl Types {
    fn from(types: PTypes, store: &mut StringPatriciaMap<SIdent>, time: Vec<TimeCounter>) -> Self {
        let mut inner = SmallVec::with_capacity(types.len());
        let mut clocks = Vec::new();
        for ty in types {
            inner.push(ty.base);
            if clocks.is_empty() {
                // we suppose that all types have the same clocks in a tuple
                // TODO: change when clocks are supported by types at typing
                clocks.extend(
                    ty.clocks
                        .into_iter()
                        .map(|clock| ClockType::from(clock, store)),
                );
            }
        }

        Self {
            inner,
            clocks,
            time,
        }
    }

    fn permut(&mut self, permutations: &mut [usize]) {
        for clock in &mut self.clocks {
            clock.clock.eq = permutations[clock.clock.eq];
        }
        for TimeCounter { eq, .. } in &mut self.time {
            *eq = permutations[*eq];
        }
    }
}

impl Types {
    pub fn new() -> Self {
        Self {
            inner: SmallVec::new(),
            clocks: Vec::new(),
            time: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub struct Ast {
    pub nodes: Vec<Node>,
    pub extern_functions: Vec<Ident>,
}

impl Ast {
    /// check if there is a cyclic dependencies between nodes
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

    /// check if there is a cyclic dependencies between nodes
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

        Ok(Ast {
            nodes,
            extern_functions: ast.extern_functions,
        })
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
        args: Vec<SIdent>,
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
    Then(SIdent, SIdent),
    Minus(SIdent),
    Not(SIdent),
    MathBinOp(SIdent, MathBinOp, SIdent),
    BoolBinOp(SIdent, BoolBinOp, SIdent),
    CompOp(SIdent, CompOp, SIdent),
    If(SIdent, SIdent, SIdent),
    Int(i64),
    Float(f64),
    Bool(bool),
    FloatCast(SIdent),
    FunCall {
        function: Ident,
        arguments: Vec<SIdent>,
    },
    Tuple(Vec<SIdent>),
}

impl Expr {
    /// permut the variables according to some permutation
    fn permut(&mut self, permutations: &mut [usize]) {
        self.ty.permut(permutations);
        match &mut self.kind {
            ExprKind::Var(id)
            | ExprKind::Minus(id)
            | ExprKind::Not(id)
            | ExprKind::FloatCast(id) => id.eq = permutations[id.eq],
            ExprKind::Tuple(tuple) => {
                for id in tuple {
                    id.eq = permutations[id.eq];
                }
            }
            ExprKind::Then(id1, id2)
            | ExprKind::MathBinOp(id1, _, id2)
            | ExprKind::BoolBinOp(id1, _, id2)
            | ExprKind::CompOp(id1, _, id2) => {
                id1.eq = permutations[id1.eq];
                id2.eq = permutations[id2.eq];
            }
            ExprKind::If(id_cond, id_then, id_else) => {
                id_cond.eq = permutations[id_cond.eq];
                id_then.eq = permutations[id_then.eq];
                id_else.eq = permutations[id_else.eq];
            }
            ExprKind::Unit
            | ExprKind::Pre(..)
            | ExprKind::Int(..)
            | ExprKind::Float(..)
            | ExprKind::Bool(..) => (),
            ExprKind::FunCall { arguments, .. } => {
                for id in arguments {
                    id.eq = permutations[id.eq];
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TimeCounter {
    pub eq: usize,
    pub on_first_time: bool,
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

    /// returns true if the equation is an expression of the form a -> b
    pub fn is_then(&self) -> bool {
        matches!(
            self.kind,
            EqKind::Expr(Expr {
                kind: ExprKind::Then(..),
                ..
            }) | EqKind::CellExpr(
                Expr {
                    kind: ExprKind::Then(..),
                    ..
                },
                _
            )
        )
    }
}

#[derive(Debug)]
struct Context {
    equations: Vec<(Equation, Option<Span>)>,
    /// n in deps[m] <=> the equation m depends on the equation n
    deps: Vec<Vec<usize>>,
    /// we replace all idents by a pair whose first element is the number
    /// of the equation introducing it (0 if it is an input) and whose
    /// second element is the number of the ident in the declaration
    store: StringPatriciaMap<SIdent>,
    /// the equation with number i is to be scheduled at order order[i]
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

    /// add en equation, returns its index in self.equations
    fn add_equation(
        &mut self,
        ty: Types,
        kind: EqKind,
        span: Option<Span>,
        deps: Vec<usize>,
    ) -> usize {
        self.equations.push((Equation::new(ty, kind), span));
        self.deps.push(deps);
        self.equations.len() - 1
    }

    /// schedule all equations of the node
    fn schedule_eq(&mut self, node: TNode) -> Result<(), Error> {
        let vec_ty = node
            .params
            .0
            .iter()
            .enumerate()
            .map(|(i, param)| {
                self.store.insert(param.id.to_string(), SIdent::new(0, i));
                param.ty.base.clone()
            })
            .collect();
        let mut ty = Types::new();
        ty.inner = vec_ty;
        self.add_equation(ty, EqKind::Input, None, Vec::new());

        let mut eqs_id = Vec::with_capacity(node.body.len());
        for decl in node.body.iter() {
            let ty = Types::from(decl.expr.inner.types.clone(), &mut self.store, Vec::new());
            // dummy EqKind::Input here because we cannot yet translate the expression
            let i = self.add_equation(ty, EqKind::Input, Some(decl.expr.span), Vec::new());
            eqs_id.push(i);

            for (j, var) in decl.vars.iter().enumerate() {
                self.store.insert(var.id.to_string(), SIdent::new(i, j));
            }
        }

        for (i, decl) in eqs_id.into_iter().zip(node.body.into_iter()) {
            let e = self.normalize_expr(decl.expr.inner, i, Vec::new());
            self.equations[i].0.kind = EqKind::Expr(e);
        }

        self.topo_sort()?;

        Ok(())
    }

    /// normalize an expression, generating equations for all subexpressions and dependencies between them
    /// parent is the parent equation
    /// time is the time at wich the equation is defined
    fn normalize_expr(&mut self, e: TExpr, parent: usize, time: Vec<TimeCounter>) -> Expr {
        let mut add_dep = |i: usize| {
            if !self.deps[parent].contains(&i) {
                self.deps[parent].push(i);
            }
        };
        let ty = Types::from(e.types, &mut self.store, time.clone());
        let sident = |eq: usize| SIdent { eq, idx: 0 };
        let kind = match e.kind {
            TExprKind::Var(id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);
                ExprKind::Var(id)
            }
            TExprKind::Unit => ExprKind::Unit,
            TExprKind::Pre(e) => {
                let ty = ty.clone();
                if ty.inner.len() > 1 {
                    todo!("pre with tuple unimplemented yet")
                }

                let i = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let s = format!("#{}", i);
                self.store.insert(s.clone(), SIdent::new(i, 0));
                let cell = self.cells;
                self.cells += 1;

                let mut time = time.clone();
                let _ = time.pop(); // we pop the last then
                let e = self.normalize_expr(*e, i, time);

                self.equations[i].0.kind = EqKind::CellExpr(e, cell);

                ExprKind::Pre(cell)
            }
            TExprKind::Then(e1, e2) => {
                let mut present = time.clone();
                present.push(TimeCounter {
                    eq: parent,
                    on_first_time: true,
                });
                let mut future = time.clone();
                future.push(TimeCounter {
                    eq: parent,
                    on_first_time: false,
                });

                let ty1 = Types::new();
                let eq1 = self.add_equation(ty1, EqKind::Input, Some(e1.span), Vec::new());
                let e1 = self.normalize_expr(*e1, eq1, present);
                self.equations[eq1].0.types = e1.ty.clone();
                self.equations[eq1].0.kind = EqKind::Expr(e1);

                let ty2 = Types::new();
                let eq2 = self.add_equation(ty2, EqKind::Input, Some(e2.span), Vec::new());
                let e2 = self.normalize_expr(*e2, eq2, future);
                self.equations[eq2].0.types = e2.ty.clone();
                self.equations[eq2].0.kind = EqKind::Expr(e2);

                if !self.deps[parent].contains(&eq1) {
                    self.deps[parent].push(eq1);
                }
                if !self.deps[parent].contains(&eq2) {
                    self.deps[parent].push(eq2);
                }

                ExprKind::Then(sident(eq1), sident(eq2))
            }
            TExprKind::Minus(e) => {
                let ty = Types::new();
                let eq = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let e = self.normalize_expr(*e, eq, time);
                self.equations[eq].0.types = e.ty.clone();
                self.equations[eq].0.kind = EqKind::Expr(e);

                if !self.deps[parent].contains(&eq) {
                    self.deps[parent].push(eq);
                }

                ExprKind::Minus(sident(eq))
            }
            TExprKind::Not(e) => {
                let ty = Types::new();
                let eq = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let e = self.normalize_expr(*e, eq, time);
                self.equations[eq].0.types = e.ty.clone();
                self.equations[eq].0.kind = EqKind::Expr(e);

                if !self.deps[parent].contains(&eq) {
                    self.deps[parent].push(eq);
                }

                ExprKind::Not(sident(eq))
            }
            TExprKind::MathBinOp(e1, op, e2) => {
                let ty1 = Types::new();
                let eq1 = self.add_equation(ty1, EqKind::Input, Some(e1.span), Vec::new());
                let e1 = self.normalize_expr(*e1, eq1, time.clone());
                self.equations[eq1].0.types = e1.ty.clone();
                self.equations[eq1].0.kind = EqKind::Expr(e1);

                let ty2 = Types::new();
                let eq2 = self.add_equation(ty2, EqKind::Input, Some(e2.span), Vec::new());
                let e2 = self.normalize_expr(*e2, eq2, time);
                self.equations[eq2].0.types = e2.ty.clone();
                self.equations[eq2].0.kind = EqKind::Expr(e2);

                if !self.deps[parent].contains(&eq1) {
                    self.deps[parent].push(eq1);
                }
                if !self.deps[parent].contains(&eq2) {
                    self.deps[parent].push(eq2);
                }

                ExprKind::MathBinOp(sident(eq1), op, sident(eq2))
            }
            TExprKind::BoolBinOp(e1, op, e2) => {
                let ty1 = Types::new();
                let eq1 = self.add_equation(ty1, EqKind::Input, Some(e1.span), Vec::new());
                let e1 = self.normalize_expr(*e1, eq1, time.clone());
                self.equations[eq1].0.types = e1.ty.clone();
                self.equations[eq1].0.kind = EqKind::Expr(e1);

                let ty2 = Types::new();
                let eq2 = self.add_equation(ty2, EqKind::Input, Some(e2.span), Vec::new());
                let e2 = self.normalize_expr(*e2, eq2, time);
                self.equations[eq2].0.types = e2.ty.clone();
                self.equations[eq2].0.kind = EqKind::Expr(e2);

                if !self.deps[parent].contains(&eq1) {
                    self.deps[parent].push(eq1);
                }
                if !self.deps[parent].contains(&eq2) {
                    self.deps[parent].push(eq2);
                }

                ExprKind::BoolBinOp(sident(eq1), op, sident(eq2))
            }
            TExprKind::CompOp(e1, op, e2) => {
                let ty1 = Types::new();
                let eq1 = self.add_equation(ty1, EqKind::Input, Some(e1.span), Vec::new());
                let e1 = self.normalize_expr(*e1, eq1, time.clone());
                self.equations[eq1].0.types = e1.ty.clone();
                self.equations[eq1].0.kind = EqKind::Expr(e1);

                let ty2 = Types::new();
                let eq2 = self.add_equation(ty2, EqKind::Input, Some(e2.span), Vec::new());
                let e2 = self.normalize_expr(*e2, eq2, time);
                self.equations[eq2].0.types = e2.ty.clone();
                self.equations[eq2].0.kind = EqKind::Expr(e2);

                if !self.deps[parent].contains(&eq1) {
                    self.deps[parent].push(eq1);
                }
                if !self.deps[parent].contains(&eq2) {
                    self.deps[parent].push(eq2);
                }

                ExprKind::CompOp(sident(eq1), op, sident(eq2))
            }
            TExprKind::If(b, e_then, e_else) => {
                let ty_b = Types::new();
                let eq_b = self.add_equation(ty_b, EqKind::Input, Some(b.span), Vec::new());
                let b = self.normalize_expr(*b, eq_b, time.clone());
                self.equations[eq_b].0.types = b.ty.clone();
                self.equations[eq_b].0.kind = EqKind::Expr(b);

                let ty_then = Types::new();
                let eq_then =
                    self.add_equation(ty_then, EqKind::Input, Some(e_then.span), Vec::new());
                let e_then = self.normalize_expr(*e_then, eq_then, time.clone());
                self.equations[eq_then].0.types = e_then.ty.clone();
                self.equations[eq_then].0.kind = EqKind::Expr(e_then);

                let ty_else = Types::new();
                let eq_else = self.add_equation(ty_else, EqKind::Input, Some(e.span), Vec::new());
                let e_else = self.normalize_expr(*e_else, eq_else, time);
                self.equations[eq_else].0.types = e_else.ty.clone();
                self.equations[eq_else].0.kind = EqKind::Expr(e_else);

                if !self.deps[parent].contains(&eq_b) {
                    self.deps[parent].push(eq_b);
                }
                if !self.deps[parent].contains(&eq_then) {
                    self.deps[parent].push(eq_then);
                }
                if !self.deps[parent].contains(&eq_else) {
                    self.deps[parent].push(eq_else);
                }

                ExprKind::If(sident(eq_b), sident(eq_then), sident(eq_else))
            }
            TExprKind::Int(n) => ExprKind::Int(n),
            TExprKind::Float(x) => ExprKind::Float(x),
            TExprKind::Bool(b) => ExprKind::Bool(b),
            TExprKind::FloatCast(e) => {
                let ty = Types::new();
                let eq = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let e = self.normalize_expr(*e, eq, time);
                self.equations[eq].0.types = e.ty.clone();
                self.equations[eq].0.kind = EqKind::Expr(e);

                if !self.deps[parent].contains(&eq) {
                    self.deps[parent].push(eq);
                }

                ExprKind::FloatCast(sident(eq))
            }
            TExprKind::When(e, id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);

                let ty = Types::new();
                let eq = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let e = self.normalize_expr(*e, eq, time);
                self.equations[eq].0.types = e.ty.clone();
                self.equations[eq].0.kind = EqKind::Expr(e);

                if !self.deps[parent].contains(&eq) {
                    self.deps[parent].push(eq);
                }

                ExprKind::Var(sident(eq))
            }
            TExprKind::WhenNot(e, id) => {
                let id = self.store.get(id.to_string()).unwrap().clone();
                add_dep(id.eq);

                let ty = Types::new();
                let eq = self.add_equation(ty, EqKind::Input, Some(e.span), Vec::new());
                let e = self.normalize_expr(*e, eq, time);
                self.equations[eq].0.types = e.ty.clone();
                self.equations[eq].0.kind = EqKind::Expr(e);

                if !self.deps[parent].contains(&eq) {
                    self.deps[parent].push(eq);
                }

                ExprKind::Var(sident(eq))
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
                        let ty = Types::new();
                        let eq = self.add_equation(ty, EqKind::Input, Some(arg.span), Vec::new());
                        let arg = self.normalize_expr(arg, eq, time.clone());
                        self.equations[eq].0.types = arg.ty.clone();
                        self.equations[eq].0.kind = EqKind::Expr(arg);

                        if !self.deps[parent].contains(&eq) {
                            self.deps[parent].push(eq);
                        }

                        args.push(sident(eq));
                    }
                    ExprKind::FunCall {
                        function,
                        arguments: args,
                    }
                } else {
                    self.node_deps.push(function.clone());
                    let cell = self.cells;
                    self.cells += 1;

                    let i = self.add_equation(ty.clone(), EqKind::Input, None, Vec::new());
                    let ty = ty.clone();
                    for j in 0..ty.inner.len() {
                        let s = format!("res {} of {}", j, i);
                        self.store.insert(s.clone(), SIdent::new(i, j));
                    }
                    // add_dep(i)
                    if !self.deps[parent].contains(&i) {
                        self.deps[parent].push(i);
                    }

                    let mut args = Vec::with_capacity(arguments.len());
                    let mut time = time.clone();
                    if spawn {
                        let _ = time.pop(); // cf pre
                    }
                    for arg in arguments {
                        let ty = Types::new();
                        let eq = self.add_equation(ty, EqKind::Input, Some(arg.span), Vec::new());
                        let arg = self.normalize_expr(arg, eq, time.clone());
                        self.equations[eq].0.types = arg.ty.clone();
                        self.equations[eq].0.kind = EqKind::Expr(arg);

                        if !self.deps[i].contains(&eq) {
                            self.deps[i].push(eq);
                        }

                        args.push(sident(eq));
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
                            .map(|j| SIdent::new(i, j))
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
/// we want that new_v[permutations[i]] = old_v[i]
/// it is unsafe because we do so without cloning, but we still allocate a new vector
/// SAFETY: the mapping i -> permutations[i] should be a permutation of [0, v.len()]
unsafe fn permut(v: &mut Vec<Equation>, mut permutations: Vec<usize>) {
    assert_eq!(v.len(), permutations.len());

    for eq in v.iter_mut() {
        eq.types.permut(&mut permutations);
        match &mut eq.kind {
            EqKind::CellExpr(e, _) | EqKind::Expr(e) => e.permut(&mut permutations),
            EqKind::NodeCall { args, .. } => {
                for arg in args {
                    arg.eq = permutations[arg.eq];
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

        let (mut ret_vars, ret_types): (Vec<SIdent>, _) = ret
            .into_iter()
            .map(|(id, ty)| (context.store.get(&id.to_string()).unwrap().clone(), ty))
            .unzip();
        let mut ret_types = Types::from(ret_types, &mut context.store, Vec::new());

        let mut equations = context.equations.into_iter().map(|eq| eq.0).collect();
        // we want to invert the permutation context.order
        {
            let length = context.order.len();
            let mut v = Vec::with_capacity(length);
            for (i, j) in context.order.into_iter().enumerate() {
                v.spare_capacity_mut()[j].write(i);
            }
            unsafe { v.set_len(length) }
            context.order = v;
        }
        unsafe {
            ret_types.permut(&mut context.order);
            for ret_var in &mut ret_vars {
                ret_var.eq = context.order[ret_var.eq];
            }
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

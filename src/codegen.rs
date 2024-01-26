use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};

use crate::{
    parser::{BaseType, BoolBinOp, CompOp, MathBinOp},
    scheduler::{Ast, EqKind, Equation, Expr, ExprKind, Node, SIdent, Types},
};

impl ToTokens for BaseType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match self {
            Self::Bool => quote!(bool),
            Self::Float64 => quote!(f64),
            Self::Int64 => quote!(i64),
            Self::Unit => quote!(()),
        })
    }
}

impl ToTokens for Types {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let types = &self.inner;
        tokens.extend(if types.is_empty() {
            quote! { () }
        } else {
            quote! {
                (#(#types),*,)
            }
        })
    }
}

struct WrapEquations<'a, F> {
    equations: &'a [Equation],
    function: F,
}
impl<'a, F> WrapEquations<'a, F> {
    fn new(equations: &'a [Equation], function: F) -> Self {
        Self {
            equations,
            function,
        }
    }
}

impl<'a, F: for<'b> Fn(&'a Equation, usize, &'b mut TokenStream)> ToTokens
    for WrapEquations<'a, F>
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        for (i, eq) in self.equations.iter().enumerate() {
            (self.function)(eq, i, tokens)
        }
    }
}

impl ToTokens for MathBinOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = match self {
            MathBinOp::Add => quote! {+},
            MathBinOp::Sub => quote! {-},
            MathBinOp::Mul => quote! {*},
            MathBinOp::Div => quote! {/},
            MathBinOp::Rem => quote! {%},
        };
        tokens.extend(ts);
    }
}

impl ToTokens for BoolBinOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = match self {
            BoolBinOp::And => quote! {&&},
            BoolBinOp::Or => quote! {||},
        };
        tokens.extend(ts);
    }
}

impl ToTokens for CompOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = match self {
            CompOp::Ge => quote! {>=},
            CompOp::Gt => quote! {>},
            CompOp::Le => quote! {<=},
            CompOp::Lt => quote! {>},
            CompOp::Eq => quote! {==},
            CompOp::NEq => quote! {!=},
        };
        tokens.extend(ts);
    }
}

impl ToTokens for SIdent {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let var = format_ident!("var_{}", self.eq);
        let j = syn::Index::from(self.idx);

        let value = quote! {
            (*#var.as_mut_ptr())
        };
        let ts = quote! {
            unsafe {
                #value.#j
            }
        };

        tokens.extend(ts);
    }
}

// usize : index of the equation
struct ExprWrapper<'a>(&'a Expr, usize);

impl ToTokens for ExprWrapper<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = match &self.0.kind {
            ExprKind::Var(var) => {
                quote! { #var }
            }
            ExprKind::Unit => quote! { () },
            ExprKind::Pre(i) => {
                let cell = format_ident!("cell_{}", i);
                quote! {
                    unsafe {
                        (*#cell.as_ptr()).0 // pre cells are always of size 1
                    }
                }
            }
            ExprKind::Then(e1, e2) => {
                let first_time = format_ident!("first_time_{}", self.1);
                quote! {
                    if *#first_time {
                        *#first_time = false;
                        #e1
                    } else {
                        #e2
                    }
                }
            }
            ExprKind::Minus(e) => {
                quote! { (-#e) }
            }
            ExprKind::Not(e) => {
                quote! { (!#e) }
            }
            ExprKind::MathBinOp(e1, op, e2) => {
                quote! { (#e1 #op #e2) }
            }
            ExprKind::BoolBinOp(e1, op, e2) => {
                quote! { (#e1 #op #e2) }
            }

            ExprKind::CompOp(e1, op, e2) => {
                quote! { (#e1 #op #e2) }
            }
            ExprKind::If(cond, e_then, e_else) => {
                quote! {
                    if #cond { #e_then } else { #e_else }
                }
            }
            ExprKind::Int(n) => quote! { #n },
            ExprKind::Float(x) => quote! { #x },
            ExprKind::Bool(b) => quote! { #b },
            ExprKind::FloatCast(e) => {
                quote! { (#e as f64) }
            }
            ExprKind::FunCall {
                function,
                arguments,
            } => {
                // mangling of extern function
                let function = format_ident!("extern_{}", function);
                let args = arguments.iter();
                quote! {
                    #function (#(#args),*)
                }
            }
            ExprKind::Tuple(vars) => {
                let vars = vars.iter().map(|var| {
                    quote! { #var }
                });

                quote! {
                    (#(#vars,)*)
                }
            }
        };

        tokens.extend(ts);
    }
}

impl ToTokens for Node {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let node_name = format_ident!("Node{}", self.name);
        let iterator_name = format_ident!("Iterator{}", self.name);
        let name = format_ident!("{}", self.name);

        let fields_decl = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| match eq.kind {
                _ if eq.is_then() => {
                    let field = format_ident!("first_time_{}", i);
                    tokens.extend(quote! {
                        #field: bool,
                    });
                }
                EqKind::Expr(..) | EqKind::Input => (),
                EqKind::NodeCall {
                    ref ident,
                    cell,
                    spawn,
                    ..
                } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = format_ident!("Node{}", ident);
                    let ty = if spawn {
                        quote! { Handle<#ty> }
                    } else {
                        quote! { #ty }
                    };

                    tokens.extend(quote! {
                        #field: ::std::boxed::Box<#ty>,
                    });
                }
                EqKind::CellExpr(_, cell) => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = &eq.types;

                    tokens.extend(quote! {
                        #field: ::std::mem::MaybeUninit<#ty>,
                    });
                }
            },
        );

        let fields_init = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| match eq.kind {
                _ if eq.is_then() => {
                    let field = format_ident!("first_time_{}", i);
                    tokens.extend(quote! {
                        #field: true,
                    });
                }
                EqKind::Expr(_) | EqKind::Input => (),
                EqKind::NodeCall {
                    ref ident,
                    cell,
                    spawn,
                    ..
                } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = format_ident!("Node{}", ident);
                    let ty = if spawn {
                        quote! { Handle<#ty> }
                    } else {
                        quote! { #ty }
                    };

                    tokens.extend(quote! {
                        #field: ::std::boxed::Box::new(<#ty>::new()),
                    })
                }
                EqKind::CellExpr(_, cell) => {
                    let field = format_ident!("cell_{}", cell);

                    tokens.extend(quote! {
                        #field: ::std::mem::MaybeUninit::uninit(),
                    })
                }
            },
        );

        let reset = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| {
                if let EqKind::NodeCall { cell, .. } = eq.kind {
                    let field = format_ident!("cell_{}", cell);
                    tokens.extend(quote! {
                        self.#field.reset();
                    })
                } else if eq.is_then() {
                    let field = format_ident!("first_time_{}", i);
                    tokens.extend(quote! {
                        self.#field = true;
                    })
                }
            },
        );

        let unpack = {
            let fields = WrapEquations::new(
                &self.equations,
                |eq: &Equation, i, tokens: &mut TokenStream| match eq.kind {
                    _ if eq.is_then() => {
                        let field = format_ident!("first_time_{}", i);
                        tokens.extend(quote! { #field, });
                    }
                    EqKind::Expr(_) | EqKind::Input => (),
                    EqKind::NodeCall { cell, .. } => {
                        let field = format_ident!("cell_{}", cell);

                        tokens.extend(quote! { #field, })
                    }
                    EqKind::CellExpr(_, cell) => {
                        let field = format_ident!("cell_{}", cell);

                        tokens.extend(quote! { #field, })
                    }
                },
            );

            quote! {
                let #node_name { #fields } = self;
            }
        };

        let compute = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| {
                let is_active = eq
                    .types
                    .time
                    .iter()
                    .map(|time| {
                        let id = format_ident!("first_time_{}", time.eq);
                        (quote! { *#id }, time.on_first_time)
                    })
                    .chain(eq.types.clocks.iter().map(|clock| {
                        let id = &clock.clock;
                        (quote! { #id }, clock.positive)
                    }))
                    .map(|(id, state)| {
                        if state {
                            quote! { #id }
                        } else {
                            quote! { !#id }
                        }
                    })
                    .fold(quote! { true }, |acc, next| {
                        quote! { #acc && #next }
                    });

                let var = format_ident!("var_{}", i);
                let ty = &eq.types;
                let quoted_ty = quote! { #ty };
                let ts = match &eq.kind {
                    EqKind::Input => {
                        assert_eq!(i, 0);
                        quote! {
                            input
                        }
                    }
                    EqKind::NodeCall {
                        args,
                        cell,
                        spawn: false,
                        ..
                    } => {
                        let node = format_ident!("cell_{}", cell);
                        if args.len() >= 1 {
                            quote! {
                                #node.step((#(#args),*,))
                            }
                        } else {
                            quote! {
                                #node.step(())
                            }
                        }
                    }
                    EqKind::NodeCall {
                        cell, spawn: true, ..
                    } => {
                        let node = format_ident!("cell_{}", cell);
                        quote! {
                            #node.join()
                        }
                    }
                    EqKind::Expr(e) | EqKind::CellExpr(e, _) => {
                        let e = ExprWrapper(e, i);
                        if ty.inner.len() == 1 && !matches!(e.0.kind, ExprKind::Tuple(_)) {
                            quote! { (#e,) }
                        } else {
                            quote! {
                                #e
                            }
                        }
                    }
                };
                tokens.extend(quote! {
                    let mut #var: ::std::mem::MaybeUninit<#quoted_ty> = if #is_active {
                        ::std::mem::MaybeUninit::new(#ts)
                    } else {
                        ::std::mem::MaybeUninit::uninit()
                    };
                });
            },
        );

        let save_cells = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| match &eq.kind {
                EqKind::CellExpr(_, cell) => {
                    let var = format_ident!("var_{}", i);
                    let cell = format_ident!("cell_{}", cell);

                    let ts = quote! {
                        unsafe {
                            #cell.as_mut_ptr().copy_from_nonoverlapping(#var.as_ptr(), 1);
                        }
                    };
                    tokens.extend(ts);
                }
                EqKind::NodeCall {
                    args,
                    cell,
                    spawn: true,
                    ..
                } => {
                    let node = format_ident!("cell_{}", cell);
                    let ts = if args.len() >= 1 {
                        quote! {
                            #node.prepare((#(#args),*,));
                        }
                    } else {
                        quote! {
                            #node.prepare(());
                        }
                    };
                    tokens.extend(ts)
                }
                _ => (),
            },
        );

        let input_types = &self.params;
        let ret_types = &self.ret_types;
        let ret = &self.ret_vars;
        let vis = &self.vis;

        let ts = quote! {
            #vis fn #name<
                T: ::std::iter::Iterator<Item = #input_types>
                >(iterator: T) -> #iterator_name<T> {
                #iterator_name { iterator, node: #node_name::new() }
            }

            impl<T: ::std::iter::Iterator<Item = #input_types>> ::std::iter::Iterator for #iterator_name<T> {
                type Item = #ret_types;
                fn next(&mut self) -> ::std::option::Option<#ret_types> {
                    Some(self.node.step(self.iterator.next()?))
                }
            }

            #vis struct #iterator_name<T> {
                iterator: T,
                node: #node_name
            }

            impl<T> #iterator_name<T> {
                #vis fn reset(&mut self) {
                    self.node.reset()
                }
            }

            struct #node_name {
                #fields_decl
            }

            impl #node_name {
                pub fn new() -> Self {
                    Self {
                        #fields_init
                    }
                }

                pub fn reset(&mut self) {
                    #reset
                }

                pub fn step(&mut self, input: #input_types) -> #ret_types {
                    #unpack

                    #compute

                    #save_cells

                    (#(#ret,)*)

                }
            }

            impl Node for #node_name {
                type Arg = #input_types;
                type Ret = #ret_types;

                fn new() -> Self {
                    Self::new()
                }
                fn reset(&mut self) {
                    Self::reset(self)
                }
                fn step(&mut self, arg: Self::Arg) -> Self::Ret {
                    Self::step(self, arg)
                }
            }
        };

        tokens.extend(ts);
    }
}

impl ToTokens for Ast {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let nodes = &self.nodes;
        let imports = if self.extern_functions.is_empty() {
            quote! {}
        } else {
            let imports = self.extern_functions.iter().map(|id| {
                let extern_id = format_ident!("extern_{}", id);
                quote! {
                    #id as #extern_id
                }
            });
            quote! {
                use super::{#(#imports),*};
            }
        };
        let ts = quote! {
            pub mod sync {
                #imports

                trait Node {
                    type Arg;
                    type Ret;

                    fn new() -> Self;
                    fn reset(&mut self);
                    fn step(&mut self, arg: Self::Arg) -> Self::Ret;
                }

                enum Command<T> {
                    Reset,
                    Step(T)
                }

                struct Handle<N: Node> {
                    sender: ::std::sync::mpsc::SyncSender<Command<N::Arg>>,
                    recv: ::std::sync::mpsc::Receiver<N::Ret>,
                    last_result: Option<N::Ret>,
                }

                impl<N> Handle<N> where
                    N: Node,
                    N::Arg: Send + 'static,
                    N::Ret: Clone + Send + 'static,
                {
                    fn new() -> Self {
                        let (arg_sender, arg_receiver) = ::std::sync::mpsc::sync_channel(0);
                        let (res_sender, res_receiver) = ::std::sync::mpsc::sync_channel(0);

                        let thread = move || {
                            let mut node = N::new();
                            while let Ok(cmd) = arg_receiver.recv() {
                                match cmd {
                                    Command::Reset => node.reset(),
                                    Command::Step(arg) => {
                                        let res = node.step(arg);
                                        let _ = res_sender.send(res); // if it returns an error, then there is no more receiver,
                                        // and the next arg_receiver.recv() will also produce an error and exit the thread
                                    }
                                }
                            }
                        };

                        ::std::thread::spawn(thread);

                        Handle {
                            sender: arg_sender,
                            recv: res_receiver,
                            last_result: None,
                        }
                    }
                    fn reset(&mut self) {
                        let _ = self.recv.recv(); // drop previous result
                        self.sender.send(Command::Reset).unwrap();
                        self.last_result = None;
                    }
                    fn prepare(&mut self, arg: <N as Node>::Arg) {
                        self.last_result = None;
                        self.sender.send(Command::Step(arg)).unwrap();
                    }
                    fn join(&mut self) -> <N as Node>::Ret {
                        match self.last_result.take() {
                            Some(res) => {
                                self.last_result = Some(res.clone());
                                res
                            }
                            None => {
                                let res = self.recv.recv().unwrap();
                                self.last_result = Some(res.clone());
                                res
                            }
                        }
                    }
                }

                #(#nodes)*
            }
        };
        tokens.extend(ts);
    }
}

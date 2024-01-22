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

        let maybe_uninit = quote! {
            (*#var.as_mut_ptr())
        };
        let value = if self.wait {
            quote! { #maybe_uninit.join() }
        } else {
            maybe_uninit
        };
        let ts = quote! {
            unsafe {
                #value.#j
            }
        };

        tokens.extend(ts);
    }
}

impl ToTokens for Expr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = match &self.kind {
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
                quote! {
                    if *counter == 0 {
                        #e1
                    } else {
                        *counter -= 1;
                        let e = #e2;
                        *counter += 1;
                        e
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
            |eq: &Equation, _, tokens: &mut TokenStream| match eq.kind {
                EqKind::Expr(_) | EqKind::Input => (),
                EqKind::NodeCall {
                    ref ident, cell, ..
                } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = format_ident!("Node{}", ident);

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
            |eq: &Equation, _, tokens: &mut TokenStream| match eq.kind {
                EqKind::Expr(_) | EqKind::Input => (),
                EqKind::NodeCall {
                    ref ident, cell, ..
                } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = format_ident!("Node{}", ident);

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
            |eq: &Equation, _, tokens: &mut TokenStream| {
                if let EqKind::NodeCall { cell, .. } = eq.kind {
                    let field = format_ident!("cell_{}", cell);
                    tokens.extend(quote! {
                        self.#field.reset();
                    })
                }
            },
        );

        let unpack = {
            let fields = WrapEquations::new(
                &self.equations,
                |eq: &Equation, _, tokens: &mut TokenStream| match eq.kind {
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
                let #node_name { counter, #fields } = self;
            }
        };

        let compute = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| {
                let is_active = eq.types.clocks.iter().fold(quote! { true }, |acc, clock| {
                    let id = &clock.clock;
                    let pos = clock.positive;
                    quote! {
                        #acc && (#id == #pos)
                    }
                });

                let var = format_ident!("var_{}", i);
                let ty = &eq.types;
                let mut quoted_ty = quote! { #ty };
                // force evaluation of the arguments of a call before a thread if launched, if any
                let mut force_args = quote! {};
                let ts = match &eq.kind {
                    EqKind::Input => {
                        assert_eq!(i, 0);
                        quote! {
                            input
                        }
                    }
                    EqKind::NodeCall {
                        args, cell, spawn, ..
                    } => {
                        let node = format_ident!("cell_{}", cell);
                        let ts = if args.len() >= 1 {
                            force_args.extend(args.iter().enumerate().map(|(i, e)| {
                                let id = format_ident!("arg_{}", i);
                                quote! {
                                    let #id = #e;
                                }
                            }));
                            let args = (0..args.len())
                                .into_iter()
                                .map(|i| format_ident!("arg_{}", i));
                            quote! {
                                #node.step((#(#args),*,))
                            }
                        } else {
                            quote! {
                                #node.step(())
                            }
                        };
                        if *spawn {
                            quoted_ty = quote! { JoinCache<#ty> };
                            quote! { JoinCache::new(scope.spawn(move || #ts))}
                        } else {
                            ts
                        }
                    }
                    EqKind::Expr(e) | EqKind::CellExpr(e, _) => {
                        if ty.inner.len() == 1 && !matches!(e.kind, ExprKind::Tuple(_)) {
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
                        #force_args
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
                counter: usize,
                #fields_decl
            }

            impl #node_name {
                pub fn new() -> Self {
                    Self {
                        counter: 0,
                        #fields_init
                    }
                }

                pub fn reset(&mut self) {
                    #reset
                    self.counter = 0;
                }

                pub fn step(&mut self, input: #input_types) -> #ret_types {
                    #unpack

                    ::std::thread::scope(|scope| {
                        #compute

                        *counter += 1;

                        #save_cells

                        (#(#ret,)*)
                    })
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

                enum JoinCache<'scope, T> {
                    Wait(::std::option::Option<::std::thread::ScopedJoinHandle<'scope, T>>),
                    Finished(T),
                }

                impl<'scope, T> JoinCache<'scope, T> {
                    fn new(handle: ::std::thread::ScopedJoinHandle<'scope, T>) -> Self {
                        Self::Wait(Some(handle))
                    }
                }

                impl<'scope, T: Clone> JoinCache<'scope, T> {
                    fn join(&mut self) -> T {
                        match self {
                            Self::Wait(opt) => {
                                let t = opt.take().unwrap().join().unwrap(); // TODO: the last unwrap can panic
                                *self = Self::Finished(t.clone());
                                t
                            }
                            Self::Finished(t) => t.clone()
                        }
                    }
                }

                #(#nodes)*
            }
        };
        tokens.extend(ts);
    }
}

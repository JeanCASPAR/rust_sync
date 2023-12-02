use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};

use crate::{
    parser::{BaseType, MathBinOp, Type, Types},
    scheduler::{EqKind, Equation, Expr, ExprKind, Node, SIdent},
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

impl ToTokens for Type {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.base.to_tokens(tokens)
    }
}

struct WrapTypes<'a>(&'a Types);

impl ToTokens for WrapTypes<'_> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let types = self.0;
        tokens.extend(quote! {
            (#(#types),*,)
        })
    }
}

struct WrapEquations<'a, F> {
    equations: &'a [Equation],
    function: F,
}
impl<'a, F: Fn(&'a Equation, usize, &'_ mut TokenStream)> WrapEquations<'a, F> {
    fn new(equations: &'a [Equation], function: F) -> Self {
        Self {
            equations,
            function,
        }
    }
}

impl<'a, F: Fn(&'a Equation, usize, &'_ mut TokenStream)> ToTokens for WrapEquations<'a, F> {
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

impl ToTokens for SIdent {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self(i, j) = self;
        let var = format_ident!("tmp_{}", i);
        let j = syn::Index::from(*j);

        let ts = quote! {
            unsafe {
                *(#var.as_ptr()).#j
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
                        *(self.#cell.as_ptr()).0 // pre cells are always of size 1
                    }
                }
            }
            ExprKind::Then(e1, e2) => {
                quote! {
                    if self.counter == 0 {
                        #e1
                    } else {
                        self.counter -= 1;
                        let e = #e2;
                        self.counter += 1;
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
            ExprKind::BinOp(e1, op, e2) => {
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
                let e = &*e;
                quote! { (#e as f64) }
            }
            ExprKind::FunCall {
                function,
                arguments,
            } => {
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
        let name = format_ident!("Node{}", self.name);

        let fields_decl = WrapEquations::new(
            &self.equations,
            |eq: &Equation, _, tokens: &mut TokenStream| match eq.kind {
                EqKind::Expr(_) | EqKind::Input => (),
                EqKind::NodeCall { cell, .. } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = WrapTypes(&eq.types);

                    tokens.extend(quote! {
                        #field: ::std::box::Box<::std::mem::MaybeUninit<#ty>>,
                    });
                }
                EqKind::CellExpr(_, cell) => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = WrapTypes(&eq.types);

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
                EqKind::NodeCall { cell, .. } => {
                    let field = format_ident!("cell_{}", cell);
                    let ty = WrapTypes(&eq.types);

                    tokens.extend(quote! {
                        #field: ::std::box::Box::new(<#ty>::new()),
                    })
                }
                EqKind::CellExpr(_, cell) => {
                    let field = format_ident!("cell_{}", cell);

                    tokens.extend(quote! {
                        #field: ::std::mem::MaybeUninit::new_uninit(),
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

        let compute = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| {
                let active = eq.types.iter().flat_map(|ty| ty.clocks.iter()).fold(
                    quote! { true },
                    |acc, clock| {
                        let id = &clock.clock; // TODO: replace id by a SIdent
                        let pos = clock.positive;
                        quote! {
                            #acc && (#id == #pos)
                        }
                    },
                );

                let var = format_ident!("tmp_{}", i);
                let ty = WrapTypes(&eq.types);
                let ts = match &eq.kind {
                    EqKind::Input => {
                        assert_eq!(i, 0);
                        quote! {
                            input
                        }
                    }
                    EqKind::NodeCall { args, .. } => {
                        let node = format_ident!("cell_{}", i);
                        quote! {
                            self.#node.step(#(#args),*)
                        }
                    }
                    EqKind::Expr(e) | EqKind::CellExpr(e, _) => {
                        quote! {
                            #e
                        }
                    }
                };
                tokens.extend(quote! {
                    let #var: ::std::mem::MaybeUninit<#ty> = if #active {
                        ::std::mem::MaybeUninit::new(#ts)
                    } else {
                        ::std::mem::MaybeUninit::uninit();
                    }
                });
            },
        );

        let save_cells = WrapEquations::new(
            &self.equations,
            |eq: &Equation, i, tokens: &mut TokenStream| match &eq.kind {
                EqKind::NodeCall { cell, .. } => {
                    let var = format_ident!("var_{}", i);
                    let cell = format_ident!("cell_{}", cell);

                    let ts = quote! {
                        ::std::mem::swap(&mut *self.#cell, &mut #var);
                    };
                    tokens.extend(ts);
                }
                EqKind::CellExpr(_, cell) => {
                    let var = format_ident!("var_{}", i);
                    let cell = format_ident!("cell_{}", cell);

                    let ts = quote! {
                        ::std::mem::swap(&mut *self.#cell, &mut #var);
                    };
                    tokens.extend(ts);
                }
                _ => (),
            },
        );

        let input_types = WrapTypes(&self.params);
        let ret_types = WrapTypes(&self.ret_type);
        let ret = &self.ret_vars;

        let ts = quote! {
            pub struct #name {
                #fields_decl,
                counter: usize,
            }

            impl struct #name {
                fn new() -> Self {
                    Self {
                        #fields_init,
                        counter: 0,
                    }
                }

                fn reset(&mut self) {
                    #reset
                    self.counter = 0;
                }

                fn step(&mut self, input: #input_types) -> #ret_types {
                    #compute

                    #save_cells

                    (#(#ret,)*)
                }
            }
        };

        tokens.extend(ts);
    }
}

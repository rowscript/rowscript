use proc_macro::TokenStream;

use quote::quote;
use syn::{Data, DeriveInput, parse_macro_input};

enum Ret {
    Bool,
    Self_,
}

#[proc_macro_derive(Ops)]
pub fn derive_lint_items(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let Data::Enum(data) = input.data else {
        panic!("Expected enum type");
    };
    let impls = [
        (quote! { eq }, quote! { == }, Ret::Bool),
        (quote! { lt }, quote! { < }, Ret::Bool),
        (quote! { gt }, quote! { > }, Ret::Bool),
        (quote! { le }, quote! { <= }, Ret::Bool),
        (quote! { ge }, quote! { >= }, Ret::Bool),
        (quote! { add }, quote! { + }, Ret::Self_),
        (quote! { sub }, quote! { - }, Ret::Self_),
        (quote! { mul }, quote! { * }, Ret::Self_),
    ]
    .into_iter()
    .flat_map(|(f, op, ty)| {
        let arms = data.variants.iter().map(|v| {
            let ident = &v.ident;
            let ret = match ty {
                Ret::Bool => quote! { a #op b },
                Ret::Self_ => quote! { Self::#ident(a #op b) },
            };
            quote! { (Self::#ident(a), Self::#ident(b)) => #ret }
        });
        let ret = match ty {
            Ret::Bool => quote! { bool },
            Ret::Self_ => quote! { Self },
        };
        quote! {
            impl #name {
                pub fn #f(&self, other: &Self) -> #ret {
                    match (self, other) {
                        #(#arms,)*
                        ab => unreachable!("{ab:?}")
                    }
                }
            }
        }
    });
    quote! { #(#impls)* }.into()
}

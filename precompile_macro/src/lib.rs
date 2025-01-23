extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn precompile(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    // Extract the function's components
    let fn_name = &input.sig.ident;
    let fn_attrs = &input.attrs;
    let fn_vis = &input.vis;
    let fn_inputs = &input.sig.inputs;
    let fn_output = &input.sig.output;
    let fn_block = &input.block;

    // Create a new function name with the "autoprecompile_" prefix
    let new_fn_name = syn::Ident::new(&format!("autoprecompile_{fn_name}"), fn_name.span());

    // Extract parameter names (assumes the inputs are named parameters)
    let param_names = fn_inputs.iter().map(|arg| match arg {
        syn::FnArg::Typed(pat_type) => &pat_type.pat,
        syn::FnArg::Receiver(_) => panic!("Methods with `self` are not supported"),
    });

    // Generate the output
    let output = quote! {
        // Define the new function with the body of the original function
        #[no_mangle]
        #[inline(never)]
        fn #new_fn_name(#fn_inputs) #fn_output {
            #fn_block
        }

        // The original function now just calls the new function
        #(#fn_attrs)*
        #fn_vis fn #fn_name(#fn_inputs) #fn_output {
            #new_fn_name(#(#param_names),*)
        }
    };

    TokenStream::from(output)
}

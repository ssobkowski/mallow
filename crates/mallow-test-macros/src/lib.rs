use std::path::Path;

use proc_macro::TokenStream;
use quote::quote;
use syn::{
    FnArg, Ident, ItemFn, LitStr, Pat, ReturnType, Token, Type, parse::Parse, parse::ParseStream,
    parse_macro_input,
};

/// The arguments accepted by [`inference_test`].
struct InferenceTestArgs {
    /// The fixture name without its `.luau` extension.
    fixture: LitStr,
}

impl Parse for InferenceTestArgs {
    /// Parses the required `fixture = "name"` argument.
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        if name != "fixture" {
            return Err(syn::Error::new(name.span(), "expected `fixture = \"...\"`"));
        }

        input.parse::<Token![=]>()?;
        let fixture: LitStr = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("expected only `fixture = \"...\"`"));
        }

        Ok(Self { fixture })
    }
}

/// Creates an inference test backed by a Luau fixture.
///
/// The annotated function must take one `TypesView` parameter. The fixture is
/// loaded from `tests/inference-cases` in the package that contains the test.
#[proc_macro_attribute]
pub fn inference_test(args: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as InferenceTestArgs);
    let function = parse_macro_input!(item as ItemFn);

    match expand_inference_test(args, function) {
        Ok(output) => output.into(),
        Err(error) => error.into_compile_error().into(),
    }
}

/// Validates and expands one inference test function.
fn expand_inference_test(
    args: InferenceTestArgs,
    function: ItemFn,
) -> syn::Result<proc_macro2::TokenStream> {
    validate_fixture(&args.fixture)?;
    let parameter = validate_signature(&function)?;

    let ItemFn {
        attrs,
        vis,
        sig,
        block,
    } = function;
    let name = sig.ident;
    let fixture = args.fixture.value();
    let fixture_path = format!("/tests/inference-cases/{fixture}.luau");
    let fixture_doc = format!("Fixture: [`{fixture}.luau`](inference-cases/{fixture}.luau)");

    Ok(quote! {
        #(#attrs)*
        #[doc = #fixture_doc]
        #[test]
        #vis fn #name() {
            let #parameter: TypesView = crate::types_view(::std::path::Path::new(concat!(
                env!("CARGO_MANIFEST_DIR"),
                #fixture_path,
            )));
            #block
        }
    })
}

/// Checks that a fixture name is safe and exists in the calling package.
fn validate_fixture(fixture: &LitStr) -> syn::Result<()> {
    let name = fixture.value();
    if name.is_empty()
        || name == "."
        || name == ".."
        || name.contains('/')
        || name.contains('\\')
        || name.ends_with(".luau")
    {
        return Err(syn::Error::new(
            fixture.span(),
            "fixture must be a file stem without separators or a `.luau` extension",
        ));
    }

    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR").ok_or_else(|| {
        syn::Error::new(fixture.span(), "Cargo did not provide `CARGO_MANIFEST_DIR`")
    })?;
    let path = Path::new(&manifest_dir)
        .join("tests")
        .join("inference-cases")
        .join(format!("{name}.luau"));
    if !path.is_file() {
        return Err(syn::Error::new(
            fixture.span(),
            format!("inference fixture does not exist: {}", path.display()),
        ));
    }

    Ok(())
}

/// Checks that a test takes exactly one named `TypesView` parameter.
fn validate_signature(function: &ItemFn) -> syn::Result<Ident> {
    let sig = &function.sig;
    if sig.constness.is_some()
        || sig.asyncness.is_some()
        || sig.unsafety.is_some()
        || sig.abi.is_some()
        || !sig.generics.params.is_empty()
        || sig.generics.where_clause.is_some()
        || !matches!(sig.output, ReturnType::Default)
    {
        return Err(syn::Error::new_spanned(
            sig,
            "an inference test must be a plain function with no return type",
        ));
    }

    if sig.inputs.len() != 1 {
        return Err(syn::Error::new_spanned(
            &sig.inputs,
            "an inference test must take exactly one `TypesView` parameter",
        ));
    }
    let argument = sig.inputs.first().expect("one test argument was checked");
    let FnArg::Typed(argument) = argument else {
        return Err(syn::Error::new_spanned(
            argument,
            "an inference test cannot take a receiver",
        ));
    };
    let Pat::Ident(parameter) = argument.pat.as_ref() else {
        return Err(syn::Error::new_spanned(
            &argument.pat,
            "the `TypesView` parameter must be a simple identifier",
        ));
    };
    let Type::Path(parameter_type) = argument.ty.as_ref() else {
        return Err(syn::Error::new_spanned(
            &argument.ty,
            "the inference test parameter must have type `TypesView`",
        ));
    };
    if parameter_type.qself.is_some()
        || parameter_type.path.segments.len() != 1
        || parameter_type.path.segments[0].ident != "TypesView"
    {
        return Err(syn::Error::new_spanned(
            &argument.ty,
            "the inference test parameter must have type `TypesView`",
        ));
    }

    Ok(parameter.ident.clone())
}

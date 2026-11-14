//! Emitted Lean modules: their definitions and the functions the kernel
//! generates for reverse sites.

/// The definitions of an emitted Lean module in order, as `(name, text)`
/// pairs: each `def` runs to the next one, and the last to the end.
pub fn lean_definitions(source: &str) -> Vec<(&str, &str)> {
    let starts: Vec<usize> = source
        .match_indices("\ndef ")
        .map(|(at, _)| at + 1)
        .collect();
    starts
        .iter()
        .enumerate()
        .map(|(index, &start)| {
            let text = &source[start..starts.get(index + 1).copied().unwrap_or(source.len())];
            let name = text["def ".len()..].split([' ', '\n']).next().unwrap();
            (name, text)
        })
        .collect()
}
/// The id of a generated Lean function `f_<id>`.
pub fn lean_function_id(name: &str) -> Option<usize> {
    name.strip_prefix("f_")?.parse().ok()
}
/// Whether a definition of an emitted Lean module declares a literal that
/// its calls share: `basis_<k>`, `matrix_<k>`, `map_<k>` or `jacobian_<k>`.
pub fn lean_shared_literal(name: &str) -> bool {
    ["basis_", "matrix_", "map_", "jacobian_"]
        .iter()
        .any(|kind| {
            name.strip_prefix(kind)
                .is_some_and(|index| index.parse::<usize>().is_ok())
        })
}
/// The backward functions that the kernel generates for the reverse sites of
/// an emitted module (#623), given the number of source functions: the
/// definitions `f_<id>` with an id past every source function's. A module
/// declares its shared literals before its functions. The test fails unless
/// the generated functions come first among the functions.
#[track_caller]
pub fn generated_reverse_functions(source: &str, functions: usize) -> Vec<(&str, &str)> {
    let definitions = lean_definitions(source);
    let literals = definitions
        .iter()
        .take_while(|(name, _)| lean_shared_literal(name))
        .count();
    let definitions = &definitions[literals..];
    let generated = definitions
        .iter()
        .take_while(|(name, _)| lean_function_id(name).is_some_and(|id| id >= functions))
        .count();
    assert!(
        definitions[generated..]
            .iter()
            .all(|(name, _)| lean_function_id(name).is_none_or(|id| id < functions)),
        "generated functions must precede the source functions:\n{source}"
    );
    definitions[..generated].to_vec()
}

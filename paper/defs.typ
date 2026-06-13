// Shared helpers for the paper sections.
//
// `lean(name)` renders a Lean declaration name as inline code — the citation
// form for a mechanized claim. Every such name is resolvable in
// metatheory/Dregg2/ and `#assert_axioms`-pinned to the kernel triple
// {propext, Classical.choice, Quot.sound}.
#let lean(name) = raw(name)

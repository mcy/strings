# proc2decl

`proc2decl` exists for one reason only: because proc macros are a toxic
ecosystem.

Sometimes, you want to use an attribute to define a macro. Unfortunately,
Rust does not support declarative macros (also called macros-by-example)
for attributes, for reasons that essentially boil down to cookie-licking.

This crate exists for one purpose only, and that is ot facilitate writing
declarative macros that an attribute converts into.

## How Uo Use

1. Define the macro-by-example you wish to use as the main implementation of
   your attribute or derive.

2. Crate a proc-macro crate. This is where the documentation for your
   attribute will need to live. Your actual crate should depend on this
   crate.

3. Use `bridge!()` to define your bridge proc macros. These
   macro calls should be documented, since their doc comments are the ones
   that will appear in rustdoc for your macros.

4. `pub use` the macros in your actual crate.

Proc macros suck!

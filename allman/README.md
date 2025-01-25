# allman

`allman` - A code formatting and line reflowing toolkit. 🗒️🖋️

`allman::Doc` is a DOM-like structure that specifies how indentation,
like breaking, and reflowing should be handled. It is a tree of `Tag`s
that dictate layout information for the source code to format.

For example, the Allman brace style (for which this crate is named) can
be implemented as follows:

```rust
// flat: fn foo() { ... }
//
// broken:
// fn foo()
// {
//   // ...
// }
Doc::new()
  .tag("fn")
  .tag(Tag::Space)
  .tag("foo")
  .tag("(").tag(")")
  .tag_with(Tag::Group(40), |doc| {
    doc
      .tag_if(Tag::Space, If::Flat)
      .tag_if(Tag::Break(1), If::Broken)
      .tag("{")
      .tag_if(Tag::Space, If::Flat)
      .tag_if(Tag::Break(1), If::Broken)
      .tag_with(Tag::Indent(2), |doc| {
        // Brace contents here...
      })
      .tag_if(Tag::Space, If::Flat)
      .tag_if(Tag::Break(1), If::Broken)
      .tag("}");
  });
```

When calling `Doc::render()`, the layout algorithm will determine whether
`Tag::Group`s should be "broken", i.e., laid out with newlines inside.

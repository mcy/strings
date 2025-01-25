# gilded

`gilded` - Easy-peesy golden testing. 👑

## Why Golden Testing?

A "golden test" is a test that transforms data in some way, and validates it
by diffing it against an expected result: the "golden".

This is especially useful for testing scenarios that consume an input file
(say, a source code file, for testing a compiler) and generate structured,
diffable textual output (such as JSON or CSV data, or even a `Debug`).

Golden tests are best for cases where the output must be deterministic, and
where capturing fine-grained detail is valuable.

Because they simply compare the result to an expected value byte-for-byte,
changes can quickly regenerate the test output by using the output of the
test itself. Diffs can be examined in code review directly.

This crate also provides the `doc::Doc` type, enabling quick-and-dirty
construction of highly readable structured tree data for golden outputs.

## Defining a Test

A `gilded` test is defined like so:

```rust
#[gilded::test("testdata/**/*.txt")]
fn my_test(test: &gilded::Test) {
  // ...
}
```

`my_test` will be run as a separate unit test for every file (relative to
the crate root) which matches the glob passed to the attribute. The input
file's path and contents can be accessed through the `Test` accessors.

To specify golden outputs, use `Test::outputs()`. This specifies the
file extension for the golden, and its computed contents. The extension is
used to construct the path of the result. If the input is `foo/bar.txt`, and
the extension for this output is `csv`, the output will be read/written to
`foo/bar.csv`.

Panicking within the test body will fail the test as normal, tests should
not contain output assertions; those are handled by the framework.

## Generating Goldens

Once the test is created, simply set the `GILDED_REGENERATE` environment
variable: `GILDED_REGENERATE=1 cargo test`.

To regenerate a specific test, simply pass its name as a filter to the test.
See `cargo test -- --help` for available flags.`

Regenerating goldens will cause a `GILDED_CHANGED` file to be crated at the
crate root, which will cause all `gilded` tests in the crate to fail until
it is deleted. Deleting it forces the user to acknowledge that goldens have
been regenerated, to avoid blindly committing them.

## Known Issues

Golden tests can run under MIRI but have extremely large overhead. For the
time being, they are `#[cfg]`'d out in MIRI mode.

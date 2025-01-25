//! Implementation detail of `gilded`.

proc2decl::fs_bridge! {
  /// Turns a function into a golden test suite.
  ///
  /// See the [crate documentation][crate] for more information on how to use
  /// this attribute.
  ///
  /// [crate]: https://docs.rs/gilded
  macro #[test] => gilded::__test__;
}

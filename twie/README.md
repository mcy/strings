# twie

`twie` \[twaɪ\] - Fast, compressed prefix tries.

This crate provides a `Trie` type that implements an associative container
with slice-like keys. It has the following properties.

- Most one-shot operations are worst-case O(n), where n is the length of
  the key in bytes. This may require at most 2n tree hops, but the internal
  representation tries to minimize this where possible.

- Finding all prefixes of a string that are in the trie is also O(n). These
  prefixes are provided in order.

- Building a trie out of, e.g., an iterator is quadratic.

- Subtries of the whole trie (i.e. all entries with some particular prefix)
  can be operated on like regular tries (insertion is only supported from
  the root, unfortunately).

- Memory for storing keys is shared.

- The trie's internal indexing type is configurable, which allows trading
  off maximum key size for shrinking the size of tree nodes, and thus,
  memory usage.

```rust
let words = Trie::<str, i32>::from([
  ("poise", 0),
  ("poison", 1),
  ("poisonous", 2),
  ("poison #9", 3),
]);

assert_eq!(
  words.prefixes("poisonous snake").map(|(k, _)| k).collect::<Vec<_>>(),
  ["poison", "poisonous"],
)
```

use buf_trait::Buf;

use crate::raw::nodes::Index;
use crate::raw::nodes::Node;
use crate::raw::RawTrie;

/// A linked list of prefix chunks. This only exists so that subtries can
/// perform insertions, since they need to know the full prefix they were
/// constructed with.
///
/// However, this functionality is not fully implemented, although the concept
/// of a prefix is otherwise very convenient so this struct lives on.
#[derive(Copy, Clone)]
pub struct Prefix<'a> {
  prev: Option<&'a Prefix<'a>>,
  chunk: &'a [u8],
  // The length of the whole prefix, including `chunk`.
  len: usize,
  // This is a usize rather than an index because there is no way to specify
  // to the compiler that I is not interior-mutable, so we can't hold a
  // reference to it in const.
  node: usize,
}

impl<'a> Prefix<'a> {
  pub const ROOT: Prefix<'static> =
    Prefix { prev: None, chunk: b"", len: 0, node: 0 };

  /// Constructs a new prefix relative to `prefix`.
  ///
  /// It does so by starting from `prefix` and searching for each byte in
  /// `suffix` until it either runs out of `suffix` or the search bottoms out.
  ///
  /// It always returns a prefix that points to a subtrie where everything
  /// beneath it, including the current node, has `[prefix, suffix]` as a
  /// prefix.
  pub fn new<K: ?Sized + Buf, V, I: Index>(
    trie: &RawTrie<K, V, I>,
    prefix: &'a Prefix<'a>,
    suffix: &'a [u8],
  ) -> Self {
    let (mut node, rest) = trie.nodes.walk(prefix.node(), suffix);
    let depth = suffix.len() - rest.len();

    // If the search doesn't complete fully, we've either reached a leaf node
    // or children exist that are do not have `[prefix, suffix]` as a prefix.
    if !rest.is_empty() {
      match trie.nodes.get(node) {
        // If no node is here, there are children that do not have the desired
        // prefix, so this cannot be a valid subtrie.
        None => node = Node::EMPTY,

        Some(entry) => {
          // If we hit a node that contains something, it must contain `suffix`
          // as a prefix. This is because the subtrie represented by the new
          // prefix contains only things that contain the full thing we've
          // searched for as a prefix.
          //
          // This is specifically to guard against the case where we have a tree
          // that contains a key "foo", and we search for "foobar". We bottom
          // out at "foo", but should return empty because "foo" is not a prefix
          // of "foobar".
          //
          // However, if we search for "foo", we might bottom out at "f", due to
          // the leaf node optimization. So we can't simply check that `rest` is
          // empty.
          if let Some((k, _)) = trie.data.get(entry) {
            let key_rest = &k.as_bytes()[prefix.len() + depth..];
            if !key_rest.starts_with(rest) {
              node = Node::EMPTY;
            }
          }
        }
      }
    }

    Prefix {
      prev: Some(prefix).filter(|p| p.len() > 0),
      chunk: suffix,
      len: prefix.len() + suffix.len(),
      node: node.try_into().unwrap_or(usize::MAX),
    }
  }

  pub fn node<I: Index>(&self) -> Node<I> {
    self.node.try_into().unwrap_or(Node::EMPTY)
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn chunk(&self) -> &[u8] {
    self.chunk
  }

  pub fn prev(&self) -> Option<&Prefix> {
    self.prev
  }
}

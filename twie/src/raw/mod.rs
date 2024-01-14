// Core implementation of the trie.

use std::marker::PhantomData;

use buf_trait::Buf;

use crate::raw::entries::Entries;
use crate::raw::nodes::Index;
use crate::raw::nodes::Node;
use crate::raw::nodes::Nodes;
use crate::raw::nodes::OutOfIndices;

mod dump;
mod entries;

pub mod iter;
pub mod nodes;

pub use dump::dump;

/// The core trie implementation.
///
/// This type is a map from `[u8] -> Option<V>` backed by a [`Nodes`]. But, the
/// way this is realized is somewhat subtle. For a given key, call its
/// *canonical* location the node you'd get from `nodes.build(nodes.root(), key)`,
/// called `canon(key)`. We could put `key` at `canon(key)` and call it a day.
/// For a given node, we call the key that would be there `keyat(node)`.
///
/// This is wasteful: if the keys are `"foo"` and `"bar"`, there will be
/// seven full `[Node]`s in the trie:
///
/// ```text
/// <root> -> f -> o -> o
///        -> b -> a -> r
/// ```
///
/// However, these keys have no common prefix, so only the ->f and ->b links are
/// actually needed.
///
/// So, rather than say that `key` must be at `canon(key)`, instead we say that
/// for any given `node`, if there is an entry there, then:
///   - `node.key.starts_with(keyat(node))`
///   - At least one of `node.key == keyat(node)` OR `node` has no children.
///
/// This means that DFS-ing the trie still yields keys in lexicographic order.
///
/// It may be possible to reduce the last requirement to `node.key < all_its_children`.
/// This mostly preserves DFS behavior, but screws with subtries. It is unclear
/// if this can be made to work.
pub struct RawTrie<K: Buf + ?Sized, V, I: Index> {
  pub nodes: Nodes<I>,
  pub data: Entries<V, I>,
  pub _ph: PhantomData<fn(&mut Self) -> &mut K>,
}

impl<K: Buf + ?Sized, V: Clone, I: Index> Clone for RawTrie<K, V, I> {
  fn clone(&self) -> Self {
    Self {
      nodes: self.nodes.clone(),
      data: self.data.clone(),
      _ph: PhantomData,
    }
  }
}

impl<K: Buf + ?Sized, V, I: Index> RawTrie<K, V, I> {
  /// Creates a new trie.
  pub fn new() -> Self {
    Self {
      nodes: Nodes::new(),
      data: Entries::new(),
      _ph: PhantomData,
    }
  }

  /// Low-level mutation operation.
  ///
  /// This operation mutates the subtree pointed to by `root` (an index into
  /// `hi`) and a two-part key, and returns a possibly uninitialized entry
  /// for the key.
  ///
  /// After this function returns, an entry will exist for `[prefix, suffix]`.
  /// This makes this operation a fused find/insert operation.
  ///
  /// # Safety
  ///
  /// First, `root` must be a valid `hi` index. Then, `prefix` must be
  /// *exactly* the prefix string for the subtrie defined by `root`. The reason
  /// for the two-part key is that this allows mutation through a subtrie
  /// reference.
  pub unsafe fn mutate(
    &mut self,
    root: Node<I>,
    key: &[u8],
  ) -> Result<usize, OutOfIndices> {
    let insert_at = self.pre_mutate(root, key)?;

    if let Some(entry) = self.nodes.get(insert_at) {
      return Ok(entry);
    }

    let new = self.data.new_entry()?;
    self.nodes.set(insert_at, new);
    Ok(new)
  }

  /// Prepares for a mutation.
  ///
  /// This operation finds the slot at which it could place `suffix` and does
  /// so.
  pub unsafe fn pre_mutate(
    &mut self,
    root: Node<I>,
    key: &[u8],
  ) -> Result<Node<I>, OutOfIndices> {
    // Next, we want to walk down as far as we can without mutating anything.
    self.nodes.init_root();
    let (mut node, rest) = self.nodes.walk(root, key);
    let depth = node.depth;

    // We've hit a point at which we may need to create new nodes. Here's the
    // decision tree.
    //
    //   1. The value at `node` is `None`, Then, we insert at this spot.
    //
    //      This case also applies if `node` is not `None` but points at an
    //      empty slot, but since we don't support removal, this case cannot
    //      happen.
    //
    //   2. `node.key == key`. This means `key` is present. We are done.
    //
    //   3. Otherwise, we have to kick the thing in this slot one level down,
    //      andepth                             g
    //                                     |
    //                                    "fog"
    //
    //      Or, in the case that we're a prefix of the node we're replacing,
    //
    //      Before:             After:
    //
    //      "" -> f             "" -> f -> o -> o -> b
    //            |                             |    |
    //           "foobar"                       "foo"|
    //                                               "foobar"

    let idx = self.nodes.get(node);

    let lookup = idx.and_then(|e| self.data.get(e).map(|(k, _)| (e, k)));
    let Some((entry, key_len)) = lookup else {
      // Case 1.
      if let [next, rest @ ..] = rest {
        node = self.nodes.build(node, &[*next])?;
        self.nodes.extend_key(node, rest);
      }
      return Ok(node);
    };

    let key_rest = &self.nodes.key(node, Some(key_len))[depth..];
    if key_rest == rest {
      // Case 2.
      return Ok(node);
    }

    // Case 3.
    let common_prefix = key_rest
      .iter()
      .zip(rest)
      .take_while(|(a, b)| a == b)
      .count();

    self.nodes.clear(node);
    node = self.nodes.build(node, &rest[..common_prefix])?;
    let build_from = node;

    // Need to recompute key_rest here to make the borrow checker happy.
    let key_rest = &self.nodes.key(node, Some(key_len))[depth..];

    // Note that because the keys are distinct, `key_rest.len() > common_prefix`.
    if let Some(&next) = key_rest.get(common_prefix) {
      let move_to = self.nodes.build(node, &[next])?;
      self.nodes.set(move_to, entry);
      // Don't need to call extend_key() here; by construction, the key at
      // the moved node is already long enough.
    } else {
      self.nodes.set(node, entry);
    }

    if let [next, rest @ ..] = &rest[common_prefix..] {
      node = self.nodes.build(build_from, &[*next])?;
      self.nodes.extend_key(node, rest);
    };

    Ok(node)
  }
}

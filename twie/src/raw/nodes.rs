use std::fmt;
use std::mem;

use crate::sealed::Seal;

/// The core "trie" part of the trie/map combo.
///
/// At its core, it's a `[u8] -> usize` map implemented as a radix tree with a
/// base of 16; in other words, each byte in a key is split into nybbles, which
/// are the indices of children on each node of the underlying 16-tree.
#[derive(Debug, Clone)]
pub struct Nodes<I: Index> {
  // This part is the actual trie. Each element of `lo` is indexed on the
  // low nybble of a byte, and the values in the array point to elements of
  // `hi`. It points back to `hi` in the same way.`
  lo: Vec<[Node<I>; 16]>,
  hi: Vec<[Node<I>; 16]>,

  // The values at each node; this is co-indexed with `hi`. If the value is
  // `I::EMPTY`, then it's an unoccupied slot.
  sparse: Vec<Node<I>>,
}

impl<I: Index> Nodes<I> {
  pub fn new() -> Self {
    Self {
      lo: Vec::new(),
      hi: Vec::new(),
      sparse: Vec::new(),
    }
  }

  /// Gets the value at `node`.
  pub fn get(&self, node: Node<I>) -> Option<usize> {
    self.sparse[node.idx()].try_into().ok()
  }

  /// Sets the value at `node`; returns the old value, if one was there.
  pub fn set(&mut self, node: Node<I>, value: usize) -> Option<usize> {
    let prev = self.get(node);
    self.sparse[node.idx()] = Node::must(value);
    prev
  }

  /// Clears the value at `node`; returns the old value, if one was there.
  pub fn clear(&mut self, node: Node<I>) -> Option<usize> {
    let prev = self.get(node);
    self.sparse[node.idx()] = Node::EMPTY;
    prev
  }

  /// Returns internal trie state. Only used by dump.rs.
  pub fn lo(&self, node: Node<I>) -> &[Node<I>] {
    &self.lo[node.idx()]
  }

  /// Returns internal trie state. Only used by dump.rs.
  pub fn hi(&self, node: Node<I>) -> &[Node<I>] {
    &self.hi[node.idx()]
  }

  /// Returns whether `node` is a leaf node (i.e, no children, occupied or
  /// otherwise).
  pub fn is_leaf(&self, node: Node<I>) -> bool {
    self.hi[node.idx()].iter().all(|n| n.is_empty())
  }

  /// Returns an iterator over the prefixes of a two-part key at the given
  /// root.
  pub fn prefixes<'key>(
    &self,
    node: Node<I>,
    suffix: &'key [u8],
  ) -> Prefixes<'_, 'key, I> {
    Prefixes {
      nodes: self,
      path: suffix,
      node: if self.sparse.is_empty() {
        Node::EMPTY
      } else {
        node
      },
    }
  }

  /// Returns an iterator over the prefixes of a two-part key at the given
  /// root.
  pub fn dfs(&self, node: Node<I>) -> Dfs<'_, I> {
    Dfs {
      nodes: self,
      path: if node.is_empty() || self.sparse.is_empty() {
        Vec::new()
      } else {
        vec![(node, None)]
      },
    }
  }

  /// Returns true if `byte` is definitely smaller than all other values out
  /// of this node. May returns false negatives.
  #[allow(dead_code)]
  pub fn would_be_min(&self, node: Node<I>, byte: u8) -> bool {
    let lo = (byte >> 4) as usize;
    let hi = (byte >> 4) as usize;
    for &i in &self.hi[node.idx()][..hi] {
      if !i.is_empty() {
        return false;
      }
    }

    let lo_idx = self.hi[node.idx()][hi];
    if lo_idx.is_empty() {
      return true;
    }

    for &i in &self.lo[lo_idx.idx()][..=lo] {
      if !i.is_empty() {
        return false;
      }
    }

    true
  }

  /// Advances down the trie from `start`, one byte from `bytes` at a time.
  ///
  /// Once either `bytes` or the path in the trie bottom out, returns the
  /// furthest node reached and whatever portion of `bytes` wasn't consumed.
  ///
  /// Never returns empty, unless `start` is empty.
  pub fn walk<'a>(
    &self,
    mut start: Node<I>,
    bytes: &'a [u8],
  ) -> (Node<I>, &'a [u8]) {
    if self.sparse.is_empty() || start.is_empty() {
      return (start, bytes);
    }

    let depth = bytes
      .iter()
      .take_while(|&&byte| {
        let lo = (byte & 0xf) as usize;
        let hi = (byte >> 4) as usize;

        let lo_idx = self.hi[start.idx()][hi];
        if lo_idx.is_empty() {
          return false;
        }

        let hi_idx = self.lo[lo_idx.idx()][lo];
        if hi_idx.is_empty() {
          return false;
        }

        start = hi_idx;

        true
      })
      .count();

    (start, &bytes[depth..])
  }

  /// Initializes the root node, if necessary.
  pub fn init_root(&mut self) {
    if self.hi.is_empty() {
      self.hi.push([Node::EMPTY; 16]);
      self.sparse.push(Node::EMPTY);
    }
  }

  /// Advances down the trie from `start`, adding nodes as necessary.
  ///
  /// If `start` corresponds to a string `"foo"`, and `bytes` is `"bar"`, then
  /// the resulting output node will correspond to `"foobar"`.
  ///
  /// Returns an error if we run of indices.
  pub fn build(
    &mut self,
    start: Node<I>,
    bytes: &[u8],
  ) -> Result<Node<I>, OutOfIndices> {
    self.build_while(start, bytes, |_, _, _| true)
  }

  /// Like build, but runs `pred` on the current node and the byte to build
  /// at it before digging any deeper.
  pub fn build_while(
    &mut self,
    mut start: Node<I>,
    bytes: &[u8],
    mut pred: impl FnMut(&mut Self, Node<I>, u8) -> bool,
  ) -> Result<Node<I>, OutOfIndices> {
    self.init_root();

    for &byte in bytes {
      if !pred(self, start, byte) {
        break;
      }

      let lo = (byte & 0xf) as usize;
      let hi = (byte >> 4) as usize;

      let lo_idx = &mut self.hi[start.idx()][hi];
      if lo_idx.is_empty() {
        *lo_idx = self.lo.len().try_into()?;
        self.lo.push([Node::EMPTY; 16]);
      }

      let hi_idx = &mut self.lo[lo_idx.idx()][lo];
      if hi_idx.is_empty() {
        *hi_idx = self.hi.len().try_into()?;
        self.hi.push([Node::EMPTY; 16]);
        self.sparse.push(Node::EMPTY);
      }

      start = *hi_idx;
    }

    Ok(start)
  }
}

/// A node from [`Nodes`].
#[derive(Copy, Clone)]
pub struct Node<I: Index>(I);

impl<I: Index> Node<I> {
  pub const ROOT: Self = Self(I::ROOT);
  pub const EMPTY: Self = Self(I::EMPTY);

  pub fn is_empty(self) -> bool {
    self.0 == I::EMPTY
  }

  pub fn or_empty(self) -> Option<Self> {
    Some(self).filter(|n| !n.is_empty())
  }

  pub fn idx(self) -> usize {
    usize::try_from(self).expect(
      "twie: internal function seems to have run out of indices; this is a bug",
    )
  }

  pub fn must(idx: usize) -> Self {
    Self::try_from(idx).expect(
      "twie: internal function seems to have run out of indices; this is a bug",
    )
  }
}

impl<I: Index + fmt::Debug> fmt::Debug for Node<I> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Debug::fmt(&self.0, f)
  }
}

/// An iterator over prefixes of a string. This returns indices into the
/// sparse vector, which need to be resolved with respect to the full tri
/// structure.
pub struct Prefixes<'a, 'key, I: Index> {
  nodes: &'a Nodes<I>,
  path: &'key [u8],
  node: Node<I>,
}

impl<I: Index> Iterator for Prefixes<'_, '_, I> {
  // The last value is whether this is a leaf node: true if it's a leaf, or if
  // the path was fully consumed. In other words, it indicates that the iterator
  // is done yielding.
  type Item = (Node<I>, Option<usize>, bool);

  fn next(&mut self) -> Option<Self::Item> {
    if self.node.is_empty() {
      return None;
    }

    if self.path.is_empty() {
      let node = mem::replace(&mut self.node, Node::EMPTY);
      return Some((node, self.nodes.get(node), true));
    }

    let step;
    (step, self.path) = self.path.split_at(1);

    let (node, rest) = self.nodes.walk(self.node, step);
    let node = mem::replace(&mut self.node, node);
    if !rest.is_empty() {
      self.node = Node::EMPTY;
    }

    Some((node, self.nodes.get(node), self.node.is_empty()))
  }
}

/// A DFS-order iterator over all elements in the trie. `path` must be
/// pre-seeded with the value `vec![(root, None)]`
pub struct Dfs<'a, I: Index> {
  nodes: &'a Nodes<I>,
  path: Vec<(Node<I>, Option<u8>)>,
}

impl<I: Index> Iterator for Dfs<'_, I> {
  type Item = Option<usize>;

  fn next(&mut self) -> Option<Self::Item> {
    while let Some((node, byte)) = self.path.last_mut() {
      loop {
        let Some(next) = byte else {
          let node = *node;
          if self.nodes.is_leaf(node) {
            self.path.pop();
          } else {
            *byte = Some(0);
          }
          return Some(self.nodes.sparse[node.idx()].try_into().ok());
        };

        let Some(next) = next.checked_add(1) else {
          self.path.pop();
          break;
        };

        let lo = next & 0xf;
        let hi = next >> 4;
        *byte = Some(next);

        let lo_idx = self.nodes.hi[node.idx()][hi as usize];
        if lo_idx.is_empty() {
          // Skip over all bytes with this high nybble.
          *byte = Some(hi << 4 | 0xf);
          continue;
        }

        let hi_idx = self.nodes.lo[lo_idx.idx()][lo as usize];
        if hi_idx.is_empty() {
          continue;
        }

        self.path.push((hi_idx, None));
        break;
      }
    }

    None
  }
}

/// Indicates that a [`Trie`][crate::Trie] ran out of internal indices.
#[derive(Debug, Clone)]
pub struct OutOfIndices(());

impl<I: Index> TryFrom<Node<I>> for usize {
  type Error = OutOfIndices;
  fn try_from(node: Node<I>) -> Result<usize, Self::Error> {
    I::to_usize(node.0, Seal)
  }
}

impl<I: Index> TryFrom<usize> for Node<I> {
  type Error = OutOfIndices;
  fn try_from(idx: usize) -> Result<Self, Self::Error> {
    I::from_usize(idx, Seal).map(Node)
  }
}

/// A type usable as the internal index parameter of a [`Trie`][crate::Trie].
pub trait Index: fmt::Debug + Copy + Eq + 'static {
  #[doc(hidden)]
  const ROOT: Self;
  #[doc(hidden)]
  const EMPTY: Self;
  #[doc(hidden)]
  fn from_usize(idx: usize, _: Seal) -> Result<Self, OutOfIndices>;
  #[doc(hidden)]
  fn to_usize(self, _: Seal) -> Result<usize, OutOfIndices>;
}

macro_rules! impl_length {
  ($($ty:ty),*) => {$(
    impl Index  for $ty {
      const ROOT: Self = <$ty>::MIN;
      const EMPTY: Self = <$ty>::MAX;
      fn from_usize(idx: usize, _: Seal) -> Result<Self, OutOfIndices> {
        let value = Self::try_from(idx).map_err(|_| OutOfIndices(()))?;
        match value {
          <$ty>::MAX => Err(OutOfIndices(())),
          _ => Ok(value),
        }
      }
      fn to_usize(self, _: Seal) -> Result<usize, OutOfIndices> {
        match self {
          <$ty>::MAX => Err(OutOfIndices(())),
          _ => usize::try_from(self).map_err(|_| OutOfIndices(())),
        }
      }
    }
  )*}
}
impl_length!(u8, u16, u32, u64, usize);

use std::collections::VecDeque;
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
  lo: Vec<[Ptr<I>; 16]>,
  hi: Vec<[Ptr<I>; 16]>,

  // The values at each node; this is co-indexed with `hi`. If the value is
  // `I::EMPTY`, then it's an unoccupied slot.
  sparse: Vec<Ptr<I>>,
  // The full contiguous key for each node, co-indexed with `hi`.
  //
  // Keys may be "overlong", which means they are longer than the node is deep
  // into the trie. The "true" length of the key is equal to the depth into the
  // trie. If a key for a node is `None`, that means it re-uses its parent's key
  // for itself (again, the length is implicit).
  keys: Vec<Option<Vec<u8>>>,
}

impl<I: Index> Nodes<I> {
  pub fn new() -> Self {
    Self {
      lo: Vec::new(),
      hi: Vec::new(),
      sparse: Vec::new(),
      keys: Vec::new(),
    }
  }

  /// Gets the value at `node`.
  pub fn get(&self, node: Node<I>) -> Option<usize> {
    self.sparse[node.ptr.idx()].try_into().ok()
  }

  /// Gets the key for `node`, with an optional overlong length.
  pub fn key(&self, node: Node<I>, len: Option<usize>) -> &[u8] {
    let key = self.keys[node.key.idx()]
      .as_ref()
      .expect("twie: key pointer pointed to a null key; this is a bug");

    if len == Some(usize::MAX) {
      return key;
    }

    &key[..len.unwrap_or(node.depth)]
  }

  /// Extends a the key for `Node` by the given text.
  pub fn extend_key(&mut self, node: Node<I>, data: &[u8]) {
    let key = self.keys[node.key.idx()]
      .as_mut()
      .expect("twie: key pointer pointed to a null key; this is a bug");

    debug_assert!(key.len() == node.depth, "attempted to overwrite shared key");
    key.extend_from_slice(data);
  }

  /// Sets the value at `node`; returns the old value, if one was there.
  pub fn set(&mut self, node: Node<I>, value: usize) -> Option<usize> {
    let prev = self.get(node);
    self.sparse[node.ptr.idx()] = Ptr::must(value);
    prev
  }

  /// Clears the value at `node`; returns the old value, if one was there.
  pub fn clear(&mut self, node: Node<I>) -> Option<usize> {
    let prev = self.get(node);
    self.sparse[node.ptr.idx()] = Ptr::EMPTY;
    prev
  }

  /// Returns internal trie state. Only used by dump.rs.
  pub fn lo(&self, ptr: Ptr<I>, hi: u8) -> &[Ptr<I>] {
    let lo_idx = &self.hi[ptr.idx()][hi as usize];
    &self.lo[lo_idx.idx()]
  }

  /// Returns internal trie state. Only used by dump.rs.
  pub fn hi(&self, ptr: Ptr<I>) -> &[Ptr<I>] {
    &self.hi[ptr.idx()]
  }

  /// Returns whether `node` is a leaf node (i.e, no children, occupied or
  /// otherwise).
  pub fn is_leaf(&self, node: Ptr<I>) -> bool {
    self.hi[node.idx()].iter().all(|n| n.is_empty())
  }

  /// Returns an iterator over the prefixes of a two-part key at the given
  /// root.
  pub fn prefixes<'key>(
    &self,
    mut node: Node<I>,
    suffix: &'key [u8],
  ) -> Prefixes<'_, 'key, I> {
    if self.sparse.is_empty() {
      node.ptr = Ptr::EMPTY;
    }

    Prefixes { nodes: self, path: suffix, node }
  }

  /// Returns an iterator over the nodes in the trie in DFS order.
  pub fn dfs(&self, node: Node<I>) -> Dfs<I> {
    Dfs {
      nodes: self,
      overlong: None,
      path: if node.is_empty() || self.sparse.is_empty() {
        Vec::new()
      } else {
        vec![(node, None)]
      },
    }
  }

  /// Returns an iterator over the nodes in the trie in BFS order.
  #[allow(unused)]
  pub fn bfs(&self, node: Node<I>) -> Bfs<I> {
    Bfs {
      nodes: self,
      queue: VecDeque::from([node]),
      next: None,
    }
  }

  /// Returns true if `byte` is definitely smaller than all other values out
  /// of this ptr. May returns false negatives.
  #[allow(dead_code)]
  pub fn would_be_min(&self, ptr: Ptr<I>, byte: u8) -> bool {
    let lo = (byte >> 4) as usize;
    let hi = (byte >> 4) as usize;
    for &i in &self.hi[ptr.idx()][..hi] {
      if !i.is_empty() {
        return false;
      }
    }

    let lo_idx = self.hi[ptr.idx()][hi];
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
  /// furthest ptr reached and whatever portion of `bytes` wasn't consumed.
  ///
  /// Never returns empty, unless `start` is empty.
  pub fn walk<'a>(
    &self,
    mut start: Node<I>,
    bytes: &'a [u8],
  ) -> (Node<I>, &'a [u8]) {
    if self.sparse.is_empty() || start.ptr.is_empty() {
      return (start, bytes);
    }

    let depth = bytes
      .iter()
      .take_while(|&&byte| {
        let lo = (byte & 0xf) as usize;
        let hi = (byte >> 4) as usize;

        let lo_idx = self.hi[start.ptr.idx()][hi];
        if lo_idx.is_empty() {
          return false;
        }

        let hi_idx = self.lo[lo_idx.idx()][lo];
        if hi_idx.is_empty() {
          return false;
        }

        start.ptr = hi_idx;
        start.depth += 1;
        if self.keys[hi_idx.idx()].is_some() {
          start.key = hi_idx
        }

        true
      })
      .count();
    (start, &bytes[depth..])
  }

  /// Initializes the root ptr, if necessary.
  pub fn init_root(&mut self) {
    if self.hi.is_empty() {
      self.hi.push([Ptr::EMPTY; 16]);
      self.sparse.push(Ptr::EMPTY);
      self.keys.push(Some(Vec::new()));
    }
  }

  /// Advances down the trie from `start`, adding nodes as necessary.
  ///
  /// If `start` corresponds to a string `"foo"`, and `bytes` is `"bar"`, then
  /// the resulting output ptr will correspond to `"foobar"`.
  ///
  /// Returns an error if we run of indices.
  pub fn build(
    &mut self,
    start: Node<I>,
    bytes: &[u8],
  ) -> Result<Node<I>, OutOfIndices> {
    self.build_while(start, bytes, |_, _, _| true)
  }

  /// Like build, but runs `pred` on the current ptr and the byte to build
  /// at it before digging any deeper.
  pub fn build_while(
    &mut self,
    mut start: Node<I>,
    bytes: &[u8],
    mut pred: impl FnMut(&mut Self, Node<I>, u8) -> bool,
  ) -> Result<Node<I>, OutOfIndices> {
    self.init_root();

    let mut key = None;
    for &byte in bytes {
      if !pred(self, start, byte) {
        break;
      }

      let lo = (byte & 0xf) as usize;
      let hi = (byte >> 4) as usize;

      let mut lo_idx = self.hi[start.ptr.idx()][hi];
      if lo_idx.is_empty() {
        lo_idx = self.lo.len().try_into()?;
        self.hi[start.ptr.idx()][hi] = lo_idx;
        self.lo.push([Ptr::EMPTY; 16]);
      }

      let mut hi_idx = self.lo[lo_idx.idx()][lo];
      if hi_idx.is_empty() {
        hi_idx = self.hi.len().try_into()?;
        self.lo[lo_idx.idx()][lo] = hi_idx;
        self.hi.push([Ptr::EMPTY; 16]);
        self.sparse.push(Ptr::EMPTY);
        self.keys.push(None);

        match &mut key {
          None => {
            let k = self.keys[start.key.idx()].as_mut().unwrap();
            if let Some([prefix @ .., last]) = k.get(..=start.depth) {
              if *last != byte {
                start.key = hi_idx;
                let mut k = prefix.to_vec();
                k.push(byte);
                key = Some(k);
              }
            } else {
              let mut k = mem::take(k);
              k.push(byte);
              key = Some(k);
            }
          }
          Some(k) => k.push(byte),
        };
      } else if self.keys[hi_idx.idx()].is_some() {
        start.key = hi_idx;
      }

      start.ptr = hi_idx;
      start.depth += 1;
    }

    if let Some(key) = key {
      self.keys[start.key.idx()] = Some(key);
    }

    Ok(start)
  }
}

/// A node inside of a [`Nodes`]
#[derive(Copy, Clone)]
pub struct Node<I: Index> {
  pub ptr: Ptr<I>,
  pub key: Ptr<I>,
  pub depth: usize,
}

/// A compressed pointer. This is used inside of [`Nodes`] and some other
/// places.
#[derive(Copy, Clone)]
pub struct Ptr<I: Index>(pub I);

impl<I: Index> Node<I> {
  pub const ROOT: Self = Self {
    ptr: Ptr(I::ROOT),
    key: Ptr(I::ROOT),
    depth: 0,
  };

  pub const EMPTY: Self = Self {
    ptr: Ptr::EMPTY,
    key: Ptr::EMPTY,
    depth: !0,
  };

  pub fn is_empty(self) -> bool {
    self.ptr.is_empty()
  }
}

impl<I: Index> Ptr<I> {
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
    if self.ptr.0 != self.key.0 {
      write!(f, "Node({:?}/{:?}, {})", self.ptr, self.key, self.depth)
    } else {
      write!(f, "Node({:?}, {})", self.ptr, self.depth)
    }
  }
}

impl<I: Index + fmt::Debug> fmt::Debug for Ptr<I> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt::Debug::fmt(&self.0, f)
  }
}

/// An iterator over prefixes of a string. This returns indices into the
/// sparse vector, which need to be resolved with respect to the full tri
/// structure.
pub struct Prefixes<'a, 'key, I: Index> {
  pub nodes: &'a Nodes<I>,
  path: &'key [u8],
  node: Node<I>,
}

impl<I: Index> Iterator for Prefixes<'_, '_, I> {
  // The last value is whether this is a leaf ptr: true if it's a leaf, or if
  // the path was fully consumed. In other words, it indicates that the iterator
  // is done yielding.
  type Item = (Node<I>, Option<usize>, bool);

  fn next(&mut self) -> Option<Self::Item> {
    if self.node.ptr.is_empty() {
      return None;
    }

    if self.path.is_empty() {
      let node = self.node;
      self.node.ptr = Ptr::EMPTY;
      return Some((node, self.nodes.get(node), true));
    }

    let step;
    (step, self.path) = self.path.split_at(1);

    let (node, rest) = self.nodes.walk(self.node, step);
    let node = mem::replace(&mut self.node, node);
    if !rest.is_empty() {
      self.node.ptr = Ptr::EMPTY;
    }

    Some((node, self.nodes.get(node), self.node.ptr.is_empty()))
  }
}

/// A DFS-order iterator over all elements in the trie. `path` must be
/// pre-seeded with the value `vec![(root, None)]`
pub struct Dfs<'a, I: Index> {
  pub nodes: &'a Nodes<I>,
  path: Vec<(Node<I>, Option<u8>)>,
  overlong: Option<(Node<I>, usize)>,
}

impl<I: Index> Iterator for Dfs<'_, I> {
  type Item = Node<I>;

  fn next(&mut self) -> Option<Self::Item> {
    if let Some((node, remaining)) = &mut self.overlong {
      node.depth += 1;
      let next = *node;
      *remaining -= 1;
      if *remaining == 0 {
        self.overlong = None;
      }

      return Some(next);
    }

    while let Some((node, byte)) = self.path.last_mut() {
      loop {
        let Some(next) = byte else {
          let node = *node;
          let is_leaf = self.nodes.is_leaf(node.ptr);
          if is_leaf {
            self.path.pop();
          } else {
            *byte = Some(0);
          }

          if is_leaf {
            let key = self.nodes.key(node, Some(usize::MAX));
            if key.len() > node.depth {
              self.overlong = Some((node, key.len() - node.depth))
            }
          }

          return Some(node);
        };

        let Some(next) = next.checked_add(1) else {
          self.path.pop();
          break;
        };

        let lo = next & 0xf;
        let hi = next >> 4;
        *byte = Some(next);

        let lo_idx = self.nodes.hi[node.ptr.idx()][hi as usize];
        if lo_idx.is_empty() {
          // Skip over all bytes with this high nybble.
          *byte = Some(hi << 4 | 0xf);
          continue;
        }

        let hi_idx = self.nodes.lo[lo_idx.idx()][lo as usize];
        if hi_idx.is_empty() {
          continue;
        }

        let next = Node {
          ptr: hi_idx,
          key: match self.nodes.keys[hi_idx.idx()] {
            Some(..) => hi_idx,
            None => node.key,
          },
          depth: node.depth + 1,
        };
        self.path.push((next, None));
        break;
      }
    }

    None
  }
}

/// A BFS-order iterator over all elements in the trie. `queue` must be seeded
/// with the root.
pub struct Bfs<'a, I: Index> {
  pub nodes: &'a Nodes<I>,
  queue: VecDeque<Node<I>>,
  next: Option<u8>,
}

impl<I: Index> Iterator for Bfs<'_, I> {
  type Item = Node<I>;

  fn next(&mut self) -> Option<Self::Item> {
    while let Some(node) = self.queue.front() {
      let Some(next) = self.next else {
        self.next = Some(0);
        return Some(*node);
      };

      let Some(next) = next.checked_add(1) else {
        self.next = None;
        self.queue.pop_front();
        continue;
      };

      let lo = next & 0xf;
      let hi = next >> 4;
      self.next = Some(next);

      let lo_idx = self.nodes.hi[node.ptr.idx()][hi as usize];
      if lo_idx.is_empty() {
        // Skip over all bytes with this high nybble.
        self.next = Some(hi << 4 | 0xf);
        continue;
      }

      let hi_idx = self.nodes.lo[lo_idx.idx()][lo as usize];
      if hi_idx.is_empty() {
        continue;
      }

      self.queue.push_back(Node {
        ptr: hi_idx,
        key: match self.nodes.keys[hi_idx.idx()] {
          Some(..) => hi_idx,
          None => node.key,
        },
        depth: node.depth + 1,
      });
    }

    None
  }
}

/// Indicates that a [`Trie`][crate::Trie] ran out of internal indices.
#[derive(Debug, Clone)]
pub struct OutOfIndices(());

impl<I: Index> TryFrom<Ptr<I>> for usize {
  type Error = OutOfIndices;
  fn try_from(ptr: Ptr<I>) -> Result<usize, Self::Error> {
    I::to_usize(ptr.0, Seal)
  }
}

impl<I: Index> TryFrom<usize> for Ptr<I> {
  type Error = OutOfIndices;
  fn try_from(idx: usize) -> Result<Self, Self::Error> {
    I::from_usize(idx, Seal).map(Ptr)
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

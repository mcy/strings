//! A trie data structure for searching for the best matching prefix among
//! a set of rules.

use std::cell::Cell;
use std::fmt;
use std::iter;
use std::mem;

use byteyarn::Yarn;

const EMPTY: u32 = u32::MAX;

/// An radix prefix trie, optimized for searching for known prefixes of a
/// string.
///
/// Elements can only be added to the trie, never removed.
pub struct Trie<V> {
  hi_nodes: Vec<[u32; 0x10]>,
  lo_nodes: Vec<[u32; 0x10]>,
  sparse: Vec<u32>,
  values: Vec<(Yarn, V)>,
}

impl<V> Trie<V> {
  /// Constructs a new, empty trie.
  pub fn new() -> Self {
    Trie {
      hi_nodes: Vec::new(),
      lo_nodes: Vec::new(),
      sparse: Vec::new(),
      values: Vec::new(),
    }
  }

  /// Gets a value, or inserts a new value (and gets it).
  pub fn get_or_insert(
    &mut self,
    key: Yarn,
    default: impl FnOnce() -> V,
  ) -> (&Yarn, &mut V) {
    self.insert_or_update(key, default, |_| {})
  }

  /// Inserts a new value into the trie.
  ///
  /// If the value was already present, it is returned.
  pub fn insert(&mut self, key: Yarn, value: V) -> (&Yarn, &mut V, Option<V>) {
    let value = Cell::new(Some(value));
    let (k, v) = self.insert_or_update(
      key,
      || value.take().unwrap(),
      |v| {
        let old = mem::replace(v, value.take().unwrap());
        value.set(Some(old));
      },
    );
    (k, v, value.take())
  }

  /// Inserts a new value into the trie.
  ///
  /// If the value is not present, `default()` is called to construct it.
  /// If the value is already present, `update` is called to update it.
  pub fn insert_or_update(
    &mut self,
    key: Yarn,
    default: impl FnOnce() -> V,
    update: impl FnOnce(&mut V),
  ) -> (&Yarn, &mut V) {
    if self.hi_nodes.is_empty() {
      self.hi_nodes.push([EMPTY; 16]);
      self.sparse.push(EMPTY);
    }

    let mut idx = 0;
    for byte in key.as_bytes() {
      let lo = (byte & 0xf) as usize;
      let hi = (byte >> 4) as usize;

      let lo_idx = &mut self.hi_nodes[idx][hi];
      if *lo_idx == EMPTY {
        *lo_idx = self.lo_nodes.len() as u32;
        self.lo_nodes.push([EMPTY; 16]);
      }

      let new_idx = &mut self.lo_nodes[*lo_idx as usize][lo];
      if *new_idx == EMPTY {
        *new_idx = self.hi_nodes.len() as u32;
        self.hi_nodes.push([EMPTY; 16]);
        self.sparse.push(EMPTY);
      }

      idx = *new_idx as usize;
    }

    let sparse = match self.sparse[idx] {
      EMPTY => {
        let sparse = self.values.len() as u32;

        self.values.push((key, default()));
        self.sparse[idx] = sparse;
        sparse
      }
      n => {
        update(&mut self.values[n as usize].1);
        n
      }
    };

    let pair = &mut self.values[sparse as usize];
    (&pair.0, &mut pair.1)
  }

  /// Constructs a subtrie consisting of those keys which have `prefix` as a
  /// prefix.
  ///
  /// `trie.subtrie("")` will cheaply view this trie as the trivial subtrie.
  #[inline(always)]
  pub fn subtrie(&self, prefix: &str) -> Subtrie<V> {
    Subtrie {
      trie: self,
      root: 0,
    }
    .subtrie(prefix)
  }

  /// Looks up `key` in this trie, returning the corresponding value if it
  /// is present.
  #[allow(unused)]
  pub fn get(&self, key: &str) -> Option<&V> {
    let idx = self
      .subtrie("")
      .prefix_nodes_of(key)
      .last()
      .filter(|&idx| idx != EMPTY)?;
    let sparse = self.sparse[idx as usize];
    if sparse == EMPTY {
      return None;
    }

    Some(&self.values[sparse as usize].1)
  }

  /// Returns an iterator over the elements of this trie.
  ///
  /// Guaranteed to traverse keys in sorted order.
  #[allow(unused)]
  pub fn iter(&self) -> impl Iterator<Item = (&Yarn, &V)> {
    self.subtrie("").iter()
  }

  /// Returns an iterator over keys in this trie that are prefixes of `key`.
  #[allow(unused)]
  pub fn prefixes_of<'a: 'b, 'b>(
    &'a self,
    key: &'b str,
  ) -> impl Iterator<Item = (&'a Yarn, &'a V)> + 'b {
    self.subtrie("").prefixes_of(key)
  }

  /// Returns the longest key in this trie that is a prefix of `key`.
  ///
  /// This is a convenience wrapper over `trie.prefixes_of(key).last()`.
  #[allow(unused)]
  pub fn longest_prefix_of(&self, key: &str) -> Option<(&Yarn, &V)> {
    self.subtrie("").longest_prefix_of(key)
  }

  /// Gets the next valid link for the node at `idx`, after `prev`, if one
  /// exists.
  fn next_valid_byte_at(
    &self,
    idx: usize,
    prev: Option<u8>,
  ) -> Option<(u8, u32)> {
    let min = prev.map(|x| x + 1).unwrap_or(0);
    let min_hi = (min >> 4) as usize;
    for (hi, &idx) in self.hi_nodes[idx].iter().enumerate().skip(min_hi) {
      let min_lo = if hi == min_hi {
        (min & 0xf) as usize
      } else {
        0
      };

      if idx == EMPTY {
        continue;
      }

      for (lo, &idx) in
        self.lo_nodes[idx as usize].iter().enumerate().skip(min_lo)
      {
        if idx != EMPTY {
          return Some(((hi << 4 | lo) as u8, idx));
        }
      }
    }

    None
  }
}

pub struct Subtrie<'a, V> {
  trie: &'a Trie<V>,
  root: u32,
}

impl<'a, V> Clone for Subtrie<'a, V> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<'a, V> Copy for Subtrie<'a, V> {}

impl<'a, V> Subtrie<'a, V> {
  /// Constructs a subtrie consisting of those keys which have `prefix` as a
  /// prefix.
  ///
  /// `trie.subtrie("")` will cheaply view this trie as the trivial subtrie.
  #[inline]
  pub fn subtrie(self, prefix: &str) -> Subtrie<'a, V> {
    if prefix.is_empty() {
      return self;
    }

    Subtrie {
      trie: self.trie,
      root: self.prefix_nodes_of(prefix).last().unwrap_or(EMPTY),
    }
  }

  /// Returns an iterator that yields indices of `hi_node` in depth-first
  /// traversal order.
  fn depth_first_nodes(self) -> impl Iterator<Item = u32> + 'a {
    let mut path = vec![];
    let mut next_offsets = vec![];

    if self.root != EMPTY && !self.trie.lo_nodes.is_empty() {
      path.push(self.root);
    }

    iter::from_fn(move || loop {
      let Some(&next) = path.last() else {
        return None;
      };

      let prev_offset = next_offsets.get(path.len() - 1).copied();

      match self.trie.next_valid_byte_at(next as usize, prev_offset) {
        Some((next_offset, next_idx)) => {
          if prev_offset.is_none() {
            next_offsets.push(next_offset);
          } else {
            *next_offsets.last_mut().unwrap() = next_offset;
          }
          path.push(next_idx);
        }
        None => {
          path.pop();
          if prev_offset.is_some() {
            next_offsets.pop();
          }
        }
      }

      if prev_offset.is_none() {
        return Some(next);
      }
    })
  }

  /// Returns an iterator over the elements of this trie.
  ///
  /// Guaranteed to traverse keys in sorted order.
  pub fn iter(self) -> impl Iterator<Item = (&'a Yarn, &'a V)> {
    self.depth_first_nodes().filter_map(|idx| {
      let sparse = self.trie.sparse[idx as usize];
      if sparse == EMPTY {
        return None;
      }
      let (k, v) = &self.trie.values[sparse as usize];
      Some((k, v))
    })
  }

  /// Returns an iterator over all `hi_node` indices that correspond to prefixes
  /// of `key`.
  ///
  /// If `key` is not in this trie, the iterator will also yield `EMPTY` to
  /// denote this.
  fn prefix_nodes_of(self, key: &'a str) -> impl Iterator<Item = u32> + 'a {
    let mut idx = self.root;
    let mut done = self.trie.lo_nodes.is_empty();
    key
      .bytes()
      .map(Some)
      .chain(Some(None))
      .map_while(move |byte| {
        // This extra done bit ensures that if `key` is not present in the
        // trie, the iterator yields an extra element to distinguish this case.
        if done {
          return None;
        }

        if idx == !0 {
          done = true;
          return Some(idx);
        }

        let ret = idx;
        if let Some(byte) = byte {
          idx = 'idx: {
            let lo = (byte & 0xf) as usize;
            let hi = (byte >> 4) as usize;
            let lo_idx = self.trie.hi_nodes[idx as usize][hi];
            if lo_idx == EMPTY {
              break 'idx EMPTY;
            }

            self.trie.lo_nodes[lo_idx as usize][lo]
          }
        }

        Some(ret)
      })
  }

  /// Returns an iterator over keys in this trie that are prefixes of `key`.
  pub fn prefixes_of<'b>(
    self,
    key: &'b str,
  ) -> impl Iterator<Item = (&'a Yarn, &'a V)> + 'b
  where
    'a: 'b,
  {
    self.prefix_nodes_of(key).filter_map(|idx| {
      if idx == EMPTY {
        return None;
      }

      let sparse_idx = self.trie.sparse[idx as usize];
      match sparse_idx {
        EMPTY => None,
        n => {
          let (k, v) = &self.trie.values[n as usize];
          Some((k, v))
        }
      }
    })
  }

  /// Returns the longest key in this trie that is a prefix of `key`.
  ///
  /// This is a convenience wrapper over `trie.prefixes_of(key).last()`.
  pub fn longest_prefix_of(self, key: &str) -> Option<(&'a Yarn, &'a V)> {
    self.prefixes_of(key).last()
  }

  /// Dumps the contents of this trie to stderr.
  #[allow(unused)]
  pub(crate) fn dump(self)
  where
    V: fmt::Debug,
  {
    fn dump_stage<V: fmt::Debug>(
      trie: &Trie<V>,
      idx: u32,
      depth: u32,
      nybbles: [Option<u8>; 2],
    ) {
      for _ in 0..depth {
        eprint!(". ");
      }
      let is_hi = depth % 2 == 0;
      let array = if is_hi {
        eprint!("hi[{idx}]: ");
        trie.hi_nodes[idx as usize]
      } else {
        eprint!("lo[{idx}]: ");
        trie.lo_nodes[idx as usize]
      };

      eprint!("[");
      for (i, chunk) in array.chunks(4).enumerate() {
        if i != 0 {
          eprint!(", ");
        }

        if chunk == [EMPTY; 4] {
          eprint!("..");
          continue;
        }

        eprint!("[");
        for (i, &idx) in chunk.iter().enumerate() {
          if i != 0 {
            eprint!(", ");
          }
          if idx == EMPTY {
            eprint!("_");
          } else {
            eprint!("{idx}");
          }
        }
        eprint!("]");
      }
      eprint!("]");

      match nybbles {
        [Some(hi), None] => {
          let start = hi << 4;
          let end = start + 0xf;
          eprint!(", 0x{hi:x} {:?}..={:?}", start as char, end as char);
        }
        [Some(hi), Some(lo)] => {
          let ch = hi << 4 | lo;
          eprint!(", 0x{lo:x} {:?}", ch as char);
        }
        _ => {}
      }

      if is_hi {
        let sparse = trie.sparse[idx as usize];
        if sparse != EMPTY {
          eprint!(", #{sparse} {:?}", trie.values[sparse as usize]);
        }
      }
      eprintln!();

      for (i, &idx) in array.iter().enumerate() {
        if idx == EMPTY {
          continue;
        }
        dump_stage(
          trie,
          idx,
          depth + 1,
          if is_hi {
            [Some(i as u8), None]
          } else {
            [nybbles[0], Some(i as u8)]
          },
        );
      }
    }

    if self.root == EMPTY {
      eprintln!("</>");
      return;
    }

    dump_stage(self.trie, self.root, 0, [None, None]);
  }
}

impl<V: fmt::Debug> fmt::Debug for Trie<V> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_map().entries(self.iter()).finish()
  }
}

impl<V> Default for Trie<V> {
  fn default() -> Self {
    Self::new()
  }
}

#[cfg(test)]
mod test {
  use super::*;
  use byteyarn::yarn;

  #[test]
  fn empty() {
    let trie = Trie::new();
    iter_eq(trie.iter(), &[]);
    iter_eq(trie.prefixes_of(""), &[]);
    iter_eq(trie.longest_prefix_of(""), &[]);
  }

  #[test]
  fn get() {
    let trie = trie_set(&["a", "b", "abc", "abd"]);
    assert!(trie.get("a").is_some());
    assert!(trie.get("ab").is_none());
    assert!(trie.get("abc").is_some());
    assert!(trie.get("c").is_none());
  }

  #[test]
  fn prefixes() {
    let trie = trie_set(&["a", "b", "abc", "abd"]);
    iter_eq(trie.prefixes_of("abc"), &["a", "abc"]);
    iter_eq(trie.prefixes_of("abcde"), &["a", "abc"]);
    iter_eq(trie.longest_prefix_of("abcde"), &["abc"]);

    let trie = trie_set(&["", "a", "b", "ab"]);
    iter_eq(trie.longest_prefix_of("c"), &[""]);
  }

  #[test]
  fn iterator() {
    let trie = trie_set(&["a", "abc", "A", "abd"]);
    iter_eq(trie.iter(), &["A", "a", "abc", "abd"]);
    iter_eq(trie.subtrie("ab").iter(), &["abc", "abd"]);
    iter_eq(trie.subtrie("a").iter(), &["a", "abc", "abd"]);
    iter_eq(trie.subtrie("abcd").iter(), &[]);
    iter_eq(trie.subtrie("c").iter(), &[]);
  }

  fn trie_set(items: &[&str]) -> Trie<()> {
    let mut trie = Trie::new();
    for &k in items {
      assert!(trie.insert(yarn!("{k}"), ()).2.is_none());
    }
    trie.subtrie("").dump();
    trie
  }

  fn iter_eq<'a>(
    items: impl IntoIterator<Item = (&'a Yarn, &'a ())>,
    expected: &[&str],
  ) {
    assert_eq!(
      items
        .into_iter()
        .map(|(k, _)| k.as_slice())
        .collect::<Vec<_>>(),
      expected,
    );
  }
}

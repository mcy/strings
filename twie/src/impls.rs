/**** TRIE ****/

use std::fmt;

use buf_trait::Buf;

use crate::Index;
use crate::Iter;
use crate::IterMut;
use crate::Sub;
use crate::SubMut;
use crate::Trie;

impl<K, V, I> Clone for Trie<K, V, I>
where
  K: Buf + ?Sized,
  V: Clone,
  I: Index,
{
  fn clone(&self) -> Self {
    Self { raw: self.raw.clone() }
  }
}

impl<K, V, I> Default for Trie<K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn default() -> Self {
    Self::new()
  }
}

impl<K, V, I> fmt::Debug for Trie<K, V, I>
where
  K: Buf + ?Sized + fmt::Debug,
  V: fmt::Debug,
  I: Index,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Debug::fmt(&self.as_ref(), f)
  }
}

impl<'a, K, V, I> IntoIterator for &'a Trie<K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a V);
  type IntoIter = Iter<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<'a, K, V, I> IntoIterator for &'a mut Trie<K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a mut V);
  type IntoIter = IterMut<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter_mut()
  }
}

impl<'a, K, V, I> FromIterator<(&'a K, V)> for Trie<K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from_iter<Iter>(iter: Iter) -> Self
  where
    Iter: IntoIterator<Item = (&'a K, V)>,
  {
    let mut trie = Trie::new();
    for (k, v) in iter {
      trie.insert(k, v);
    }
    trie
  }
}

impl<K, V, I, const N: usize> From<[(&K, V); N]> for Trie<K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: [(&K, V); N]) -> Self {
    value.into_iter().collect()
  }
}

impl<K, V, I, const N: usize> From<[&K; N]> for Trie<K, V, I>
where
  K: Buf + ?Sized,
  V: Default,
  I: Index,
{
  fn from(value: [&K; N]) -> Self {
    value.into_iter().map(|k| (k, V::default())).collect()
  }
}

/**** SUB ****/

impl<'a, K, V, I> From<&'a Trie<K, V, I>> for Sub<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: &'a Trie<K, V, I>) -> Self {
    value.as_ref()
  }
}

impl<'a, K, V, I> From<SubMut<'a, K, V, I>> for Sub<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: SubMut<'a, K, V, I>) -> Self {
    Sub { raw: value.raw, prefix: value.prefix }
  }
}

impl<'a, K, V, I> From<&'a SubMut<'_, K, V, I>> for Sub<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: &'a SubMut<'_, K, V, I>) -> Self {
    value.as_ref()
  }
}

impl<K, V, I> Clone for Sub<'_, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn clone(&self) -> Self {
    *self
  }
}

impl<K, V, I> Copy for Sub<'_, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
}

impl<K, V, I> fmt::Debug for Sub<'_, K, V, I>
where
  K: Buf + ?Sized + fmt::Debug,
  V: fmt::Debug,
  I: Index,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    f.debug_map().entries(self.iter()).finish()
  }
}

impl<'a, K, V, I> IntoIterator for &'a Sub<'_, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a V);
  type IntoIter = Iter<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<'a, K, V, I> IntoIterator for Sub<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a V);
  type IntoIter = Iter<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

/**** SUB MUT ****/

impl<'a, K, V, I> From<&'a mut Trie<K, V, I>> for SubMut<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: &'a mut Trie<K, V, I>) -> Self {
    value.as_mut()
  }
}

impl<'a, K, V, I> From<&'a mut SubMut<'_, K, V, I>> for SubMut<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  fn from(value: &'a mut SubMut<'_, K, V, I>) -> Self {
    value.as_mut()
  }
}

impl<K, V, I> fmt::Debug for SubMut<'_, K, V, I>
where
  K: Buf + ?Sized + fmt::Debug,
  V: fmt::Debug,
  I: Index,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Debug::fmt(&self.as_ref(), f)
  }
}

impl<'a, K, V, I> IntoIterator for &'a SubMut<'_, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a V);
  type IntoIter = Iter<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.as_ref().iter()
  }
}

impl<'a, K, V, I> IntoIterator for &'a mut SubMut<'_, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a mut V);
  type IntoIter = IterMut<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.as_mut().iter_mut()
  }
}

impl<'a, K, V, I> IntoIterator for SubMut<'a, K, V, I>
where
  K: Buf + ?Sized,
  I: Index,
{
  type Item = (&'a K, &'a mut V);
  type IntoIter = IterMut<'a, K, V, I>;

  fn into_iter(self) -> Self::IntoIter {
    self.iter_mut()
  }
}

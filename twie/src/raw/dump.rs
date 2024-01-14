use std::fmt;
use std::fmt::Write;

use buf_trait::Buf;

use crate::raw::entries::Entries;
use crate::raw::nodes::Node;
use crate::raw::nodes::Nodes;
use crate::raw::RawTrie;
use crate::DebugBytes;
use crate::Index;

/// Dumps the contents of this trie to a string in an unspecified format.
pub fn dump<K: Buf + ?Sized, V: fmt::Debug, I: Index>(
  trie: &RawTrie<K, V, I>,
  root: Node<I>,
) -> String {
  if root.is_empty() {
    return "</>".to_string();
  }

  let mut out = String::new();
  let _ignored =
    dump0(&mut out, &trie.nodes, &trie.data, root, None, &mut Vec::new());

  out.truncate(out.trim_end().len());
  out
}

fn dump0<V: fmt::Debug, I: Index>(
  out: &mut String,
  nodes: &Nodes<I>,
  entries: &Entries<V, I>,
  node: Node<I>,
  hi: Option<u8>,
  bus: &mut Vec<bool>,
) -> Result<(), fmt::Error> {
  use boxy::Char;

  let is_hi = hi.is_none();
  let array = match hi {
    Some(hi) => nodes.lo(node.ptr, hi),
    None => nodes.hi(node.ptr),
  };

  let has = array.iter().any(|&x| !x.is_empty());

  // All this crap is just so we get a pretty tree.
  let last = bus
    .iter()
    .enumerate()
    .filter_map(|(i, x)| x.then_some(i + 1))
    .last()
    .unwrap_or(0);
  for (i, &flag) in bus.iter().enumerate().take(last) {
    if flag {
      if i == bus.len() - 1 {
        write!(out, "{}", Char::right_tee(boxy::Weight::Normal))?;
      } else {
        write!(out, "{}", Char::vertical(boxy::Weight::Normal))?;
      }
    } else {
      write!(out, "{}", Char::empty())?;
    }
  }
  for i in last..bus.len() {
    if i == bus.len() - 1 {
      write!(out, "{}", Char::lower_left(boxy::Weight::Normal))?;
    } else {
      write!(out, "{}", Char::empty())?;
    }
  }
  if has {
    write!(out, "{}", Char::down_tee(boxy::Weight::Normal))?;
  } else {
    write!(out, "{}", Char::horizontal(boxy::Weight::Normal))?;
  }
  write!(out, "{}", Char::left_half(boxy::Weight::Normal))?;

  let new_line = |out: &mut String| {
    writeln!(out)?;
    for &flag in bus.iter().take(last) {
      if flag {
        write!(out, "{}", Char::vertical(boxy::Weight::Normal))?;
      } else {
        write!(out, "{}", Char::empty())?;
      }
    }
    for _ in last..bus.len() {
      write!(out, "{}", Char::empty())?;
    }
    if has {
      write!(out, "{}", Char::vertical(boxy::Weight::Normal))?;
    }

    write!(out, "  ")
  };

  write!(out, "[{}]", node.ptr.idx() * 2 + (!is_hi as usize),)?;

  if is_hi {
    let key = nodes.key(node, Some(usize::MAX));
    write!(
      out,
      ": {:?}/{:?}",
      DebugBytes(&key[..node.depth]),
      DebugBytes(&key[node.depth..]),
    )?;
  }

  if let Some(hi) = hi {
    new_line(out)?;
    let start = hi << 4;
    let end = start + 0xf;
    let _ = write!(out, "hi: 0x{hi:x} {:?}..={:?}", start as char, end as char);
  } else if let Some(&ch) = nodes.key(node, None).last() {
    new_line(out)?;
    let lo = ch & 0xf;
    write!(out, "lo: 0x{lo:x} {:?}", ch as char)?;
  }

  new_line(out)?;
  write!(out, "ptrs: ")?;
  for (i, chunk) in array.chunks(4).enumerate() {
    if i != 0 {
      write!(out, "|")?;
    }

    if chunk.iter().all(|n| n.is_empty()) {
      write!(out, "--")?;
      continue;
    }

    for (i, &ptr) in chunk.iter().enumerate() {
      if i != 0 {
        write!(out, "/")?;
      }

      match usize::try_from(ptr) {
        Ok(idx) => {
          write!(out, "{}", if !is_hi { idx * 2 } else { idx * 2 + 1 })
        }
        Err(_) => write!(out, "-"),
      }?;
    }
  }

  if is_hi {
    if let Some(sparse) = nodes.get(node) {
      if let Some((len, v)) = entries.get(sparse) {
        let k = nodes.key(node, Some(len));
        new_line(out)?;
        write!(out, "[{sparse}]: {k:p} {:?} -> {v:p} {v:?}", DebugBytes(k),)?;
      }
    }
  }

  new_line(out)?;
  writeln!(out)?;

  let last = array
    .iter()
    .enumerate()
    .filter_map(|(i, &node)| (!node.is_empty()).then_some(i))
    .last()
    .unwrap_or(0);

  bus.push(true);
  for (i, &n) in array.iter().enumerate() {
    if n.is_empty() {
      continue;
    }

    if i == last {
      bus.pop();
      bus.push(false);
    }

    let (node, hi) = match hi {
      None => (node, Some(i as u8)),
      Some(hi) => {
        let byte = hi << 4 | (i as u8);
        (nodes.walk(node, &[byte]).0, None)
      }
    };

    dump0(out, nodes, entries, node, hi, bus)?;
  }
  bus.pop();

  Ok(())
}

use std::fmt;
use std::fmt::Write;
use std::str;

use buf_trait::Buf;

use crate::raw::nodes::Node;
use crate::raw::Prefix;
use crate::raw::RawTrie;
use crate::Index;

/// Dumps the contents of this trie to a string in an unspecified format.
pub fn dump<K: Buf + ?Sized, V: fmt::Debug, I: Index>(
  trie: &RawTrie<K, V, I>,
  root: &Prefix,
) -> String {
  let node = root.node();
  if node.is_empty() {
    return "</>".to_string();
  }

  let mut out = String::new();
  let _ignored = dump0(
    trie,
    &mut out,
    node,
    &mut Vec::new(),
    &mut Vec::new(),
    0,
    [None, None],
  );

  out.truncate(out.trim_end().len());
  out
}

fn dump0<K: Buf + ?Sized, V: fmt::Debug, I: Index>(
  trie: &RawTrie<K, V, I>,
  out: &mut String,
  node: Node<I>,
  bus: &mut Vec<bool>,
  stack: &mut Vec<u8>,
  depth: usize,
  nybbles: [Option<u8>; 2],
) -> Result<(), fmt::Error> {
  use boxy::Char;

  let is_hi = depth % 2 == 0;
  let array = if is_hi { trie.nodes.hi(node) } else { trie.nodes.lo(node) };

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

  if !is_hi {
    stack.push(b'?');
  }
  write!(
    out,
    "[{}]: {:?}",
    node.idx() * 2 + (!is_hi as usize),
    DebugBytes(stack),
  )?;
  if !is_hi {
    stack.pop();
  }

  match nybbles {
    [Some(hi), None] => {
      new_line(out)?;
      let start = hi << 4;
      let end = start + 0xf;
      let _ =
        write!(out, "hi: 0x{hi:x} {:?}..={:?}", start as char, end as char);
    }
    [Some(hi), Some(lo)] => {
      new_line(out)?;
      let ch = hi << 4 | lo;
      write!(out, "lo: 0x{lo:x} {:?}", ch as char)?;
    }
    _ => {}
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

    for (i, &node) in chunk.iter().enumerate() {
      if i != 0 {
        write!(out, "/")?;
      }

      match usize::try_from(node) {
        Ok(node) => {
          write!(out, "{}", if !is_hi { node * 2 } else { node * 2 + 1 })
        }
        Err(_) => write!(out, "-"),
      }?;
    }
  }

  if is_hi {
    if let Some(sparse) = trie.nodes.get(node) {
      if let Some((k, v)) = trie.data.get(sparse) {
        new_line(out)?;
        write!(
          out,
          "[{sparse}]: {k:p} {:?} -> {v:p} {v:?}",
          DebugBytes(k.as_bytes()),
        )?;
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

    let nybbles =
      if is_hi { [Some(i as u8), None] } else { [nybbles[0], Some(i as u8)] };

    if let Some(hi) = nybbles[0].filter(|_| !is_hi) {
      let ch = hi << 4 | (i as u8);
      stack.push(ch);
    }

    dump0(trie, out, n, bus, stack, depth + 1, nybbles)?;

    if !is_hi {
      stack.pop();
    }
  }
  bus.pop();

  Ok(())
}

struct DebugBytes<'a>(&'a [u8]);
impl fmt::Debug for DebugBytes<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.write_char('"')?;
    let mut buf = self.0;
    while !buf.is_empty() {
      let len = match str::from_utf8(buf) {
        Ok(rest) => rest.len(),
        Err(e) => e.valid_up_to(),
      };

      let prefix = &buf[..len];
      write!(f, "{}", str::from_utf8(prefix).unwrap().escape_debug())?;
      if len == buf.len() {
        break;
      }

      write!(f, "\\x{:02x}", buf[len])?;
      buf = &buf[len + 1..];
    }
    f.write_char('"')
  }
}

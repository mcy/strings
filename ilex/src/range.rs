use core::fmt;
use std::ops;
use std::ops::Add;
use std::ops::Bound;
use std::ops::Index;
use std::ops::RangeBounds;

/// A custom range type that is a little easier to manipulate.
#[derive(Clone, Copy, Default)]
pub struct Range {
  pub start: u32,
  pub end: u32,
}

#[allow(non_snake_case)]
#[track_caller]
pub fn Range<T: Copy + TryInto<u32> + fmt::Debug>(start: T, end: T) -> Range {
  Range { start: cast(start), end: cast(end) }
}

#[track_caller]
fn cast<T: Copy + TryInto<u32> + fmt::Debug>(value: T) -> u32 {
  value
    .try_into()
    .unwrap_or_else(|_| bug!("range bound does not fit into u32: {:?}", value))
}

impl Range {
  #[track_caller]
  pub fn new<T: Copy + TryInto<u32> + fmt::Debug>(
    range: impl RangeBounds<T>,
  ) -> Range {
    let start = match range.start_bound() {
      Bound::Included(&x) => cast(x),
      Bound::Excluded(&x) => cast(x).saturating_add(1),
      Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
      Bound::Included(&x) => cast(x).saturating_add(1),
      Bound::Excluded(&x) => cast(x),
      Bound::Unbounded => u32::MAX,
    };

    Range(start, end)
  }

  pub fn start(self) -> usize {
    self.start as usize
  }

  pub fn end(self) -> usize {
    self.end as usize
  }

  pub fn bounds(self) -> ops::Range<usize> {
    self.start as usize..self.end as usize
  }

  pub fn clip(self, that: Range) -> Range {
    Range(self.start.max(that.start), self.end.min(that.end))
  }

  pub fn len(self) -> usize {
    (self.end - self.start) as usize
  }

  pub fn join(self, that: Range) -> Range {
    Range(u32::min(self.start, that.start), u32::max(self.start, that.start))
  }

  pub fn delete(self, middle: Range) -> (Range, Range) {
    (Range(self.start, middle.start), Range(middle.end, self.end))
  }

  #[track_caller]
  pub fn bounds_check(self, limit: usize) {
    assert!(
      self.start <= self.end,
      "out of order range: {} > {}",
      self.start,
      self.end
    );
    assert!(
      self.end as usize <= limit,
      "got out of bounds range: {} > {}",
      self.end,
      limit
    );
  }
}

impl Index<Range> for str {
  type Output = str;

  #[track_caller]
  fn index(&self, index: Range) -> &Self::Output {
    &self[index.start as usize..index.end as usize]
  }
}

impl<T: Copy + TryInto<u32> + fmt::Debug> Add<T> for Range {
  type Output = Self;

  fn add(self, rhs: T) -> Self::Output {
    let rhs = cast(rhs);
    Range(self.start + rhs, self.end + rhs)
  }
}

impl fmt::Debug for Range {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}..{}", self.start, self.end)
  }
}

impl RangeBounds<u32> for Range {
  fn start_bound(&self) -> Bound<&u32> {
    Bound::Included(&self.start)
  }

  fn end_bound(&self) -> Bound<&u32> {
    Bound::Excluded(&self.end)
  }
}

// concrete.rs

use crate::set::Set;
use std::ops::{Add, Mul};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Z5(u8);

impl Z5 {
    pub fn new(value: u8) -> Self {
        Z5(value % 5)
    }
}

impl Add for Z5 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Z5::new(self.0 + rhs.0)
    }
}

impl Mul for Z5 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Z5::new(self.0 * rhs.0)
    }
}

impl Set<Z5> for Z5 {
    fn is_empty(&self) -> bool {
        false
    }

    fn contains(&self, element: &Z5) -> bool {
        *self == *element
    }

    fn empty() -> Self {
        Z5(0)
    }

    fn singleton(element: Z5) -> Self {
        element
    }

    fn union(&self, other: &Self) -> Self {
        if self == other {
            *self
        } else {
            Z5::new(self.0.min(other.0))
        }
    }

    fn intersection(&self, other: &Self) -> Self {
        if self == other {
            *self
        } else {
            Z5::new(0)
        }
    }

    fn difference(&self, other: &Self) -> Self {
        if self == other {
            Z5::new(0)
        } else {
            *self
        }
    }

    fn symmetric_difference(&self, other: &Self) -> Self {
        if self == other {
            Z5::new(0)
        } else {
            Z5::new(self.0.max(other.0))
        }
    }

    fn is_subset(&self, other: &Self) -> bool {
        self == other
    }

    fn is_equal(&self, other: &Self) -> bool {
        self == other
    }

    fn cardinality(&self) -> Option<usize> {
        Some(1)
    }

    fn is_finite(&self) -> bool {
        true
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct InfiniteRealSet;

impl Set<f64> for InfiniteRealSet {
    fn is_empty(&self) -> bool {
        false
    }

    fn contains(&self, _element: &f64) -> bool {
        true
    }

    fn empty() -> Self {
        InfiniteRealSet
    }

    fn singleton(_element: f64) -> Self {
        InfiniteRealSet
    }

    fn union(&self, _other: &Self) -> Self {
        InfiniteRealSet
    }

    fn intersection(&self, _other: &Self) -> Self {
        InfiniteRealSet
    }

    fn difference(&self, _other: &Self) -> Self {
        InfiniteRealSet
    }

    fn symmetric_difference(&self, _other: &Self) -> Self {
        InfiniteRealSet
    }

    fn is_subset(&self, _other: &Self) -> bool {
        true
    }

    fn is_equal(&self, _other: &Self) -> bool {
        true
    }

    fn cardinality(&self) -> Option<usize> {
        None
    }

    fn is_finite(&self) -> bool {
        false
    }
}

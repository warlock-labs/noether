use std::ops::{Add, Mul, Neg};
use num_traits::{Inv, One, Zero};
use crate::{Associative, Commutative, Distributive};
use crate::set::Set;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Z5(pub(crate) u8);

impl Z5 {
    pub fn new(value: u8) -> Self {
        Z5(value % 5)
    }
}

impl Set for Z5 {
    type Element = Z5;

    fn is_empty(&self) -> bool {
        false
    }

    fn contains(&self, element: &Self::Element) -> bool {
        self == element
    }

    fn empty() -> Self {
        Z5(0)
    }

    fn singleton(element: Self::Element) -> Self {
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
        Some(5)
    }

    fn is_finite(&self) -> bool {
        true
    }
}

// Implement necessary traits for Z5
impl Add for Z5 {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Z5::new(self.0 + other.0)
    }
}

impl Mul for Z5 {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Z5::new(self.0 * other.0)
    }
}

impl Zero for Z5 {
    fn zero() -> Self {
        Z5::new(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl One for Z5 {
    fn one() -> Self {
        Z5::new(1)
    }
}

impl Neg for Z5 {
    type Output = Self;

    fn neg(self) -> Self {
        Z5::new(5 - self.0)
    }
}

impl Inv for Z5 {
    type Output = Self;

    fn inv(self) -> Self {
        match self.0 {
            1 => Z5::new(1),
            2 => Z5::new(3),
            3 => Z5::new(2),
            4 => Z5::new(4),
            0 => panic!("Cannot invert zero in Z5"),
            _ => unreachable!(),
        }
    }
}

impl Associative for Z5 {}

impl Commutative for Z5 {}

impl Distributive for Z5 {}

#[derive(Clone, PartialEq, Debug)]
pub struct InfiniteRealSet;

impl Set for InfiniteRealSet {
    type Element = f64;

    fn is_empty(&self) -> bool {
        false
    }

    fn contains(&self, _element: &Self::Element) -> bool {
        true
    }

    fn empty() -> Self {
        InfiniteRealSet
    }

    fn singleton(_element: Self::Element) -> Self {
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

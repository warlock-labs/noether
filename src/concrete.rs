use crate::set::Set;
use crate::{Associative, Commutative, Distributive};
use num_traits::{Euclid, Inv, One, Zero};
use std::cmp::Ordering;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

// This is a very sloppy and not optimal implementation of Z5.
// But seems correct overall.

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

impl Add for Z5 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Z5::new((self.0 + rhs.0) % 5)
    }
}

impl Mul for Z5 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Z5::new((self.0 * rhs.0) % 5)
    }
}

impl Neg for Z5 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Z5::new(5 - self.0)
    }
}

impl Inv for Z5 {
    type Output = Self;

    fn inv(self) -> Self::Output {
        if self.0 == 0 {
            panic!("Cannot invert zero in Z5");
        }
        for i in 1..5 {
            if (self.0 * i) % 5 == 1 {
                return Z5::new(i);
            }
        }
        unreachable!()
    }
}

impl Div for Z5 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl Sub for Z5 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Z5::new((self.0 + 5 - rhs.0) % 5)
    }
}

impl Rem for Z5 {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        Z5::new(self.0 % rhs.0)
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

impl Euclid for Z5 {
    fn div_euclid(&self, v: &Self) -> Self {
        if v.is_zero() {
            panic!("attempt to divide by zero");
        }
        let q = (self.0 as i32 * v.inv().0 as i32) % 5;
        Z5::new(q as u8)
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        if v.is_zero() {
            panic!("attempt to divide by zero");
        }
        let r = self.0 % v.0;
        Z5::new(r)
    }
}

impl Z5 {
    pub fn div_rem_euclid(&self, v: &Self) -> (Self, Self) {
        let q = self.div_euclid(v);
        let r = *self - q * *v;
        (q, r)
    }
}

impl PartialOrd for Z5 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Z5 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
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

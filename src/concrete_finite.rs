use crate::{Associative, Commutative, Distributive, EuclideanDomain, Field, FiniteField, Set};
use num_traits::{Inv, One, Zero};
use std::fmt::{self, Debug, Display};
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct FinitePrimeField<const P: u64> {
    value: u64,
}

impl<const P: u64> FinitePrimeField<P> {
    pub fn new(value: u64) -> Self {
        assert!(Self::is_prime(P), "P must be prime");
        Self { value: value % P }
    }

    fn is_prime(n: u64) -> bool {
        if n <= 1 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        let sqrt_n = (n as f64).sqrt() as u64;
        for i in (3..=sqrt_n).step_by(2) {
            if n % i == 0 {
                return false;
            }
        }
        true
    }

    pub fn value(&self) -> u64 {
        self.value
    }
}

impl<const P: u64> Debug for FinitePrimeField<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(mod {})", self.value, P)
    }
}

impl<const P: u64> Display for FinitePrimeField<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<const P: u64> Add for FinitePrimeField<P> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.value + rhs.value)
    }
}

impl<const P: u64> Sub for FinitePrimeField<P> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.value + P - rhs.value)
    }
}

impl<const P: u64> Mul for FinitePrimeField<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.value * rhs.value)
    }
}

impl<const P: u64> Div for FinitePrimeField<P> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<const P: u64> Neg for FinitePrimeField<P> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self::new(P - self.value)
    }
}

impl<const P: u64> Rem for FinitePrimeField<P> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        Self::new(self.value % rhs.value)
    }
}

impl<const P: u64> Zero for FinitePrimeField<P> {
    fn zero() -> Self {
        Self::new(0)
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const P: u64> One for FinitePrimeField<P> {
    fn one() -> Self {
        Self::new(1)
    }
}

impl<const P: u64> Inv for FinitePrimeField<P> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        if self.is_zero() {
            panic!("attempt to invert zero");
        }
        self.pow(P - 2)
    }
}

impl<const P: u64> Set for FinitePrimeField<P> {
    type Element = Self;

    fn is_empty(&self) -> bool {
        false
    }

    fn contains(&self, element: &Self::Element) -> bool {
        element.value < P
    }

    fn empty() -> Self {
        Self::zero()
    }

    fn singleton(element: Self::Element) -> Self {
        element
    }

    fn union(&self, _other: &Self) -> Self {
        *self
    }

    fn intersection(&self, other: &Self) -> Self {
        if self == other {
            *self
        } else {
            Self::empty()
        }
    }

    fn difference(&self, other: &Self) -> Self {
        if self == other {
            Self::empty()
        } else {
            *self
        }
    }

    fn symmetric_difference(&self, other: &Self) -> Self {
        if self == other {
            Self::empty()
        } else {
            *self
        }
    }

    fn is_subset(&self, _other: &Self) -> bool {
        true
    }

    fn is_equal(&self, other: &Self) -> bool {
        self == other
    }

    fn cardinality(&self) -> Option<usize> {
        Some(P as usize)
    }

    fn is_finite(&self) -> bool {
        true
    }
}

impl<const P: u64> Commutative for FinitePrimeField<P> {}
impl<const P: u64> Associative for FinitePrimeField<P> {}
impl<const P: u64> Distributive for FinitePrimeField<P> {}

impl<const P: u64> num_traits::Euclid for FinitePrimeField<P> {
    fn div_euclid(&self, v: &Self) -> Self {
        *self / *v
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        *self % *v
    }
}

impl<const P: u64> EuclideanDomain for FinitePrimeField<P> {
    fn gcd(a: Self, b: Self) -> Self {
        if b.is_zero() {
            a
        } else {
            Self::gcd(b, a % b)
        }
    }
}

impl<const P: u64> Field for FinitePrimeField<P> {}

impl<const P: u64> FiniteField for FinitePrimeField<P> {
    fn characteristic() -> u64 {
        P
    }

    fn order() -> u64 {
        P
    }

    fn is_primitive_element(element: &Self) -> bool {
        if element.is_zero() {
            return false;
        }
        let mut x = *element;
        for _ in 1..P - 1 {
            if x.is_one() {
                return false;
            }
            x = x * *element;
        }
        x.is_one()
    }

    fn pow(&self, mut exponent: u64) -> Self {
        let mut base = *self;
        let mut result = Self::one();
        while exponent > 0 {
            if exponent % 2 == 1 {
                result = result * base;
            }
            exponent /= 2;
            base = base * base;
        }
        result
    }

    fn mul_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(self.inv())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type F5 = FinitePrimeField<5>;

    #[test]
    fn test_finite_prime_field_arithmetic() {
        let a = F5::new(2);
        let b = F5::new(3);

        assert_eq!(a + b, F5::new(0));
        assert_eq!(a - b, F5::new(4));
        assert_eq!(a * b, F5::new(1));
        assert_eq!(a / b, F5::new(4));
        assert_eq!(-a, F5::new(3));
    }

    #[test]
    fn test_finite_prime_field_pow() {
        type F7 = FinitePrimeField<7>;

        let a = F7::new(3);
        assert_eq!(a.pow(0), F7::one());
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(2), F7::new(2));
        assert_eq!(a.pow(6), F7::one());
    }

    #[test]
    fn test_finite_prime_field_inv() {
        type F11 = FinitePrimeField<11>;

        let a = F11::new(2);
        assert_eq!(a.inv(), F11::new(6));
        assert_eq!(F11::zero().mul_inverse(), None);
    }

    #[test]
    fn test_finite_prime_field_primitive_element() {
        assert!(F5::is_primitive_element(&F5::new(2)));
        assert!(!F5::is_primitive_element(&F5::new(1)));
    }

    #[test]
    #[should_panic(expected = "P must be prime")]
    fn test_non_prime_field() {
        let _ = FinitePrimeField::<4>::new(1);
    }
}

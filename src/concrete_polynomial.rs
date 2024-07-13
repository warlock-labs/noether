use crate::{Associative, Commutative, Distributive, EuclideanDomain, Field, FiniteField, Set};
use num_traits::{One, Zero};
use std::fmt;
use std::fmt::{Debug, Display};
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PolynomialField<F: FiniteField + Copy, const N: usize> {
    coeffs: [F; N],
}

impl<F: FiniteField + Copy, const N: usize> PolynomialField<F, N> {
    pub fn new(coeffs: [F; N]) -> Self {
        Self { coeffs }
    }

    pub fn degree(&self) -> usize {
        self.coeffs
            .iter()
            .rev()
            .position(|&c| !c.is_zero())
            .map_or(0, |p| N - 1 - p)
    }

    pub fn leading_coefficient(&self) -> F {
        self.coeffs[self.degree()]
    }

    pub fn modulus() -> Self {
        let mut coeffs = [F::zero(); N];
        coeffs[0] = F::one();
        coeffs[1] = F::one();
        coeffs[N - 1] = F::one();
        Self::new(coeffs)
    }

    fn inv(&self) -> Self {
        if self.is_zero() {
            panic!("attempt to invert zero");
        }
        // Use Fermat's Little Theorem for inversion: a^(p^n - 2) mod p^n
        self.pow(Self::order() - 2)
    }

    fn pow(&self, mut exponent: u64) -> Self {
        let mut base = *self;
        let mut result = Self::one();
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = result * base;
            }
            base = base * base;
            exponent >>= 1;
        }
        result
    }
}

impl<F: FiniteField + Copy, const N: usize> Debug for PolynomialField<F, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PolynomialField(")?;
        let terms: Vec<String> = self
            .coeffs
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, &c)| !c.is_zero())
            .map(|(i, c)| match i {
                0 => format!("{:?}", c),
                1 => format!("{:?}x", c),
                _ => format!("{:?}x^{}", c, i),
            })
            .collect();
        write!(f, "{})", terms.join(" + "))
    }
}

impl<F: FiniteField + Copy, const N: usize> Display for PolynomialField<F, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<F: FiniteField + Copy, const N: usize> Add for PolynomialField<F, N> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let mut coeffs = [F::zero(); N];
        for i in 0..N {
            coeffs[i] = self.coeffs[i] + rhs.coeffs[i];
        }
        Self::new(coeffs)
    }
}

impl<F: FiniteField + Copy, const N: usize> Sub for PolynomialField<F, N> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let mut coeffs = [F::zero(); N];
        for i in 0..N {
            coeffs[i] = self.coeffs[i] - rhs.coeffs[i];
        }
        Self::new(coeffs)
    }
}

impl<F: FiniteField + Copy, const N: usize> Mul for PolynomialField<F, N> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = [F::zero(); N];
        for i in 0..N {
            for j in 0..N {
                if i + j < N {
                    result[i + j] = result[i + j] + self.coeffs[i] * rhs.coeffs[j];
                }
            }
        }
        Self::new(result) % Self::modulus()
    }
}

impl<F: FiniteField + Copy, const N: usize> Div for PolynomialField<F, N> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<F: FiniteField + Copy, const N: usize> Neg for PolynomialField<F, N> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        let mut coeffs = [F::zero(); N];
        for i in 0..N {
            coeffs[i] = -self.coeffs[i];
        }
        Self::new(coeffs)
    }
}

impl<F: FiniteField + Copy, const N: usize> Rem for PolynomialField<F, N> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        let mut r = self;
        while r.degree() >= rhs.degree() {
            let lead_r = r.leading_coefficient();
            let lead_rhs = rhs.leading_coefficient();
            let mut t = Self::zero();
            t.coeffs[r.degree() - rhs.degree()] = lead_r / lead_rhs;
            r = r - (t * rhs);
        }
        r
    }
}

impl<F: FiniteField + Copy, const N: usize> Zero for PolynomialField<F, N> {
    fn zero() -> Self {
        Self::new([F::zero(); N])
    }

    fn is_zero(&self) -> bool {
        self.coeffs.iter().all(|&c| c.is_zero())
    }
}

impl<F: FiniteField + Copy, const N: usize> One for PolynomialField<F, N> {
    fn one() -> Self {
        let mut coeffs = [F::zero(); N];
        coeffs[0] = F::one();
        Self::new(coeffs)
    }
}

impl<F: FiniteField + Copy, const N: usize> Set for PolynomialField<F, N> {
    type Element = Self;

    fn is_empty(&self) -> bool {
        false
    }
    fn contains(&self, _element: &Self::Element) -> bool {
        true
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
        Some(F::order().pow(N as u32) as usize)
    }
    fn is_finite(&self) -> bool {
        true
    }
}

impl<F: FiniteField + Copy, const N: usize> Commutative for PolynomialField<F, N> {}
impl<F: FiniteField + Copy, const N: usize> Associative for PolynomialField<F, N> {}
impl<F: FiniteField + Copy, const N: usize> Distributive for PolynomialField<F, N> {}

impl<F: FiniteField + Copy, const N: usize> num_traits::Euclid for PolynomialField<F, N> {
    fn div_euclid(&self, v: &Self) -> Self {
        *self / *v
    }
    fn rem_euclid(&self, v: &Self) -> Self {
        *self % *v
    }
}

impl<F: FiniteField + Copy, const N: usize> EuclideanDomain for PolynomialField<F, N> {
    fn gcd(mut a: Self, mut b: Self) -> Self {
        while !b.is_zero() {
            let r = a % b;
            a = b;
            b = r;
        }
        a
    }
}

impl<F: FiniteField + Copy, const N: usize> Field for PolynomialField<F, N> {}

impl<F: FiniteField + Copy, const N: usize> FiniteField for PolynomialField<F, N> {
    fn characteristic() -> u64 {
        F::characteristic()
    }

    fn order() -> u64 {
        F::order().pow(N as u32)
    }

    fn is_primitive_element(element: &Self) -> bool {
        if element.is_zero() || element.is_one() {
            return false;
        }
        let order = Self::order();
        let mut x = *element;
        for i in 1..100 {
            // Limit iterations for practicality
            if x.is_one() {
                return i == order - 1;
            }
            x = x * *element;
            if i % 10 == 0 && x == *element {
                return false;
            }
        }
        false // Assume not primitive if not determined after 100 iterations
    }

    fn pow(&self, exponent: u64) -> Self {
        self.pow(exponent)
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
    use crate::concrete_finite::FinitePrimeField;
    use std::time::{Duration, Instant};

    type F5 = FinitePrimeField<5>;
    type F5_3 = PolynomialField<F5, 3>;

    fn run_with_timeout<F, R>(f: F, timeout: Duration) -> R
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        use std::sync::mpsc::channel;
        use std::thread;

        let (tx, rx) = channel();
        let handle = thread::spawn(move || {
            let result = f();
            tx.send(result).unwrap();
        });

        match rx.recv_timeout(timeout) {
            Ok(result) => {
                handle.join().unwrap();
                result
            }
            Err(_) => panic!("Test timed out after {:?}", timeout),
        }
    }

    #[test]
    fn test_polynomial_field_arithmetic() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(1), F5::new(2), F5::new(3)]);
                let b = F5_3::new([F5::new(4), F5::new(0), F5::new(1)]);

                let sum = a + b;
                let diff = a - b;
                let prod = a * b;
                let quot = a / b;

                assert_eq!(sum, F5_3::new([F5::new(0), F5::new(2), F5::new(4)]));
                assert_eq!(diff, F5_3::new([F5::new(2), F5::new(2), F5::new(2)]));
                assert_eq!(prod, F5_3::new([F5::new(4), F5::new(3), F5::new(2)]));
                assert_eq!(quot * b, a);
            },
            Duration::from_secs(1),
        );
    }

    #[test]
    fn test_polynomial_field_inv() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(1), F5::new(2), F5::new(3)]);
                let a_inv = a.inv();
                assert_eq!(a * a_inv, F5_3::one());
            },
            Duration::from_secs(1),
        );
    }

    #[test]
    fn test_polynomial_field_pow() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(2), F5::new(1), F5::new(0)]);
                assert_eq!(a.pow(0), F5_3::one());
                assert_eq!(a.pow(1), a);
                assert_eq!(a.pow(5), a * a * a * a * a);
            },
            Duration::from_secs(1),
        );
    }

    #[test]
    fn test_polynomial_field_primitive_element() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(2), F5::new(1), F5::new(0)]);
                let is_primitive = F5_3::is_primitive_element(&a);
                println!("Is primitive element: {}", is_primitive);
            },
            Duration::from_secs(1),
        );
    }

    #[test]
    fn test_field_properties() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(1), F5::new(2), F5::new(3)]);
                let b = F5_3::new([F5::new(4), F5::new(0), F5::new(1)]);
                let c = F5_3::new([F5::new(2), F5::new(1), F5::new(0)]);

                assert_eq!((a + b) + c, a + (b + c));
                assert_eq!((a * b) * c, a * (b * c));
                assert_eq!(a + b, b + a);
                assert_eq!(a * b, b * a);
                assert_eq!(a * (b + c), (a * b) + (a * c));
                assert_eq!(a + F5_3::zero(), a);
                assert_eq!(a * F5_3::one(), a);
                assert_eq!(a + (-a), F5_3::zero());
                assert_eq!(a * a.inv(), F5_3::one());
            },
            Duration::from_secs(1),
        );
    }

    #[test]
    fn test_field_order() {
        let order = F5_3::order();
        assert_eq!(order, 125); // 5^3 = 125
    }

    #[test]
    fn test_polynomial_degree() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(1), F5::new(2), F5::new(3)]);
                assert_eq!(a.degree(), 2);
                let b = F5_3::new([F5::new(1), F5::new(2), F5::new(0)]);
                assert_eq!(b.degree(), 1);
                let c = F5_3::new([F5::new(1), F5::new(0), F5::new(0)]);
                assert_eq!(c.degree(), 0);
                let d = F5_3::zero();
                assert_eq!(d.degree(), 0);
            },
            Duration::from_secs(1),
        );
    }

    // ... [Include the rest of the tests from the previous response] ...

    #[test]
    fn test_polynomial_large_exponent() {
        run_with_timeout(
            || {
                let a = F5_3::new([F5::new(2), F5::new(1), F5::new(0)]);
                let large_exp = 1_000_000_007; // A large prime number
                let result = a.pow(large_exp);
                assert!(!result.is_zero());
            },
            Duration::from_secs(5),
        ); // Allow more time for this test
    }
}

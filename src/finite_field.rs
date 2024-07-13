use crate::Field;

/// Represents a Finite Prime Field, a field with a finite number of elements where the number of elements is prime.
///
/// A finite prime field ℤ/pℤ (also denoted as 𝔽_p or GF(p)) consists of:
/// - A set of p elements {0, 1, 2, ..., p-1}, where p is prime
/// - Addition and multiplication operations modulo p
///
/// Formal Definition:
/// Let p be a prime number. Then:
/// 1. The set is {0, 1, 2, ..., p-1}
/// 2. Addition: a +_p b = (a + b) mod p
/// 3. Multiplication: a ·_p b = (a · b) mod p
/// 4. The additive identity is 0
/// 5. The multiplicative identity is 1
/// 6. Every non-zero element has a unique multiplicative inverse
pub trait FinitePrimeField: Field {
    /// Returns the characteristic of the field, which is the prime number p.
    fn characteristic() -> u64;

    /// Returns the number of elements in the field, which is equal to the characteristic for prime fields.
    fn order() -> u64 {
        Self::characteristic()
    }

    /// Checks if the given integer is a primitive element (generator) of the multiplicative group.
    fn is_primitive_element(element: &Self) -> bool;

    /// Computes the multiplicative inverse using Fermat's Little Theorem: a^(p-1) ≡ 1 (mod p)
    /// Therefore, a^(p-2) is the multiplicative inverse of a.
    fn mul_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            None
        } else {
            Some(self.pow(Self::characteristic() - 2))
        }
    }

    /// Raises the element to a power using exponentiation by squaring.
    fn pow(&self, mut exponent: u64) -> Self {
        let mut base = self.clone();
        let mut result = Self::one();
        while exponent > 0 {
            if exponent % 2 == 1 {
                result = result * base.clone();
            }
            base = base.clone() * base;
            exponent /= 2;
        }
        result
    }
}

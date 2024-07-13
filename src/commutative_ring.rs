use crate::ring::Ring;
use crate::Commutative;

/// Represents a Commutative Ring, an algebraic structure where multiplication is commutative.
///
/// A commutative ring (R, +, ·) is a ring that also satisfies:
/// - Commutativity of multiplication: ∀ a, b ∈ R, a · b = b · a
///
/// Formal Definition:
/// Let (R, +, ·) be a commutative ring. Then:
/// 1. (R, +, ·) is a ring
/// 2. ∀ a, b ∈ R, a · b = b · a (commutativity of multiplication)
pub trait CommutativeRing: Ring + Commutative {}

impl<T> CommutativeRing for T where T: Ring + Commutative {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{One, Zero};

    #[test]
    fn test_z5_commutative_ring() {
        // Test commutativity of multiplication
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);
                assert_eq!(a * b, b * a);
            }
        }
    }

    #[test]
    fn test_z5_ring_properties() {
        // Test additive properties
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);

                // Commutativity of addition
                assert_eq!(a + b, b + a);

                // Associativity of addition
                let c = Z5::new((i + j) % 5);
                assert_eq!((a + b) + c, a + (b + c));
            }
        }

        // Test multiplicative properties
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);

                // Associativity of multiplication
                let c = Z5::new((i * j) % 5);
                assert_eq!((a * b) * c, a * (b * c));
            }
        }

        // Test distributive property
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..5 {
                    let a = Z5::new(i);
                    let b = Z5::new(j);
                    let c = Z5::new(k);

                    assert_eq!(a * (b + c), (a * b) + (a * c));
                    assert_eq!((b + c) * a, (b * a) + (c * a));
                }
            }
        }

        // Test additive identity and inverse
        let zero = Z5::zero();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
            let neg_a = -a;
            assert_eq!(a + neg_a, zero);
            assert_eq!(neg_a + a, zero);
        }

        // Test multiplicative identity
        let one = Z5::one();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a * one, a);
            assert_eq!(one * a, a);
        }
    }

    #[test]
    fn test_z5_implements_commutative_ring() {
        fn assert_commutative_ring<T: CommutativeRing>() {}
        assert_commutative_ring::<Z5>();
    }
}

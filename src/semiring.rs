use crate::monoid::{AdditiveMonoid, MultiplicativeMonoid};
use crate::Distributive;

/// Represents a Semiring, an algebraic structure with two binary operations (addition and multiplication)
/// that satisfy certain axioms.
///
/// A semiring (S, +, ·, 0, 1) consists of:
/// - A set S
/// - Two binary operations + (addition) and · (multiplication) on S
/// - Two distinguished elements 0 (zero) and 1 (one) of S
///
/// Formal Definition:
/// Let (S, +, ·, 0, 1) be a semiring. Then:
/// 1. (S, +, 0) is a commutative monoid:
///    a. ∀ a, b, c ∈ S, (a + b) + c = a + (b + c) (associativity)
///    b. ∀ a, b ∈ S, a + b = b + a (commutativity)
///    c. ∀ a ∈ S, a + 0 = a = 0 + a (identity)
/// 2. (S, ·, 1) is a monoid:
///    a. ∀ a, b, c ∈ S, (a · b) · c = a · (b · c) (associativity)
///    b. ∀ a ∈ S, a · 1 = a = 1 · a (identity)
/// 3. Multiplication distributes over addition:
///    a. ∀ a, b, c ∈ S, a · (b + c) = (a · b) + (a · c) (left distributivity)
///    b. ∀ a, b, c ∈ S, (a + b) · c = (a · c) + (b · c) (right distributivity)
/// 4. Multiplication by 0 annihilates S:
///    ∀ a ∈ S, 0 · a = 0 = a · 0
pub trait Semiring: AdditiveMonoid + MultiplicativeMonoid + Distributive {}

impl<T> Semiring for T where T: AdditiveMonoid + MultiplicativeMonoid + Distributive {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{One, Zero};

    #[test]
    fn test_z5_semiring() {
        // Test additive abelian group properties
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);

                // Commutativity
                assert_eq!(a + b, b + a);

                // Associativity
                let c = Z5::new((i + j) % 5);
                assert_eq!((a + b) + c, a + (b + c));
            }
        }

        // Test additive identity
        let zero = Z5::zero();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
        }

        // Test multiplicative monoid properties
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);

                // Associativity
                let c = Z5::new((i * j) % 5);
                assert_eq!((a * b) * c, a * (b * c));
            }
        }

        // Test multiplicative identity
        let one = Z5::one();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a * one, a);
            assert_eq!(one * a, a);
        }

        // Test distributivity
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..5 {
                    let a = Z5::new(i);
                    let b = Z5::new(j);
                    let c = Z5::new(k);

                    // Left distributivity
                    assert_eq!(a * (b + c), (a * b) + (a * c));

                    // Right distributivity
                    assert_eq!((a + b) * c, (a * c) + (b * c));
                }
            }
        }

        // Test multiplication by zero
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a * zero, zero);
            assert_eq!(zero * a, zero);
        }
    }

    #[test]
    fn test_z5_implements_semiring() {
        fn assert_semiring<T: Semiring>() {}
        assert_semiring::<Z5>();
    }
}

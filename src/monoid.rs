use crate::semigroup::{AdditiveSemigroup, MultiplicativeSemigroup};
use crate::{ClosedOne, ClosedZero};

/// Represents an Additive Monoid, an algebraic structure with a set, an associative closed addition operation, and an identity element.
///
/// An additive monoid (M, +, 0) consists of:
/// - A set M (represented by the Set trait)
/// - A binary addition operation +: M × M → M that is associative
/// - An identity element 0 ∈ M
///
/// Formal Definition:
/// Let (M, +, 0) be an additive monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a + b) + c = a + (b + c) (associativity)
/// 2. ∀ a ∈ M, a + 0 = 0 + a = a (identity)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a + b is also in M.
/// - Associativity: For all a, b, and c in M, (a + b) + c = a + (b + c).
/// - Identity: There exists an element 0 in M such that for every element a in M, a + 0 = 0 + a = a.
pub trait AdditiveMonoid: AdditiveSemigroup + ClosedZero {}

/// Represents a Multiplicative Monoid, an algebraic structure with a set, an associative closed multiplication operation, and an identity element.
///
/// A multiplicative monoid (M, ∙, 1) consists of:
/// - A set M (represented by the Set trait)
/// - A binary multiplication operation ∙: M × M → M that is associative
/// - An identity element 1 ∈ M
///
/// Formal Definition:
/// Let (M, ∙, 1) be a multiplicative monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∀ a ∈ M, a ∙ 1 = 1 ∙ a = a (identity)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a ∙ b is also in M.
/// - Associativity: For all a, b, and c in M, (a ∙ b) ∙ c = a ∙ (b ∙ c).
/// - Identity: There exists an element 1 in M such that for every element a in M, a ∙ 1 = 1 ∙ a = a.
pub trait MultiplicativeMonoid: MultiplicativeSemigroup + ClosedOne {}

impl<T> AdditiveMonoid for T where T: AdditiveSemigroup + ClosedZero {}

impl<T> MultiplicativeMonoid for T where T: MultiplicativeSemigroup + ClosedOne {}

#[cfg(test)]
mod tests {
    use std::ops::{Add, Mul};

    use crate::concrete::Z5;
    use crate::{AdditiveMonoid, Associative, MultiplicativeMonoid};
    use num_traits::{One, Zero};

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

    impl Associative for Z5 {}

    #[test]
    fn test_z5_additive_monoid() {
        // Test associativity
        let a = Z5::new(2);
        let b = Z5::new(3);
        let c = Z5::new(4);
        assert_eq!((a + b) + c, a + (b + c));

        // Test identity
        let zero = Z5::zero();
        assert_eq!(a + zero, a);
        assert_eq!(zero + a, a);

        // Test closure
        let sum = a + b;
        assert!(matches!(sum, Z5(_)));
    }

    #[test]
    fn test_z5_multiplicative_monoid() {
        // Test associativity
        let a = Z5::new(2);
        let b = Z5::new(3);
        let c = Z5::new(4);
        assert_eq!((a * b) * c, a * (b * c));

        // Test identity
        let one = Z5::one();
        assert_eq!(a * one, a);
        assert_eq!(one * a, a);

        // Test closure
        let product = a * b;
        assert!(matches!(product, Z5(_)));
    }

    #[test]
    fn test_z5_additive_monoid_properties() {
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);
                let zero = Z5::zero();

                // Closure
                assert!(matches!(a + b, Z5(_)));

                // Identity
                assert_eq!(a + zero, a);
                assert_eq!(zero + a, a);
            }
        }
    }

    #[test]
    fn test_z5_multiplicative_monoid_properties() {
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);
                let one = Z5::one();

                // Closure
                assert!(matches!(a * b, Z5(_)));

                // Identity
                assert_eq!(a * one, a);
                assert_eq!(one * a, a);
            }
        }
    }

    #[test]
    fn test_z5_implements_monoids() {
        fn assert_additive_monoid<T: AdditiveMonoid>() {}
        fn assert_multiplicative_monoid<T: MultiplicativeMonoid>() {}

        assert_additive_monoid::<Z5>();
        assert_multiplicative_monoid::<Z5>();
    }
}

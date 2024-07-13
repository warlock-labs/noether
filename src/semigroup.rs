use crate::magma::{AdditiveMagma, MultiplicativeMagma};
use crate::operator::{ClosedAdd, ClosedMul};
use crate::Associative;

/// If this trait is implemented, the object implements Additive Semigroup, an
/// algebraic structure with a set and an associative closed addition operation.
///
/// An additive semigroup (S, +) consists of:
/// - A set S
/// - A binary operation +: S × S → S that is associative
///
/// Formal Definition:
/// Let (S, +) be an additive semigroup. Then:
/// ∀ a, b, c ∈ S, (a + b) + c = a + (b + c) (associativity)
///
/// Properties:
/// - Closure: ∀ a, b ∈ S, a + b ∈ S
/// - Associativity: ∀ a, b, c ∈ S, (a + b) + c = a + (b + c)
pub trait AdditiveSemigroup: AdditiveMagma + ClosedAdd + Associative {}

/// If this trait is implemented, the object implements a Multiplicative Semigroup, an algebraic
/// structure with a set and an associative closed multiplication operation.
///
/// A multiplicative semigroup (S, *) consists of:
/// - A set S
/// - A binary operation ∙: S × S → S that is associative
///
/// Formal Definition:
/// Let (S, *) be a multiplicative semigroup. Then:
/// ∀ a, b, c ∈ S, (a * b) * c = a * (b * c) (associativity)
///
/// Properties:
/// - Closure: ∀ a, b ∈ S, a * b ∈ S
/// - Associativity: ∀ a, b, c ∈ S, (a * b) ∙ c = a * (b * c)
pub trait MultiplicativeSemigroup: MultiplicativeMagma + ClosedMul + Associative {}

// Blanket implementations
impl<T> AdditiveSemigroup for T where T: AdditiveMagma + ClosedAdd + Associative {}
impl<T> MultiplicativeSemigroup for T where T: MultiplicativeMagma + ClosedMul + Associative {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::{Add, Mul};

    // Test structures
    #[derive(Clone, PartialEq, Debug)]
    struct IntegerAdditiveSemigroup(i32);

    #[derive(Clone, PartialEq, Debug)]
    struct StringMultiplicativeSemigroup(String);

    impl Associative for IntegerAdditiveSemigroup {}

    // Implement the necessary traits for IntegerAdditiveSemigroup
    impl Add for IntegerAdditiveSemigroup {
        type Output = Self;
        fn add(self, other: Self) -> Self {
            IntegerAdditiveSemigroup(self.0 + other.0)
        }
    }

    // Implement necessary traits for StringMultiplicativeSemigroup
    impl Mul for StringMultiplicativeSemigroup {
        type Output = Self;
        fn mul(self, other: Self) -> Self {
            StringMultiplicativeSemigroup(self.0 + &other.0)
        }
    }

    #[test]
    fn test_additive_semigroup() {
        let a = IntegerAdditiveSemigroup(2);
        let b = IntegerAdditiveSemigroup(3);
        let c = IntegerAdditiveSemigroup(4);

        // Test associativity
        assert_eq!((a.clone() + b.clone()) + c.clone(), a + (b + c));
    }

    #[test]
    fn test_multiplicative_semigroup() {
        let a = StringMultiplicativeSemigroup("a".to_string());
        let b = StringMultiplicativeSemigroup("b".to_string());
        let c = StringMultiplicativeSemigroup("c".to_string());

        // Test associativity
        assert_eq!((a.clone() * b.clone()) * c.clone(), a * (b * c));
    }
}

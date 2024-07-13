use crate::{ClosedAdd, ClosedMul, Set};

/// Represents an Additive Magma, an algebraic structure with a set and a closed addition operation.
///
/// An additive magma (M, +) consists of:
/// - A set M (represented by the Set trait)
/// - A binary addition operation +: M × M → M
///
/// Formal Definition:
/// Let (M, +) be an additive magma. Then:
/// ∀ a, b ∈ M, a + b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a + b is also in M.
///
/// Note: An additive magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait AdditiveMagma: Set + ClosedAdd {}

/// Represents a Multiplicative Magma, an algebraic structure with a set and a closed multiplication operation.
///
/// A multiplicative magma (M, *) consists of:
/// - A set M (represented by the Set trait)
/// - A binary multiplication operation *: M × M → M
///
/// Formal Definition:
/// Let (M, *) be a multiplicative magma. Then:
/// ∀ a, b ∈ M, a × b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a * b is also in M.
///
/// Note: A multiplicative magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait MultiplicativeMagma: Set + ClosedMul {}

impl<T> AdditiveMagma for T where T: Set + ClosedAdd {}
impl<T> MultiplicativeMagma for T where T: Set + ClosedMul {}

#[cfg(test)]
mod tests {
    // Using a string here is an interesting way to test as the elements can form a set.
    // However, we can make non-associative addition and multiplication operations.
    use super::*;

    #[derive(Clone, PartialEq, Debug)]
    struct StringMagma(String);

    impl Set for StringMagma {
        type Element = char;

        fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        fn contains(&self, element: &Self::Element) -> bool {
            self.0.contains(*element)
        }

        fn empty() -> Self {
            StringMagma(String::new())
        }

        fn singleton(element: Self::Element) -> Self {
            StringMagma(element.to_string())
        }

        fn union(&self, other: &Self) -> Self {
            StringMagma(self.0.clone() + &other.0)
        }

        fn intersection(&self, other: &Self) -> Self {
            StringMagma(self.0.chars().filter(|c| other.0.contains(*c)).collect())
        }

        fn difference(&self, other: &Self) -> Self {
            StringMagma(self.0.chars().filter(|c| !other.0.contains(*c)).collect())
        }

        fn symmetric_difference(&self, other: &Self) -> Self {
            let union = self.union(other);
            let intersection = self.intersection(other);
            union.difference(&intersection)
        }

        fn is_subset(&self, other: &Self) -> bool {
            self.0.chars().all(|c| other.0.contains(c))
        }

        fn is_equal(&self, other: &Self) -> bool {
            self.0 == other.0
        }

        fn cardinality(&self) -> Option<usize> {
            Some(self.0.len())
        }

        fn is_finite(&self) -> bool {
            true
        }
    }

    impl std::ops::Add for StringMagma {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            StringMagma(self.0 + &other.0)
        }
    }

    impl std::ops::Mul for StringMagma {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            StringMagma(self.0.chars().chain(other.0.chars()).collect())
        }
    }

    #[test]
    fn test_additive_magma() {
        let a = StringMagma("Hello".to_string());
        let b = StringMagma(" World".to_string());
        let result = a + b;
        assert_eq!(result, StringMagma("Hello World".to_string()));
    }

    #[test]
    fn test_multiplicative_magma() {
        let a = StringMagma("Hello".to_string());
        let b = StringMagma("World".to_string());
        let result = a * b;
        assert_eq!(result, StringMagma("HelloWorld".to_string()));
    }

    #[test]
    fn test_set_operations() {
        let set = StringMagma("Hello".to_string());
        assert!(!set.is_empty());
        assert!(set.contains(&'H'));
        assert!(!set.contains(&'W'));
    }
}

use crate::{ClosedAdd, ClosedMul, Set};

/// Represents an Additive Magma, an algebraic structure with a set and a closed addition operation.
///
/// An additive magma (M, +) consists of:
/// - A set M (represented by the Set trait)
/// - A binary addition operation +: M × M → M (represented by the ClosedAdd trait)
///
/// Formal Definition:
/// Let (M, +) be an additive magma. Then:
/// ∀ a, b ∈ M, a + b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a + b is also in M.
///
/// Note: An additive magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait AdditiveMagma<T>: Set<T> + ClosedAdd {}

/// Represents a Multiplicative Magma, an algebraic structure with a set and a closed multiplication operation.
///
/// A multiplicative magma (M, *) consists of:
/// - A set M (represented by the Set trait)
/// - A binary multiplication operation *: M × M → M (represented by the ClosedMul trait)
///
/// Formal Definition:
/// Let (M, ×) be a multiplicative magma. Then:
/// ∀ a, b ∈ M, a × b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a * b is also in M.
///
/// Note: A multiplicative magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait MultiplicativeMagma<T>: Set<T> + ClosedMul {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::{Add, Mul};

    #[derive(Clone, PartialEq, Debug)]
    struct StringMagma(String);

    impl Set<String> for StringMagma {
        fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        fn contains(&self, element: &String) -> bool {
            self.0 == *element
        }

        fn empty() -> Self {
            StringMagma(String::new())
        }

        fn singleton(element: String) -> Self {
            StringMagma(element)
        }

        fn union(&self, other: &Self) -> Self {
            StringMagma(self.0.clone() + &other.0)
        }

        fn intersection(&self, other: &Self) -> Self {
            if self == other {
                self.clone()
            } else {
                Self::empty()
            }
        }

        fn difference(&self, other: &Self) -> Self {
            if self == other {
                Self::empty()
            } else {
                self.clone()
            }
        }

        fn symmetric_difference(&self, other: &Self) -> Self {
            if self == other {
                Self::empty()
            } else {
                self.union(other)
            }
        }

        fn is_subset(&self, other: &Self) -> bool {
            self == other
        }

        fn is_equal(&self, other: &Self) -> bool {
            self == other
        }

        fn cardinality(&self) -> Option<usize> {
            Some(if self.is_empty() { 0 } else { 1 })
        }

        fn is_finite(&self) -> bool {
            true
        }
    }

    impl Add for StringMagma {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            StringMagma(self.0 + &rhs.0)
        }
    }

    impl Mul for StringMagma {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            StringMagma(self.0.repeat(rhs.0.len().max(1)))
        }
    }

    impl AdditiveMagma<String> for StringMagma {}
    impl MultiplicativeMagma<String> for StringMagma {}

    #[test]
    fn test_additive_magma() {
        let a = StringMagma("Hello".to_string());
        let b = StringMagma("World".to_string());

        // Test closure property
        let c = a.clone() + b.clone();
        assert_eq!(c, StringMagma("HelloWorld".to_string()));
        assert!(c.contains(&"HelloWorld".to_string()));

        // Test non-commutativity
        let d = b.clone() + a.clone();
        assert_eq!(d, StringMagma("WorldHello".to_string()));
        assert_ne!(c, d);

        // Test non-associativity
        let e = StringMagma("!".to_string());
        let f = (a.clone() + b.clone()) + e.clone();
        let g = a.clone() + (b.clone() + e.clone());
        assert_eq!(f, StringMagma("HelloWorld!".to_string()));
        assert_eq!(g, StringMagma("HelloWorld!".to_string()));
        assert_eq!(f, g); // In this case, it happens to be associative, but it's not guaranteed for all string concatenations
    }

    #[test]
    fn test_multiplicative_magma() {
        let a = StringMagma("Hello".to_string());
        let b = StringMagma("Wor".to_string());
        let e = StringMagma("!".to_string());

        // Test closure property
        let c = a.clone() * b.clone();
        assert_eq!(c, StringMagma("HelloHelloHello".to_string()));
        assert!(c.contains(&"HelloHelloHello".to_string()));

        // Test non-commutativity
        let d = b.clone() * a.clone();
        assert_eq!(d, StringMagma("WorWorWorWorWor".to_string()));
        assert_ne!(c, d);

        // Test non-associativity
        let f = (a.clone() * b.clone()) * e.clone();
        let g = a.clone() * (b.clone() * e);
        assert_eq!(f, StringMagma("HelloHelloHello".to_string()));
        assert_eq!(g, StringMagma("HelloHelloHello".to_string()));
        assert_eq!(f, g); // In this case, it happens to be associative, but it's not guaranteed for all string multiplications
    }
}

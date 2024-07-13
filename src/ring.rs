use crate::{AdditiveAbelianGroup, Distributive, MultiplicativeMonoid};

/// Represents a Ring, an algebraic structure with two binary operations (addition and multiplication)
/// that satisfy certain axioms.
///
/// A ring (R, +, ·) consists of:
/// - A set R
/// - Two binary operations + (addition) and · (multiplication) on R
///
/// Formal Definition:
/// Let (R, +, ·) be a ring. Then:
/// 1. (R, +) is an abelian group:
///    a. ∀ a, b, c ∈ R, (a + b) + c = a + (b + c) (associativity)
///    b. ∀ a, b ∈ R, a + b = b + a (commutativity)
///    c. ∃ 0 ∈ R, ∀ a ∈ R, a + 0 = 0 + a = a (identity)
///    d. ∀ a ∈ R, ∃ -a ∈ R, a + (-a) = (-a) + a = 0 (inverse)
/// 2. (R, ·) is a monoid:
///    a. ∀ a, b, c ∈ R, (a · b) · c = a · (b · c) (associativity)
///    b. ∃ 1 ∈ R, ∀ a ∈ R, 1 · a = a · 1 = a (identity)
/// 3. Multiplication is distributive over addition:
///    a. ∀ a, b, c ∈ R, a · (b + c) = (a · b) + (a · c) (left distributivity)
///    b. ∀ a, b, c ∈ R, (a + b) · c = (a · c) + (b · c) (right distributivity)
pub trait Ring: AdditiveAbelianGroup + MultiplicativeMonoid + Distributive {}

impl<T> Ring for T where T: AdditiveAbelianGroup + MultiplicativeMonoid + Distributive {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{One, Zero};

    #[test]
    fn test_z5_ring() {
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
    }

    #[test]
    fn test_z5_implements_ring() {
        fn assert_ring<T: Ring>() {}
        assert_ring::<Z5>();
    }
}

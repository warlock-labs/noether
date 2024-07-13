use crate::integral_domain::IntegralDomain;

/// Represents a Unique Factorization Domain (UFD), an integral domain where every non-zero
/// non-unit element has a unique factorization into irreducible elements.
///
/// A UFD (R, +, ·) is an integral domain that satisfies:
/// 1. Every non-zero non-unit element can be factored into irreducible elements.
/// 2. This factorization is unique up to order and associates.
///
/// Formal Definition:
/// Let R be an integral domain. R is a UFD if:
/// 1. For every non-zero non-unit a ∈ R, there exist irreducible elements p₁, ..., pₙ such that
///    a = p₁ · ... · pₙ
/// 2. If a = p₁ · ... · pₙ = q₁ · ... · qₘ are two factorizations of a into irreducible elements,
///    then n = m and there exists a bijection σ: {1, ..., n} → {1, ..., n} such that pᵢ is
///    associated to qₛᵢ for all i.
pub trait UniqueFactorizationDomain: IntegralDomain {}

impl<T> UniqueFactorizationDomain for T where T: IntegralDomain {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{One, Zero};

    fn is_irreducible(a: &Z5) -> bool {
        !a.is_zero() && !a.is_one()
    }

    fn factor(a: &Z5) -> Vec<Z5> {
        if a.is_zero() || a.is_one() {
            vec![*a]
        } else {
            vec![*a] // In Z5, all non-zero, non-one elements are irreducible
        }
    }

    fn are_associates(a: &Z5, b: &Z5) -> bool {
        !a.is_zero() && !b.is_zero()
    }

    fn check_unique_factorization(a: &Z5) -> bool {
        let factorization = factor(a);

        if a.is_zero() || a.is_one() {
            factorization.len() == 1 && factorization[0] == *a
        } else {
            factorization.len() == 1 && is_irreducible(&factorization[0])
        }
    }

    #[test]
    fn test_z5_ufd() {
        // Test irreducibility
        assert!(!is_irreducible(&Z5::new(0)));
        assert!(!is_irreducible(&Z5::new(1)));
        assert!(is_irreducible(&Z5::new(2)));
        assert!(is_irreducible(&Z5::new(3)));
        assert!(is_irreducible(&Z5::new(4)));

        // Test factorization
        assert_eq!(factor(&Z5::new(0)), vec![Z5::new(0)]);
        assert_eq!(factor(&Z5::new(1)), vec![Z5::new(1)]);
        assert_eq!(factor(&Z5::new(2)), vec![Z5::new(2)]);
        assert_eq!(factor(&Z5::new(3)), vec![Z5::new(3)]);
        assert_eq!(factor(&Z5::new(4)), vec![Z5::new(4)]);

        // Test associates
        for i in 1..5 {
            for j in 1..5 {
                assert!(are_associates(&Z5::new(i), &Z5::new(j)));
            }
        }

        // Test unique factorization
        for i in 0..5 {
            assert!(check_unique_factorization(&Z5::new(i)));
        }
    }

    #[test]
    fn test_z5_implements_ufd() {
        fn assert_ufd<T: UniqueFactorizationDomain>() {}
        assert_ufd::<Z5>();
    }
}

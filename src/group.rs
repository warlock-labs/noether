use crate::{ClosedInv, ClosedNeg};
use crate::monoid::{AdditiveMonoid, MultiplicativeMonoid};

/// Represents an Additive Group, an algebraic structure with a set, an associative closed addition operation,
/// an identity element, and inverses for all elements.
///
/// An additive group (G, +) consists of:
/// - A set G
/// - A binary operation +: G × G → G that is associative
/// - An identity element 0 ∈ G
/// - For each a ∈ G, an inverse element -a ∈ G such that a + (-a) = (-a) + a = 0
///
/// Formal Definition:
/// Let (G, +) be an additive group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
pub trait AdditiveGroup: AdditiveMonoid + ClosedNeg {}

/// Represents a Multiplicative Group, an algebraic structure with a set, an associative closed multiplication operation,
/// an identity element, and inverses for all elements.
///
/// A multiplicative group (G, ∙) consists of:
/// - A set G
/// - A binary operation ∙: G × G → G that is associative
/// - An identity element 1 ∈ G
/// - For each a ∈ G, an inverse element a⁻¹ ∈ G such that a ∙ a⁻¹ = a⁻¹ ∙ a = 1
///
/// Formal Definition:
/// Let (G, ∙) be a multiplicative group. Then:
/// 1. ∀ a, b, c ∈ G, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 ∙ a = a ∙ 1 = a (identity)
/// 3. ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∙ a⁻¹ = a⁻¹ ∙ a = 1 (inverse)
pub trait MultiplicativeGroup: MultiplicativeMonoid + ClosedInv {}

impl<T> AdditiveGroup for T where T: AdditiveMonoid + ClosedNeg {}
impl<T> MultiplicativeGroup for T where T: MultiplicativeMonoid + ClosedInv {}

#[cfg(test)]
mod tests {
    use crate::concrete::Z5;
    use num_traits::{Zero, One, Inv};
    use crate::group::{AdditiveGroup, MultiplicativeGroup};

    #[test]
    fn test_z5_additive_group() {
        // Test associativity
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..5 {
                    let a = Z5::new(i);
                    let b = Z5::new(j);
                    let c = Z5::new(k);
                    assert_eq!((a + b) + c, a + (b + c));
                }
            }
        }

        // Test identity
        let zero = Z5::zero();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
        }

        // Test inverse
        for i in 0..5 {
            let a = Z5::new(i);
            let neg_a = -a;
            assert_eq!(a + neg_a, zero);
            assert_eq!(neg_a + a, zero);
        }
    }

    #[test]
    fn test_z5_multiplicative_group() {
        // Test associativity
        for i in 1..5 {  // Skip 0 as it's not part of the multiplicative group
            for j in 1..5 {
                for k in 1..5 {
                    let a = Z5::new(i);
                    let b = Z5::new(j);
                    let c = Z5::new(k);
                    assert_eq!((a * b) * c, a * (b * c));
                }
            }
        }

        // Test identity
        let one = Z5::one();
        for i in 1..5 {
            let a = Z5::new(i);
            assert_eq!(a * one, a);
            assert_eq!(one * a, a);
        }

        // Test inverse
        for i in 1..5 {
            let a = Z5::new(i);
            let inv_a = a.inv();
            assert_eq!(a * inv_a, one);
            assert_eq!(inv_a * a, one);
        }
    }

    #[test]
    fn test_z5_implements_groups() {
        fn assert_additive_group<T: AdditiveGroup>() {}
        fn assert_multiplicative_group<T: MultiplicativeGroup>() {}

        assert_additive_group::<Z5>();
        assert_multiplicative_group::<Z5>();
    }
}
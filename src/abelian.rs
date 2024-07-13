use crate::group::{AdditiveGroup, MultiplicativeGroup};
use crate::Commutative;

/// Represents an Additive Abelian Group, an algebraic structure with a commutative addition operation.
///
/// An additive abelian group (G, +) is an additive group that also satisfies:
/// - Commutativity: ∀ a, b ∈ G, a + b = b + a
///
/// Formal Definition:
/// Let (G, +) be an additive abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
/// 4. ∀ a, b ∈ G, a + b = b + a (commutativity)
pub trait AdditiveAbelianGroup: AdditiveGroup + Commutative {}

/// Represents a Multiplicative Abelian Group, an algebraic structure with a commutative multiplication operation.
///
/// A multiplicative abelian group (G, ∙) is a multiplicative group that also satisfies:
/// - Commutativity: ∀ a, b ∈ G, a ∙ b = b ∙ a
///
/// Formal Definition:
/// Let (G, ∙) be a multiplicative abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 ∙ a = a ∙ 1 = a (identity)
/// 3. ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∙ a⁻¹ = a⁻¹ ∙ a = 1 (inverse)
/// 4. ∀ a, b ∈ G, a ∙ b = b ∙ a (commutativity)
pub trait MultiplicativeAbelianGroup: MultiplicativeGroup + Commutative {}

impl<T> AdditiveAbelianGroup for T where T: AdditiveGroup + Commutative {}
impl<T> MultiplicativeAbelianGroup for T where T: MultiplicativeGroup + Commutative {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{Inv, One, Zero};

    #[test]
    fn test_z5_additive_abelian_group() {
        // Test commutativity
        for i in 0..5 {
            for j in 0..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);
                assert_eq!(a + b, b + a);
            }
        }

        // Test associativity (inherited from AdditiveGroup)
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

        // Test identity (inherited from AdditiveGroup)
        let zero = Z5::zero();
        for i in 0..5 {
            let a = Z5::new(i);
            assert_eq!(a + zero, a);
            assert_eq!(zero + a, a);
        }

        // Test inverse (inherited from AdditiveGroup)
        for i in 0..5 {
            let a = Z5::new(i);
            let neg_a = -a;
            assert_eq!(a + neg_a, zero);
            assert_eq!(neg_a + a, zero);
        }
    }

    #[test]
    fn test_z5_multiplicative_abelian_group() {
        // Test commutativity
        for i in 1..5 {
            // Skip 0 as it's not part of the multiplicative group
            for j in 1..5 {
                let a = Z5::new(i);
                let b = Z5::new(j);
                assert_eq!(a * b, b * a);
            }
        }

        // Test associativity (inherited from MultiplicativeGroup)
        for i in 1..5 {
            for j in 1..5 {
                for k in 1..5 {
                    let a = Z5::new(i);
                    let b = Z5::new(j);
                    let c = Z5::new(k);
                    assert_eq!((a * b) * c, a * (b * c));
                }
            }
        }

        // Test identity (inherited from MultiplicativeGroup)
        let one = Z5::one();
        for i in 1..5 {
            let a = Z5::new(i);
            assert_eq!(a * one, a);
            assert_eq!(one * a, a);
        }

        // Test inverse (inherited from MultiplicativeGroup)
        for i in 1..5 {
            let a = Z5::new(i);
            let inv_a = a.inv();
            assert_eq!(a * inv_a, one);
            assert_eq!(inv_a * a, one);
        }
    }

    #[test]
    fn test_z5_implements_abelian_groups() {
        fn assert_additive_abelian_group<T: AdditiveAbelianGroup>() {}
        fn assert_multiplicative_abelian_group<T: MultiplicativeAbelianGroup>() {}

        assert_additive_abelian_group::<Z5>();
        assert_multiplicative_abelian_group::<Z5>();
    }
}

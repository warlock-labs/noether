//! Group theory structures.
//!
//! This module defines traits for algebraic structures from magmas to groups,
//! implementing the algebraic hierarchy up to abelian groups.

use crate::operations::*;
use crate::sets::Set;

/// Represents an Additive Magma, an algebraic structure with a set and a closed addition operation.
///
/// # Mathematical Definition
/// An additive magma (M, +) consists of:
/// - A set M
/// - A binary operation +: M × M → M
///
/// # Formal Definition
/// Let (M, +) be an additive magma. Then:
/// ∀ a, b ∈ M, a + b ∈ M (closure property)
///
/// # Properties
/// - Closure: For all a and b in M, the result of a + b is also in M.
pub trait AdditiveMagma: Set + ClosedAdd + ClosedAddAssign {}

/// Represents a Multiplicative Magma, an algebraic structure with a set and a closed multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative magma (M, *) consists of:
/// - A set M
/// - A binary operation *: M × M → M
///
/// # Formal Definition
/// Let (M, *) be a multiplicative magma. Then:
/// ∀ a, b ∈ M, a * b ∈ M (closure property)
///
/// # Properties
/// - Closure: For all a and b in M, the result of a * b is also in M.
pub trait MultiplicativeMagma: Set + ClosedMul + ClosedMulAssign {}

/// Represents an Additive Semigroup, an algebraic structure with an associative addition operation.
///
/// # Mathematical Definition
/// An additive semigroup (S, +) is an additive magma where:
/// - The operation + is associative
///
/// # Formal Definition
/// Let (S, +) be an additive semigroup. Then:
/// ∀ a, b, c ∈ S, (a + b) + c = a + (b + c) (associativity)
///
/// # Properties
/// - Associativity: For all a, b, and c in S, (a + b) + c = a + (b + c)
pub trait AdditiveSemigroup: AdditiveMagma + AssociativeAddition {}

/// Represents a Multiplicative Semigroup, an algebraic structure with an associative multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative semigroup (S, *) is a multiplicative magma where:
/// - The operation * is associative
///
/// # Formal Definition
/// Let (S, *) be a multiplicative semigroup. Then:
/// ∀ a, b, c ∈ S, (a * b) * c = a * (b * c) (associativity)
///
/// # Properties
/// - Associativity: For all a, b, and c in S, (a * b) * c = a * (b * c)
pub trait MultiplicativeSemigroup: MultiplicativeMagma + AssociativeMultiplication {}

/// Represents an Additive Monoid, an algebraic structure with an associative addition operation and an identity element.
///
/// # Mathematical Definition
/// An additive monoid (M, +, 0) is an additive semigroup with:
/// - An identity element 0 ∈ M
///
/// # Formal Definition
/// Let (M, +, 0) be an additive monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a + b) + c = a + (b + c) (associativity)
/// 2. ∀ a ∈ M, a + 0 = 0 + a = a (identity)
///
/// # Properties
/// - Identity: There exists an element 0 in M such that for every element a in M, a + 0 = 0 + a = a
pub trait AdditiveMonoid: AdditiveSemigroup + ClosedZero {}

/// Represents a Multiplicative Monoid, an algebraic structure with an associative multiplication operation and an identity element.
///
/// # Mathematical Definition
/// A multiplicative monoid (M, *, 1) is a multiplicative semigroup with:
/// - An identity element 1 ∈ M
///
/// # Formal Definition
/// Let (M, *, 1) be a multiplicative monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a * b) * c = a * (b * c) (associativity)
/// 2. ∀ a ∈ M, a * 1 = 1 * a = a (identity)
///
/// # Properties
/// - Identity: There exists an element 1 in M such that for every element a in M, a * 1 = 1 * a = a
pub trait MultiplicativeMonoid: MultiplicativeSemigroup + ClosedOne {}

/// Represents an Additive Group, an algebraic structure with an associative addition operation, an identity element, and inverses.
///
/// # Mathematical Definition
/// An additive group (G, +, 0) is an additive monoid where:
/// - Every element has an additive inverse
///
/// # Formal Definition
/// Let (G, +, 0) be an additive group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
///
/// # Properties
/// - Inverse: For every element a in G, there exists an element -a in G such that a + (-a) = (-a) + a = 0
pub trait AdditiveGroup: AdditiveMonoid + ClosedNeg + ClosedSub + ClosedSubAssign {}

/// Represents a Multiplicative Group, an algebraic structure with an associative multiplication operation, an identity element, and inverses.
///
/// # Mathematical Definition
/// A multiplicative group (G, *, 1) is a multiplicative monoid where:
/// - Every non-zero element has a multiplicative inverse
///
/// # Formal Definition
/// Let (G, *, 1) be a multiplicative group. Then:
/// 1. ∀ a, b, c ∈ G, (a * b) * c = a * (b * c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 * a = a * 1 = a (identity)
/// 3. ∀ a ∈ G, a ≠ 0, ∃ a^(-1) ∈ G, a * a^(-1) = a^(-1) * a = 1 (inverse)
///
/// # Properties
/// - Inverse: For every non-zero element a in G, there exists an element a^(-1) in G such that a * a^(-1) = a^(-1) * a = 1
pub trait MultiplicativeGroup:
    MultiplicativeMonoid + ClosedInv + ClosedDiv + ClosedDivAssign
{
}

/// Represents an Additive Abelian Group, an algebraic structure with a commutative addition operation.
///
/// # Mathematical Definition
/// An additive abelian group is an additive group where:
/// - The addition operation is commutative
///
/// # Formal Definition
/// Let (G, +, 0) be an additive abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
/// 4. ∀ a, b ∈ G, a + b = b + a (commutativity)
///
/// # Properties
/// - Commutativity: For all a and b in G, a + b = b + a
pub trait AdditiveAbelianGroup: AdditiveGroup + CommutativeAddition {}

/// Represents a Multiplicative Abelian Group, an algebraic structure with a commutative multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative abelian group is a multiplicative group where:
/// - The multiplication operation is commutative
///
/// # Formal Definition
/// Let (G, *, 1) be a multiplicative abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a * b) * c = a * (b * c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 * a = a * 1 = a (identity)
/// 3. ∀ a ∈ G, a ≠ 0, ∃ a^(-1) ∈ G, a * a^(-1) = a^(-1) * a = 1 (inverse)
/// 4. ∀ a, b ∈ G, a * b = b * a (commutativity)
///
/// # Properties
/// - Commutativity: For all a and b in G, a * b = b * a
pub trait MultiplicativeAbelianGroup: MultiplicativeGroup + CommutativeMultiplication {}

// Blanket implementations
impl<T: Set + ClosedAdd + ClosedAddAssign> AdditiveMagma for T {}
impl<T: Set + ClosedMul + ClosedMulAssign> MultiplicativeMagma for T {}
impl<T: AdditiveMagma + AssociativeAddition> AdditiveSemigroup for T {}
impl<T: MultiplicativeMagma + AssociativeMultiplication> MultiplicativeSemigroup for T {}
impl<T: AdditiveSemigroup + ClosedZero> AdditiveMonoid for T {}
impl<T: MultiplicativeSemigroup + ClosedOne> MultiplicativeMonoid for T {}
impl<T: AdditiveMonoid + ClosedNeg + ClosedSub + ClosedSubAssign> AdditiveGroup for T {}
impl<T: MultiplicativeMonoid + ClosedInv + ClosedDiv + ClosedDivAssign> MultiplicativeGroup for T {}
impl<T: AdditiveGroup + CommutativeAddition> AdditiveAbelianGroup for T {}
impl<T: MultiplicativeGroup + CommutativeMultiplication> MultiplicativeAbelianGroup for T {}

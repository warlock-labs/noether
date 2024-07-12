//! # Noether
//!
//! Noether provides traits and blanket implementations for algebraic structures,
//! from basic ones like magmas to more complex ones like fields. It leans heavily on
//! the basic traits available in std::ops and num_traits.
//!
//! The goal is to provide a common interface for working with algebraic structures
//! in Rust.
//!
//! Interestingly, these traits can be used to categorize implementations of various
//! structs based on the properties they satisfy, and be applied in most cases for
//! anything from scalar values to n-dimensional arrays.
//!
//! ## Binary Operations and Their Properties
//!
//! An algebraic structure consists of a set with one or more binary operations.
//! Let 𝑆 be a set (Self) and • be a binary operation on 𝑆.
//! Here are the key properties a binary operation may possess, organized from simplest to most complex:
//!
//! - (Closure) ∀ a, b ∈ 𝑆, a • b ∈ 𝑆
//! - (Totality) ∀ a, b ∈ 𝑆, a • b is defined
//! - (Commutativity) ∀ a, b ∈ 𝑆, a • b = b • a
//! - (Associativity) ∀ a, b, c ∈ 𝑆, (a • b) • c = a • (b • c)
//! - (Idempotence) ∀ a ∈ 𝑆, a • a = a
//! - (Identity) ∃ e ∈ 𝑆, ∀ a ∈ 𝑆, e • a = a • e = a
//! - (Inverses) ∀ a ∈ 𝑆, ∃ b ∈ 𝑆, a • b = b • a = e (where e is the identity)
//! - (Cancellation) ∀ a, b, c ∈ 𝑆, a • b = a • c ⇒ b = c (a ≠ 0 if ∃ zero element)
//! - (Divisibility) ∀ a, b ∈ 𝑆, ∃ x ∈ 𝑆, a • x = b
//! - (Regularity) ∀ a ∈ 𝑆, ∃ x ∈ 𝑆, a • x • a = a
//! - (Alternativity) ∀ a, b ∈ 𝑆, (a • a) • b = a • (a • b) ∧ (b • a) • a = b • (a • a)
//! - (Distributivity) ∀ a, b, c ∈ 𝑆, a * (b + c) = (a * b) + (a * c)
//! - (Absorption) ∀ a, b ∈ 𝑆, a * (a + b) = a ∧ a + (a * b) = a
//! - (Monotonicity) ∀ a, b, c ∈ 𝑆, a ≤ b ⇒ a • c ≤ b • c ∧ c • a ≤ c • b
//! - (Modularity) ∀ a, b, c ∈ 𝑆, a ≤ c ⇒ a ∨ (b ∧ c) = (a ∨ b) ∧ c
//! - (Switchability) ∀ x, y, z ∈ S, (x + y) * z = x + (y * z)
//! - (Min/Max Ops) ∀ a, b ∈ S, a ∨ b = min{a,b}, a ∧ b = max{a,b}
//! - (Defect Op) ∀ a, b ∈ S, a *₃ b = a + b - 3
//! - (Continuity) ∀ V ⊆ 𝑆 open, f⁻¹(V) is open (for f: 𝑆 → 𝑆, 𝑆 topological)
//! - (Solvability) ∃ series {Gᵢ} | G = G₀ ▷ G₁ ▷ ... ▷ Gₙ = {e}, [Gᵢ, Gᵢ] ≤ Gᵢ₊₁
//! - (Alg. Closure) ∀ p(x) ∈ 𝑆[x] non-constant, ∃ a ∈ 𝑆 | p(a) = 0
//!
//! In general, checking the properties of the binary operators at compile time
//! which are implemented is a challenge.
//!
//! ## Hierarchy of Scalar Algebraic Structures
//!
//! ```text
//!                               ┌─────┐
//!                               │ Set │
//!                               └──┬──┘
//!                                  │
//!                               ┌──▼──┐
//!                               │Magma│
//!                               └──┬──┘
//!                ┌────────────────┼────────────────┐
//!                │                │                │
//!          ┌─────▼─────┐    ┌─────▼─────┐    ┌─────▼─────┐
//!          │Quasigroup │    │ Semigroup │    │Semilattice│
//!          └─────┬─────┘    └─────┬─────┘    └───────────┘
//!                │                │
//!            ┌───▼───┐        ┌───▼───┐
//!            │ Loop  │        │Monoid │
//!            └───┬───┘        └───┬───┘
//!                │                │
//!                └────────┐ ┌─────┘
//!                         │ │
//!                      ┌──▼─▼──┐
//!                      │ Group │
//!                      └───┬───┘
//!                          │
//!                 ┌────────▼────────┐
//!                 │  Abelian Group  │
//!                 └────────┬────────┘
//!                          │
//!                     ┌────▼────┐
//!                     │Semiring │
//!                     └────┬────┘
//!                          │
//!                     ┌────▼────┐
//!                     │  Ring   │
//!                     └────┬────┘
//!           ┌───────────────────────┐
//!           │                       │
//!     ┌─────▼─────┐           ┌─────▼─────┐
//!     │  Module   │           │Commutative│
//!     └───────────┘           │   Ring    │
//!                             └─────┬─────┘
//!                                   │
//!                          ┌────────▼────────┐
//!                          │ Integral Domain │
//!                          └────────┬────────┘
//!                                   │
//!                     ┌─────────────▼─────────────┐
//!                     │Unique Factorization Domain│
//!                     └─────────────┬─────────────┘
//!                                   │
//!                       ┌───────────▼───────────┐
//!                       │Principal Ideal Domain │
//!                       └───────────┬───────────┘
//!                                   │
//!                          ┌────────▼────────┐
//!                          │Euclidean Domain │
//!                          └────────┬────────┘
//!                                   │
//!                               ┌───▼───┐
//!                               │ Field │────────────────────────┐
//!                               └───┬───┘                        │
//!                         ┌─────────┴──────────┐                 │
//!                         │                    │                 │
//!                   ┌─────▼─────┐        ┌─────▼─────┐     ┌─────▼─────┐
//!                   │   Finite  │        │ Infinite  │     │  Vector   │
//!                   │   Field   │        │   Field   │     │   Space   │
//!                   └─────┬─────┘        └───────────┘     └───────────┘
//!                         │
//!                   ┌─────▼─────┐
//!                   │   Field   │
//!                   │ Extension │
//!                   └─────┬─────┘
//!                         │
//!                   ┌─────▼─────┐
//!                   │ Extension │
//!                   │   Tower   │
//!                   └───────────┘
//! ```

mod operator;

use num_traits::Euclid;
pub use num_traits::{Inv, One, Zero};
pub use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// Trait alias for `Add` with result of type `Self`.
pub trait ClosedAdd<Right = Self>: Sized + Add<Right, Output = Self> {}

/// Trait alias for `Sub` with result of type `Self`.
pub trait ClosedSub<Right = Self>: Sized + Sub<Right, Output = Self> {}

/// Trait alias for `Mul` with result of type `Self`.
pub trait ClosedMul<Right = Self>: Sized + Mul<Right, Output = Self> {}

/// Trait alias for `Div` with result of type `Self`.
pub trait ClosedDiv<Right = Self>: Sized + Div<Right, Output = Self> {}

/// Trait alias for `Neg` with result of type `Self`.
pub trait ClosedNeg: Sized + Neg<Output = Self> {}

/// Trait alias for `Add` and `AddAssign` with result of type `Self`.
pub trait ClosedAddAssign<Right = Self>: ClosedAdd<Right> + AddAssign<Right> {}

/// Trait alias for `Sub` and `SubAssign` with result of type `Self`.
pub trait ClosedSubAssign<Right = Self>: ClosedSub<Right> + SubAssign<Right> {}

/// Trait alias for `Mul` and `MulAssign` with result of type `Self`.
pub trait ClosedMulAssign<Right = Self>: ClosedMul<Right> + MulAssign<Right> {}

/// Trait alias for `Div` and `DivAssign` with result of type `Self`.
pub trait ClosedDivAssign<Right = Self>: ClosedDiv<Right> + DivAssign<Right> {}

/// Trait alias for `Inv` with result of type `Self`.
pub trait ClosedInv: Inv<Output = Self> {}

// Blanket implementations for the closed traits
impl<T, Right> ClosedAdd<Right> for T where T: Add<Right, Output = T> + AddAssign<Right> {}
impl<T, Right> ClosedSub<Right> for T where T: Sub<Right, Output = T> + SubAssign<Right> {}
impl<T, Right> ClosedMul<Right> for T where T: Mul<Right, Output = T> + MulAssign<Right> {}
impl<T, Right> ClosedDiv<Right> for T where T: Div<Right, Output = T> + DivAssign<Right> {}
impl<T> ClosedNeg for T where T: Neg<Output = T> {}
impl<T, Right> ClosedAddAssign<Right> for T where T: ClosedAdd<Right> + AddAssign<Right> {}
impl<T, Right> ClosedSubAssign<Right> for T where T: ClosedSub<Right> + SubAssign<Right> {}
impl<T, Right> ClosedMulAssign<Right> for T where T: ClosedMul<Right> + MulAssign<Right> {}
impl<T, Right> ClosedDivAssign<Right> for T where T: ClosedDiv<Right> + DivAssign<Right> {}
impl<T> ClosedInv for T where T: Inv<Output = T> {}

/// Basic representation of a mathematical set, a collection of distinct objects.
///
/// In set theory, a set is a well-defined collection of distinct objects. These objects
/// are called elements or members of the set. This trait provides methods to work with
/// sets in a way that aligns with fundamental set theory concepts.
///
/// # Set Theory Concepts
///
/// - **Membership**: An object `element` is a member of set `Self` if `element ∈ Self`.
/// - **Empty Set**: The unique set with no elements, denoted as ∅.
/// - **Subset**: A set `Self` is a subset of set `Other`, denoted as `Self ⊆ Other`, if every element of `Self` is also an element of `Other`.
/// - **Set Equality**: Two sets are equal if they have exactly the same elements.
///
/// This trait is meant for sets representing numerics like the natural numbers, integers, real numbers, etc.
/// Represents a mathematical set rather than a broader collection type.
pub trait Set: Sized + Clone + PartialEq {
    /// Checks if the given element is a member of the set.
    fn contains(&self, element: &Self) -> bool;
}

// TODO
// A lot of the weirdness here comes from the fact that we can't
// easily wrap the binary operator and find out if it has certain
// properties, and so we introduce this marker trait
// and the chains of lookalike strucure up to the semiring
// when the two operators unit. This is definitely sub optimal.

/// Marker trait for associative operations.
///
/// An operation • is associative if (a • b) • c = a • (b • c) for all a, b, c in the set.
pub trait Associative {}

/// Marker trait for commutative operations.
///
/// An operation • is commutative if a • b = b • a for all a, b in the set.
pub trait Commutative {}

/// Marker trait for idempotent operations.
///
/// An operation • is idempotent if a • a = a for all a in the set.
pub trait Idempotent {}

/// Represents a set with a closed addition operation (magma).
///
/// A magma is the most basic algebraic structure, consisting of a set with a single binary operation
/// that is closed.
///
/// # Properties
/// - Closure: ∀ a, b ∈ Self, a + b ∈ Self
pub trait AdditiveMagma: Set + ClosedAdd + ClosedAddAssign {}

/// Represents an additive quasigroup.
///
/// A quasigroup is a magma where division is always possible and unique.
///
/// # Properties
/// - Latin Square Property: For any elements a and b, there exist unique elements x and y such that:
///   a + x = b and y + a = b
///
/// TODO: Implement a method to enforce the Latin square property of the Cayley table.
/// This is challenging to express in Rust's type system and may require runtime checks.
pub trait AdditiveQuasigroup: AdditiveMagma {}

impl<T> AdditiveQuasigroup for T where T: AdditiveMagma {}

/// Represents an associative additive magma.
///
/// # Properties
/// - Associativity: ∀ a, b, c ∈ Self, (a + b) + c = a + (b + c)
pub trait AdditiveSemigroup: AdditiveMagma + Associative {}

impl<T> AdditiveSemigroup for T where T: AdditiveMagma + Associative {}

/// Represents an additive quasigroup with an identity element (zero).
///
/// # Properties
/// - Identity Element: ∃ 0 ∈ Self, ∀ a ∈ Self, 0 + a = a + 0 = a
pub trait AdditiveLoop: AdditiveQuasigroup + Zero {}

impl<T> AdditiveLoop for T where T: AdditiveQuasigroup + Zero {}

/// Represents an additive semigroup with an identity element (zero).
///
/// # Properties
/// - Associativity (from Semigroup)
/// - Identity Element: ∃ 0 ∈ Self, ∀ a ∈ Self, 0 + a = a + 0 = a
pub trait AdditiveMonoid: AdditiveSemigroup + Zero {}

impl<T> AdditiveMonoid for T where T: AdditiveSemigroup + Zero {}

/// Represents an additive group.
///
/// A group is a monoid where every element has an inverse.
///
/// # Properties
/// - Associativity and Identity (from Monoid)
/// - Inverses: ∀ a ∈ Self, ∃ -a ∈ Self such that a + (-a) = (-a) + a = 0
///
/// Note: For groups, the quasigroup property is satisfied by the inverse element.
pub trait AdditiveGroup: AdditiveMonoid + AdditiveQuasigroup + ClosedNeg {}

impl<T> AdditiveGroup for T where T: AdditiveMonoid + AdditiveQuasigroup + ClosedNeg {}

/// Represents an additive abelian (commutative) group.
///
/// # Properties
/// - All Group properties
/// - Commutativity: ∀ a, b ∈ Self, a + b = b + a
pub trait AdditiveAbelianGroup: AdditiveGroup + Commutative {}

impl<T> AdditiveAbelianGroup for T where T: AdditiveGroup + Commutative {}

/// Represents a set with a closed multiplication operation (magma).
pub trait MultiplicativeMagma: Set + ClosedMul + ClosedMulAssign {}

impl<T> MultiplicativeMagma for T where T: Set + ClosedMul + ClosedMulAssign {}

/// Represents a multiplicative quasigroup.
///
/// TODO: Implement a method to enforce the Latin square property of the Cayley table.
/// This is challenging to express in Rust's type system and may require runtime checks.
pub trait MultiplicativeQuasigroup: MultiplicativeMagma {}

impl<T> MultiplicativeQuasigroup for T where T: MultiplicativeMagma {}

/// Represents an associative multiplicative magma.
pub trait MultiplicativeSemigroup: MultiplicativeMagma + Associative {}

impl<T> MultiplicativeSemigroup for T where T: MultiplicativeMagma + Associative {}

/// Represents a multiplicative quasigroup with an identity element (one).
pub trait MultiplicativeLoop: MultiplicativeQuasigroup + One {}

impl<T> MultiplicativeLoop for T where T: MultiplicativeQuasigroup + One {}

/// Represents a multiplicative monoid.
///
/// A monoid is a semigroup with an identity element.
pub trait MultiplicativeMonoid: MultiplicativeSemigroup + MultiplicativeQuasigroup + One {}

impl<T> MultiplicativeMonoid for T where T: MultiplicativeSemigroup + MultiplicativeQuasigroup + One {}

/// Represents a multiplicative group.
///
/// A group is a monoid where every non-zero element has a multiplicative inverse.
pub trait MultiplicativeGroup: MultiplicativeMonoid + ClosedInv {}

impl<T> MultiplicativeGroup for T where T: MultiplicativeMonoid + ClosedInv {}

/// Represents a multiplicative abelian (commutative) group.
pub trait MultiplicativeAbelianGroup: MultiplicativeGroup + Commutative {}

impl<T> MultiplicativeAbelianGroup for T where T: MultiplicativeGroup + Commutative {}

/// Represents a semiring.
///
/// A semiring introduces a second binary operation. We now use + and * to distinguish between
/// the two operations.
///
/// # Properties
/// - (Self, +) is a commutative monoid
/// - (Self, *) is a monoid
/// - Distributive property: a * (b + c) = (a * b) + (a * c) and (b + c) * a = (b * a) + (c * a)
/// - Multiplication by additive identity annihilates: 0 * a = a * 0 = 0
pub trait Semiring: AdditiveAbelianGroup + MultiplicativeMonoid {
    // TODO(Figure out how to check the distributive property holds)
}

impl<T> Semiring for T where T: AdditiveAbelianGroup + MultiplicativeMonoid {}

/// Represents a ring.
///
/// A ring is a semiring where the additive structure is an abelian group.
///
/// # Properties
/// - All Semiring properties
/// - (Self, +) is an abelian group
pub trait Ring: Semiring + AdditiveGroup {}

impl<T> Ring for T where T: Semiring + AdditiveGroup {}

/// Represents a commutative ring.
///
/// A commutative ring is a ring where multiplication is commutative.
///
/// # Properties
/// - All Ring properties
/// - Commutativity of multiplication: ∀ a, b ∈ Self, a * b = b * a
pub trait CommutativeRing: Ring + MultiplicativeAbelianGroup {}

impl<T> CommutativeRing for T where T: Ring + MultiplicativeAbelianGroup {}

/// Represents an integral domain.
///
/// An integral domain is a commutative ring with no zero divisors.
///
/// # Properties
/// - All Commutative Ring properties
/// - No zero divisors: If a * b = 0, then a = 0 or b = 0
pub trait IntegralDomain: CommutativeRing {}

impl<T> IntegralDomain for T where T: CommutativeRing {}

/// Represents a Euclidean domain.
///
/// A Euclidean domain is an integral domain equipped with a Euclidean function.
///
/// # Properties
/// - All Integral Domain properties
/// - Euclidean function f: Self \ {0} → ℕ satisfying:
///   1. ∀ a, b ∈ Self, b ≠ 0, ∃ q, r ∈ Self such that a = bq + r, where r = 0 or f(r) < f(b)
///   2. ∀ a, b ∈ Self, b ≠ 0 ⇒ f(a) ≤ f(ab)
pub trait EuclideanDomain: IntegralDomain + Euclid {}

impl<T> EuclideanDomain for T where T: IntegralDomain + Euclid {}

/// Represents a field.
///
/// A field is a commutative ring where every non-zero element has a multiplicative inverse,
/// and the distributive property holds.
///
/// # Properties
/// - All Integral Domain properties
/// - Multiplicative inverses for non-zero elements:
///   ∀ a ∈ Self, a ≠ 0 ⇒ ∃ a⁻¹ ∈ Self such that a * a⁻¹ = a⁻¹ * a = 1
/// - Distributive property: ∀ a, b, c ∈ Self, a * (b + c) = (a * b) + (a * c)
pub trait Field: IntegralDomain + MultiplicativeGroup {}

impl<T> Field for T where T: IntegralDomain + MultiplicativeGroup {}

/// Represents a finite field.
///
/// A finite field is a field with a finite number of elements.
///
/// # Properties
/// - All Field properties
/// - |Self| = p^n where p is prime and n is a positive integer
pub trait FiniteField: Field {
    /// Returns the order (number of elements) of the finite field.
    fn order() -> usize;
}

/// Represents the field of real numbers.
///
/// The real field is the field of real numbers.
///
/// # Properties
/// - All Field properties
/// - Totally ordered: ∀ a, b ∈ ℝ, exactly one of a < b, a = b, or a > b is true
/// - Order-compatible with operations
/// - Dedekind-complete: Every non-empty subset of ℝ with an upper bound has a least upper bound in ℝ
pub trait RealField: Field + PartialOrd {}

impl<T> RealField for T where T: Field + PartialOrd {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::borrow::Cow;

    #[derive(Debug, Clone, PartialEq)]
    struct StringMagma<'a>(Cow<'a, str>);

    impl<'a> Set for StringMagma<'a> {
        fn contains(&self, _: &Self) -> bool {
            true // All strings are valid in our magma
        }
    }

    impl<'a> Add for StringMagma<'a> {
        type Output = Self;

        fn add(self, other: Self) -> Self {
            StringMagma(Cow::Owned(self.0.to_string() + &other.0))
        }
    }

    impl<'a> AddAssign for StringMagma<'a> {
        fn add_assign(&mut self, other: Self) {
            self.0 = Cow::Owned(self.0.to_string() + &other.0);
        }
    }

    impl<'a> AdditiveMagma for StringMagma<'a> {}

    #[test]
    fn test_magma_closure() {
        let a = StringMagma(Cow::Borrowed("Hello"));
        let b = StringMagma(Cow::Borrowed(" World"));
        let _ = a + b; // This should compile and run without issues
    }

    #[test]
    fn test_magma_operation() {
        let a = StringMagma(Cow::Borrowed("Hello"));
        let b = StringMagma(Cow::Borrowed(" World"));
        assert_eq!(a + b, StringMagma(Cow::Borrowed("Hello World")));
    }

    #[test]
    fn test_magma_associativity_not_required() {
        let a = StringMagma(Cow::Borrowed("A"));
        let b = StringMagma(Cow::Borrowed("B"));
        let c = StringMagma(Cow::Borrowed("C"));

        // String concatenation is associative, but magmas don't require this property
        assert_eq!(
            (a.clone() + b.clone()) + c.clone(),
            a.clone() + (b.clone() + c.clone())
        );
    }

    #[test]
    fn test_magma_commutativity_not_required() {
        let a = StringMagma(Cow::Borrowed("Hello"));
        let b = StringMagma(Cow::Borrowed(" World"));

        assert_ne!(a.clone() + b.clone(), b + a);
    }

    #[test]
    fn test_magma_add_assign() {
        let mut a = StringMagma(Cow::Borrowed("Hello"));
        let b = StringMagma(Cow::Borrowed(" World"));
        a += b;
        assert_eq!(a, StringMagma(Cow::Borrowed("Hello World")));
    }

    #[test]
    fn test_magma_with_empty_string() {
        let a = StringMagma(Cow::Borrowed("Hello"));
        let e = StringMagma(Cow::Borrowed(""));

        // Empty string acts like an identity, but magmas don't require an identity
        assert_eq!(a.clone() + e.clone(), a.clone());
        assert_eq!(e + a.clone(), a);
    }
}

//! Ring theory structures.
//!
//! This module defines traits for algebraic structures from rings to integral domains.

use crate::groups::{AdditiveAbelianGroup, MultiplicativeMonoid};
use crate::operations::{ClosedAdd, ClosedMul, Distributive};
use crate::CommutativeMultiplication;
use num_traits::Euclid;

/// Represents a Ring, an algebraic structure with two binary operations (addition and multiplication) that satisfy certain axioms.
///
/// # Mathematical Definition
/// A ring (R, +, ·) consists of:
/// - A set R
/// - Two binary operations + (addition) and · (multiplication) on R
///
/// # Formal Definition
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

/// Represents a Commutative Ring, an algebraic structure where multiplication is commutative.
///
/// # Mathematical Definition
/// A commutative ring (R, +, ·) is a ring where:
/// - The multiplication operation is commutative
///
/// # Formal Definition
/// Let (R, +, ·) be a commutative ring. Then:
/// 1. (R, +, ·) is a ring
/// 2. ∀ a, b ∈ R, a · b = b · a (commutativity of multiplication)
pub trait CommutativeRing: Ring + CommutativeMultiplication {}

/// Represents an Integral Domain, a commutative ring with no zero divisors.
///
/// # Mathematical Definition
/// An integral domain (D, +, ·) is a commutative ring where:
/// - The ring has no zero divisors
///
/// # Formal Definition
/// Let (D, +, ·) be an integral domain. Then:
/// 1. (D, +, ·) is a commutative ring
/// 2. D has no zero divisors:
///    ∀ a, b ∈ D, if a · b = 0, then a = 0 or b = 0
/// 3. The zero element is distinct from the unity:
///    0 ≠ 1
pub trait IntegralDomain: CommutativeRing {}

/// Represents a Unique Factorization Domain (UFD), an integral domain where every non-zero
/// non-unit element has a unique factorization into irreducible elements.
///
/// # Mathematical Definition
/// A UFD (R, +, ·) is an integral domain that satisfies:
/// 1. Every non-zero non-unit element can be factored into irreducible elements.
/// 2. This factorization is unique up to order and associates.
///
/// # Formal Definition
/// Let R be an integral domain. R is a UFD if:
/// 1. For every non-zero non-unit a ∈ R, there exist irreducible elements p₁, ..., pₙ such that
///    a = p₁ · ... · pₙ
/// 2. If a = p₁ · ... · pₙ = q₁ · ... · qₘ are two factorizations of a into irreducible elements,
///    then n = m and there exists a bijection σ: {1, ..., n} → {1, ..., n} such that pᵢ is
///    associated to qₛᵢ for all i.
pub trait UniqueFactorizationDomain: IntegralDomain {}

/// Represents a Principal Ideal Domain (PID), an integral domain where every ideal is principal.
///
/// # Mathematical Definition
/// A Principal Ideal Domain (R, +, ·) is an integral domain where:
/// - Every ideal in R is principal (can be generated by a single element)
///
/// # Formal Definition
/// Let R be an integral domain. R is a PID if for every ideal I ⊆ R, there exists an element a ∈ R
/// such that I = (a) = {ra | r ∈ R}.
pub trait PrincipalIdealDomain: UniqueFactorizationDomain {}

/// Represents a Polynomial over a ring.
///
/// # Mathematical Definition
/// A polynomial over a field F is an expression of the form:
/// a_n * X^n + a_{n-1} * X^{n-1} + ... + a_1 * X + a_0
/// where a_i ∈ F are called the coefficients, and X is the indeterminate.
pub trait Polynomial: Clone + PartialEq + ClosedAdd + ClosedMul + Euclid {
    /// The type of the coefficients of the polynomial.
    type Coefficient: Ring;

    /// Returns the degree of the polynomial.
    fn degree(&self) -> usize;

    /// Gets the coefficient of the term with the given degree.
    fn coefficient(&self, degree: usize) -> Self::Coefficient;
}

// Blanket implementations
impl<T: AdditiveAbelianGroup + MultiplicativeMonoid + Distributive> Ring for T {}
impl<T: Ring + CommutativeMultiplication> CommutativeRing for T {}
impl<T: CommutativeRing> IntegralDomain for T {}
impl<T: IntegralDomain> UniqueFactorizationDomain for T {}
impl<T: UniqueFactorizationDomain> PrincipalIdealDomain for T {}

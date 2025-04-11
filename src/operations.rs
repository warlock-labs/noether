//! Algebraic operations and their properties.
//!
//! This module defines traits for algebraic operations and their properties,
//! such as commutativity, associativity, and distributivity. These properties
//! are fundamental to algebraic structures and define their behavior.
//!
//! # Algebraic Properties
//!
//! - **Closure**: An operation ⊕ on a set S is closed if for all a, b ∈ S, a ⊕ b ∈ S
//! - **Commutativity**: An operation ⊕ is commutative if a ⊕ b = b ⊕ a for all a, b
//! - **Associativity**: An operation ⊕ is associative if (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) for all a, b, c
//! - **Distributivity**: An operation ⊗ distributes over ⊕ if a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c) for all a, b, c
//! - **Identity**: An element e is an identity for ⊕ if e ⊕ a = a ⊕ e = a for all a
//! - **Inverse**: For an element a and identity e, b is an inverse if a ⊕ b = b ⊕ a = e

use num_traits::{Euclid, Inv, One, Zero};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

// A note on the reasons why certain traits are used:
//
// The `Inv` trait is the multiplicative inverse operation.
// The `One` trait is the multiplicative identity operation.
// The `Zero` trait is the additive identity operation.
// The `Neg` trait is the additive inverse operation.

// Marker traits for algebraic properties

/// Marker trait for commutative addition.
///
/// # Mathematical Definition
/// Let (S, +) be an algebraic structure. Addition is commutative if:
/// ∀ a, b ∈ S, a + b = b + a
///
/// # Properties
/// - Commutativity allows elements to be reordered without changing the result
/// - Order insensitivity: a₁ + a₂ + ... + aₙ = aᵢ₁ + aᵢ₂ + ... + aᵢₙ for any permutation i
/// - Geometric interpretation: Vector addition in Euclidean space is commutative
pub trait CommutativeAddition {}

/// Marker trait for commutative multiplication.
///
/// # Mathematical Definition
/// Let (S, ·) be an algebraic structure. Multiplication is commutative if:
/// ∀ a, b ∈ S, a · b = b · a
///
/// # Properties
/// - Commutativity allows factors to be reordered without changing the result
/// - Order insensitivity: a₁ · a₂ · ... · aₙ = aᵢ₁ · aᵢ₂ · ... · aᵢₙ for any permutation i
/// - Counter-example: Matrix multiplication is not generally commutative
pub trait CommutativeMultiplication {}

/// Marker trait for associative addition.
///
/// # Mathematical Definition
/// Let (S, +) be an algebraic structure. Addition is associative if:
/// ∀ a, b, c ∈ S, (a + b) + c = a + (b + c)
///
/// # Properties
/// - Associativity allows operations to be regrouped without changing the result
/// - Enables unambiguous definition of sums without parentheses: a₁ + a₂ + ... + aₙ
/// - Enables parallel computation by splitting operations into independent groups
pub trait AssociativeAddition {}

/// Marker trait for associative multiplication.
///
/// # Mathematical Definition
/// Let (S, ·) be an algebraic structure. Multiplication is associative if:
/// ∀ a, b, c ∈ S, (a · b) · c = a · (b · c)
///
/// # Properties
/// - Associativity allows operations to be regrouped without changing the result
/// - Enables unambiguous definition of products without parentheses: a₁ · a₂ · ... · aₙ
/// - Function composition is an example of an associative operation: (f ∘ g) ∘ h = f ∘ (g ∘ h)
pub trait AssociativeMultiplication {}

/// Marker trait for distributive multiplication over addition.
///
/// # Mathematical Definition
/// Let (S, +, ·) be an algebraic structure with two operations. Multiplication
/// distributes over addition if:
///
/// For all a, b, c ∈ S:
/// - Left distributivity: a · (b + c) = (a · b) + (a · c)
/// - Right distributivity: (a + b) · c = (a · c) + (b · c)
///
/// # Properties
/// - Enables factorization and expansion of expressions
/// - Fundamental property in rings and fields
/// - Matrix multiplication distributes over matrix addition
pub trait Distributive {}

// Closed operation traits

/// Trait for closed addition operation.
///
/// # Mathematical Definition
/// An addition operation + on a set S is closed if:
/// ∀ a, b ∈ S, a + b ∈ S
///
/// This means the result of the operation always remains within the set.
///
/// # Properties
/// - Closure is the first axiom for most algebraic structures
/// - Ensures operations can be chained without leaving the set
/// - Natural numbers are not closed under subtraction, but integers are
pub trait ClosedAdd<Rhs = Self>: Add<Rhs, Output = Self> {}

/// Trait for closed addition operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// An addition operation + on a set S is closed if:
/// ∀ a, b ∈ S, a + b ∈ S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedAddRef<Rhs = Self>: for<'a> Add<&'a Rhs, Output = Self> {}

/// Trait for closed subtraction operation.
///
/// # Mathematical Definition
/// A subtraction operation - on a set S is closed if:
/// ∀ a, b ∈ S, a - b ∈ S
///
/// # Properties
/// - Integers are closed under subtraction, but natural numbers are not
/// - Subtraction is neither associative nor commutative in general
/// - Can be defined as addition of the additive inverse: a - b = a + (-b)
pub trait ClosedSub<Rhs = Self>: Sub<Rhs, Output = Self> {}

/// Trait for closed subtraction operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A subtraction operation - on a set S is closed if:
/// ∀ a, b ∈ S, a - b ∈ S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedSubRef<Rhs = Self>: for<'a> Sub<&'a Rhs, Output = Self> {}

/// Trait for closed multiplication operation.
///
/// # Mathematical Definition
/// A multiplication operation · on a set S is closed if:
/// ∀ a, b ∈ S, a · b ∈ S
///
/// # Properties
/// - Fundamental to the definition of algebraic structures like rings and fields
/// - Natural numbers, integers, rationals, reals, and complex numbers are all closed under multiplication
/// - Many mathematical objects have natural multiplication: matrices, polynomials, functions
pub trait ClosedMul<Rhs = Self>: Mul<Rhs, Output = Self> {}

/// Trait for closed multiplication operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A multiplication operation · on a set S is closed if:
/// ∀ a, b ∈ S, a · b ∈ S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedMulRef<Rhs = Self>: for<'a> Mul<&'a Rhs, Output = Self> {}

/// Trait for closed division operation.
///
/// # Mathematical Definition
/// A division operation / on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, a / b ∈ S
///
/// # Properties
/// - Not always defined for all pairs of elements (division by zero)
/// - Rational, real, and complex numbers are closed under division (except by zero)
/// - Integers are not closed under division
/// - Can be defined as multiplication by the multiplicative inverse: a / b = a · b⁻¹
pub trait ClosedDiv<Rhs = Self>: Div<Rhs, Output = Self> {}

/// Trait for closed division operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A division operation / on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, a / b ∈ S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedDivRef<Rhs = Self>: for<'a> Div<&'a Rhs, Output = Self> {}

/// Trait for closed remainder operation.
///
/// # Mathematical Definition
/// A remainder operation % on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, a % b ∈ S
///
/// # Properties
/// - Fundamental to modular arithmetic and congruence relations
/// - Integers are closed under the remainder operation
/// - In division with remainder, we have: a = (a ÷ b) · b + (a % b), where 0 ≤ a % b < |b|
pub trait ClosedRem<Rhs = Self>: Rem<Rhs, Output = Self> {}

/// Trait for closed remainder operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A remainder operation % on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, a % b ∈ S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedRemRef<Rhs = Self>: for<'a> Rem<&'a Rhs, Output = Self> {}

/// Trait for closed negation operation (additive inverse).
///
/// # Mathematical Definition
/// A negation operation - on a set S is closed if:
/// ∀ a ∈ S, -a ∈ S
///
/// # Properties
/// - For any element a, its negation -a satisfies a + (-a) = 0
/// - Integers, rationals, reals, and complex numbers are closed under negation
/// - Natural numbers are not closed under negation
/// - Essential for the group structure in additive groups
pub trait ClosedNeg: Neg<Output = Self> {}

/// Trait for closed multiplication inverse operation.
///
/// # Mathematical Definition
/// A multiplicative inversion operation ⁻¹ on a set S is closed if:
/// ∀ a ∈ S, a ≠ 0, a⁻¹ ∈ S
///
/// # Properties
/// - For any non-zero element a, its multiplicative inverse a⁻¹ satisfies a · a⁻¹ = 1
/// - Rationals, reals, and complex numbers (excluding 0) are closed under inversion
/// - Integers are not closed under inversion (except for 1 and -1)
/// - Essential for the group structure in multiplicative groups
/// - Critical for the definition of fields and division rings
pub trait ClosedInv: Inv<Output = Self> {}

// Closed assignment operation traits

/// Trait for closed addition assignment operation.
///
/// # Mathematical Definition
/// An addition assignment operation += on a set S is closed if:
/// ∀ a, b ∈ S, after a += b, a remains in S
///
/// # Properties
/// - Provides in-place mutation semantics for the addition operation
/// - Implicitly requires closure of the underlying addition operation
/// - Can be defined semantically as a ← a + b
pub trait ClosedAddAssign<Rhs = Self>: AddAssign<Rhs> {}

/// Trait for closed addition assignment operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// An addition assignment operation += on a set S is closed if:
/// ∀ a, b ∈ S, after a += b, a remains in S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedAddAssignRef<Rhs = Self>: for<'a> AddAssign<&'a Rhs> {}

/// Trait for closed subtraction assignment operation.
///
/// # Mathematical Definition
/// A subtraction assignment operation -= on a set S is closed if:
/// ∀ a, b ∈ S, after a -= b, a remains in S
///
/// # Properties
/// - Provides in-place mutation semantics for the subtraction operation
/// - Implicitly requires closure of the underlying subtraction operation
/// - Can be defined semantically as a ← a - b
pub trait ClosedSubAssign<Rhs = Self>: SubAssign<Rhs> {}

/// Trait for closed subtraction assignment operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A subtraction assignment operation -= on a set S is closed if:
/// ∀ a, b ∈ S, after a -= b, a remains in S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedSubAssignRef<Rhs = Self>: for<'a> SubAssign<&'a Rhs> {}

/// Trait for closed multiplication assignment operation.
///
/// # Mathematical Definition
/// A multiplication assignment operation *= on a set S is closed if:
/// ∀ a, b ∈ S, after a *= b, a remains in S
///
/// # Properties
/// - Provides in-place mutation semantics for the multiplication operation
/// - Implicitly requires closure of the underlying multiplication operation
/// - Can be defined semantically as a ← a · b
pub trait ClosedMulAssign<Rhs = Self>: MulAssign<Rhs> {}

/// Trait for closed multiplication assignment operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A multiplication assignment operation *= on a set S is closed if:
/// ∀ a, b ∈ S, after a *= b, a remains in S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedMulAssignRef<Rhs = Self>: for<'a> MulAssign<&'a Rhs> {}

/// Trait for closed division assignment operation.
///
/// # Mathematical Definition
/// A division assignment operation /= on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, after a /= b, a remains in S
///
/// # Properties
/// - Provides in-place mutation semantics for the division operation
/// - Implicitly requires closure of the underlying division operation
/// - Can be defined semantically as a ← a / b
pub trait ClosedDivAssign<Rhs = Self>: DivAssign<Rhs> {}

/// Trait for closed division assignment operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A division assignment operation /= on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, after a /= b, a remains in S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedDivAssignRef<Rhs = Self>: for<'a> DivAssign<&'a Rhs> {}

/// Trait for closed remainder assignment operation.
///
/// # Mathematical Definition
/// A remainder assignment operation %= on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, after a %= b, a remains in S
///
/// # Properties
/// - Provides in-place mutation semantics for the remainder operation
/// - Implicitly requires closure of the underlying remainder operation
/// - Can be defined semantically as a ← a % b
pub trait ClosedRemAssign<Rhs = Self>: RemAssign<Rhs> {}

/// Trait for closed remainder assignment operation with the right-hand side as a reference.
///
/// # Mathematical Definition
/// A remainder assignment operation %= on a set S is closed if:
/// ∀ a, b ∈ S, b ≠ 0, after a %= b, a remains in S
///
/// This trait provides the same closure property but allows references for efficiency.
pub trait ClosedRemAssignRef<Rhs = Self>: for<'a> RemAssign<&'a Rhs> {}

/// Trait for types with a closed zero value (additive identity).
///
/// # Mathematical Definition
/// For a set S with an addition operation +, an element 0 ∈ S is an additive identity if:
/// ∀ a ∈ S, a + 0 = 0 + a = a
///
/// # Properties
/// - Zero is the neutral element for addition
/// - Forms the basis for the identity axiom in additive monoids and groups
/// - In number systems: 0
/// - In matrices: the zero matrix (all entries 0)
/// - In functions: the zero function f(x) = 0
pub trait ClosedZero: Zero {}

/// Trait for types with a closed one value (multiplicative identity).
///
/// # Mathematical Definition
/// For a set S with a multiplication operation ·, an element 1 ∈ S is a multiplicative identity if:
/// ∀ a ∈ S, a · 1 = 1 · a = a
///
/// # Properties
/// - One is the neutral element for multiplication
/// - Forms the basis for the identity axiom in multiplicative monoids and groups
/// - In number systems: 1
/// - In matrices: the identity matrix (1s on diagonal, 0s elsewhere)
/// - In functions under composition: the identity function f(x) = x
pub trait ClosedOne: One {}

/// Trait for closed Euclidean division operation.
///
/// # Mathematical Definition
/// Euclidean division on a ring R with Euclidean function φ satisfies:
/// ∀ a, b ∈ R, b ≠ 0, ∃ q, r ∈ R : a = b·q + r ∧ (r = 0 ∨ φ(r) < φ(b))
///
/// # Properties
/// - Produces quotient q and remainder r with r either zero or "smaller" than b
/// - The "smallness" is measured by the Euclidean function φ
/// - Fundamental to the definition of Euclidean domains
/// - Example: For integers, φ(n) = |n|, and r satisfies 0 ≤ r < |b|
pub trait ClosedDivEuclid: Euclid {
    fn div_euclid(self, rhs: Self) -> Self;
}

/// Trait for closed Euclidean remainder operation.
///
/// # Mathematical Definition
/// In Euclidean division, the remainder r satisfies:
/// a = b·q + r, where r = 0 or φ(r) < φ(b)
///
/// # Properties
/// - The remainder r is either zero or "smaller" than the divisor b
/// - For integers: 0 ≤ a % b < |b|
/// - For polynomials: deg(r) < deg(b)
/// - Used in the Euclidean algorithm for computing GCD
pub trait ClosedRemEuclid {
    fn rem_euclid(self, rhs: Self) -> Self;
}

impl<T> ClosedRemEuclid for T
where
    T: Euclid,
{
    fn rem_euclid(self, rhs: Self) -> Self {
        Euclid::rem_euclid(&self, &rhs)
    }
}

// Blanket implementations for basic operation traits
impl<T: Add<Output = T>> ClosedAdd for T {}
impl<T: for<'a> Add<&'a T, Output = T>> ClosedAddRef for T {}
impl<T: Sub<Output = T>> ClosedSub for T {}
impl<T: for<'a> Sub<&'a T, Output = T>> ClosedSubRef for T {}
impl<T: Mul<Output = T>> ClosedMul for T {}
impl<T: for<'a> Mul<&'a T, Output = T>> ClosedMulRef for T {}
impl<T: Div<Output = T>> ClosedDiv for T {}
impl<T: for<'a> Div<&'a T, Output = T>> ClosedDivRef for T {}
impl<T: Rem<Output = T>> ClosedRem for T {}
impl<T: for<'a> Rem<&'a T, Output = T>> ClosedRemRef for T {}
impl<T: Neg<Output = T>> ClosedNeg for T {}
impl<T: Inv<Output = T>> ClosedInv for T {}

// Blanket implementations for assignment operation traits
impl<T: AddAssign> ClosedAddAssign for T {}
impl<T: for<'a> AddAssign<&'a T>> ClosedAddAssignRef for T {}
impl<T: SubAssign> ClosedSubAssign for T {}
impl<T: for<'a> SubAssign<&'a T>> ClosedSubAssignRef for T {}
impl<T: MulAssign> ClosedMulAssign for T {}
impl<T: for<'a> MulAssign<&'a T>> ClosedMulAssignRef for T {}
impl<T: DivAssign> ClosedDivAssign for T {}
impl<T: for<'a> DivAssign<&'a T>> ClosedDivAssignRef for T {}
impl<T: RemAssign> ClosedRemAssign for T {}
impl<T: for<'a> RemAssign<&'a T>> ClosedRemAssignRef for T {}

// Blanket implementations for zero and one
impl<T: Zero> ClosedZero for T {}
impl<T: One> ClosedOne for T {}

//! # Operator Traits for Algebraic Structures
//!
//! This module defines traits for various operators and their properties,
//! providing a foundation for implementing algebraic structures in Rust.
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
//!
//! To be determined:
//!
//! - (Solvability) ∃ series {Gᵢ} | G = G₀ ▷ G₁ ▷ ... ▷ Gₙ = {e}, [Gᵢ, Gᵢ] ≤ Gᵢ₊₁
//! - (Alg. Closure) ∀ p(x) ∈ 𝑆[x] non-constant, ∃ a ∈ 𝑆 | p(a) = 0
//!
//! The traits and blanket implementations provided above serve several important purposes:
//!
//! 1. Closure: All `Closed*` traits ensure that operations on a type always produce a result
//!    of the same type. This is crucial for defining algebraic structures.
//!
//! 2. Reference Operations: The `*Ref` variants of traits allow for more efficient operations
//!    when the right-hand side can be borrowed, which is common in many algorithms.
//!
//! 3. Marker Traits: Traits like `Commutative`, `Associative`, etc., allow types to declare
//!    which algebraic properties they satisfy. This can be used for compile-time checks
//!    and to enable more generic implementations of algorithms.
//!
//! 4. Property Checking: Some marker traits include methods to check if the property holds
//!    for specific values. While not providing compile-time guarantees, these can be
//!    useful for testing and runtime verification.
//!
//! 5. Generic Binary Operations: The `BinaryOp` trait provides a generic way to represent
//!    any binary operation, which can be useful for implementing algorithms that work
//!    with arbitrary binary operations.
//!
//! 6. Automatic Implementation: The blanket implementations ensure that any type satisfying
//!    the basic requirements automatically implements the corresponding closed trait.
//!    This reduces boilerplate and makes the traits easier to use.
//!
//! 7. Extensibility: New types that implement the standard traits (like `Add`, `Sub`, etc.)
//!    will automatically get the closed trait implementations, making the system more
//!    extensible and future-proof.
//!
//! 8. Type Safety: These traits help in catching type-related errors at compile-time,
//!    ensuring that operations maintain closure within the same type.
//!
//! 9. Generic Programming: These traits enable more expressive generic programming,
//!    allowing functions and structs to be generic over types that are closed under
//!    certain operations or satisfy certain algebraic properties.
//!
//! Note that while these blanket implementations cover a wide range of cases, there might
//! be situations where more specific implementations are needed. In such cases, you can
//! still manually implement these traits for your types, and the manual implementations
//! will take precedence over these blanket implementations.

use num_traits::{Euclid, Inv, One, Zero};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

// TODO(These marker traits could actually mean something and check things)

/// Marker trait for commutative operations
pub trait Commutative {}

/// Marker trait for associative operations
pub trait Associative {}

/// Marker trait for idempotent operations
pub trait Idempotent {}

/// Marker trait for operations with inverses for all elements
pub trait Invertible {}

/// Marker trait for operations with the cancellation property
pub trait Cancellative {}

/// Marker trait for regular operations
pub trait Regular {}

/// Marker trait for alternative operations
pub trait Alternative {}

/// Marker trait for distributive operations
pub trait Distributive {}

/// Marker trait for operations with the absorption property
pub trait Absorptive {}

/// Marker trait for monotonic operations
pub trait Monotonic {}

/// Marker trait for modular operations
pub trait Modular {}

/// Marker trait for switchable operations
pub trait Switchable {}

/// Marker trait for defect operations
pub trait DefectOp {}

/// Marker trait for continuous operations
pub trait Continuous {}

/// Marker trait for solvable operations
pub trait Solvability {}

/// Marker trait for algebraically closed operations
pub trait AlgebraicClosure {}

/// Trait for closed addition operation.
pub trait ClosedAdd<Rhs = Self>: Add<Rhs, Output = Self> {}

/// Trait for closed addition operation with the right-hand side as a reference.
pub trait ClosedAddRef<Rhs = Self>: for<'a> Add<&'a Rhs, Output = Self> {}

/// Trait for closed subtraction operation.
pub trait ClosedSub<Rhs = Self>: Sub<Rhs, Output = Self> {}

/// Trait for closed subtraction operation with the right-hand side as a reference.
pub trait ClosedSubRef<Rhs = Self>: for<'a> Sub<&'a Rhs, Output = Self> {}

/// Trait for closed multiplication operation.
pub trait ClosedMul<Rhs = Self>: Mul<Rhs, Output = Self> {}

/// Trait for closed multiplication operation with the right-hand side as a reference.
pub trait ClosedMulRef<Rhs = Self>: for<'a> Mul<&'a Rhs, Output = Self> {}

/// Trait for closed division operation.
pub trait ClosedDiv<Rhs = Self>: Div<Rhs, Output = Self> {}

/// Trait for closed division operation with the right-hand side as a reference.
pub trait ClosedDivRef<Rhs = Self>: for<'a> Div<&'a Rhs, Output = Self> {}

/// Trait for closed remainder operation.
pub trait ClosedRem<Rhs = Self>: Rem<Rhs, Output = Self> {}

/// Trait for closed remainder operation with the right-hand side as a reference.
pub trait ClosedRemRef<Rhs = Self>: for<'a> Rem<&'a Rhs, Output = Self> {}

/// Trait for closed negation operation.
pub trait ClosedNeg: Neg<Output = Self> {}

/// Trait for closed negation operation.
pub trait ClosedInv: Inv<Output = Self> {}

/// Trait for closed addition assignment operation.
pub trait ClosedAddAssign<Rhs = Self>: AddAssign<Rhs> {}

/// Trait for closed addition assignment operation with the right-hand side as a reference.
pub trait ClosedAddAssignRef<Rhs = Self>: for<'a> AddAssign<&'a Rhs> {}

/// Trait for closed subtraction assignment operation.
pub trait ClosedSubAssign<Rhs = Self>: SubAssign<Rhs> {}

/// Trait for closed subtraction assignment operation with the right-hand side as a reference.
pub trait ClosedSubAssignRef<Rhs = Self>: for<'a> SubAssign<&'a Rhs> {}

/// Trait for closed multiplication assignment operation.
pub trait ClosedMulAssign<Rhs = Self>: MulAssign<Rhs> {}

/// Trait for closed multiplication assignment operation with the right-hand side as a reference.
pub trait ClosedMulAssignRef<Rhs = Self>: for<'a> MulAssign<&'a Rhs> {}

/// Trait for closed division assignment operation.
pub trait ClosedDivAssign<Rhs = Self>: DivAssign<Rhs> {}

/// Trait for closed division assignment operation with the right-hand side as a reference.
pub trait ClosedDivAssignRef<Rhs = Self>: for<'a> DivAssign<&'a Rhs> {}

/// Trait for closed remainder assignment operation.
pub trait ClosedRemAssign<Rhs = Self>: RemAssign<Rhs> {}

/// Trait for closed remainder assignment operation with the right-hand side as a reference.
pub trait ClosedRemAssignRef<Rhs = Self>: for<'a> RemAssign<&'a Rhs> {}

/// Trait for closed bitwise AND operation.
pub trait ClosedBitAnd<Rhs = Self>: BitAnd<Rhs, Output = Self> {}

/// Trait for closed bitwise AND operation with the right-hand side as a reference.
pub trait ClosedBitAndRef<Rhs = Self>: for<'a> BitAnd<&'a Rhs, Output = Self> {}

/// Trait for closed bitwise OR operation.
pub trait ClosedBitOr<Rhs = Self>: BitOr<Rhs, Output = Self> {}

/// Trait for closed bitwise OR operation with the right-hand side as a reference.
pub trait ClosedBitOrRef<Rhs = Self>: for<'a> BitOr<&'a Rhs, Output = Self> {}

/// Trait for closed bitwise XOR operation.
pub trait ClosedBitXor<Rhs = Self>: BitXor<Rhs, Output = Self> {}

/// Trait for closed bitwise XOR operation with the right-hand side as a reference.
pub trait ClosedBitXorRef<Rhs = Self>: for<'a> BitXor<&'a Rhs, Output = Self> {}

/// Trait for closed bitwise NOT operation.
pub trait ClosedNot: Not<Output = Self> {}

/// Trait for closed left shift operation.
pub trait ClosedShl<Rhs = Self>: Shl<Rhs, Output = Self> {}

/// Trait for closed left shift operation with the right-hand side as a reference.
pub trait ClosedShlRef<Rhs = Self>: for<'a> Shl<&'a Rhs, Output = Self> {}

/// Trait for closed right shift operation.
pub trait ClosedShr<Rhs = Self>: Shr<Rhs, Output = Self> {}

/// Trait for closed right shift operation with the right-hand side as a reference.
pub trait ClosedShrRef<Rhs = Self>: for<'a> Shr<&'a Rhs, Output = Self> {}

/// Trait for closed bitwise AND assignment operation.
pub trait ClosedBitAndAssign<Rhs = Self>: BitAndAssign<Rhs> {}

/// Trait for closed bitwise AND assignment operation with the right-hand side as a reference.
pub trait ClosedBitAndAssignRef<Rhs = Self>: for<'a> BitAndAssign<&'a Rhs> {}

/// Trait for closed bitwise OR assignment operation.
pub trait ClosedBitOrAssign<Rhs = Self>: BitOrAssign<Rhs> {}

/// Trait for closed bitwise OR assignment operation with the right-hand side as a reference.
pub trait ClosedBitOrAssignRef<Rhs = Self>: for<'a> BitOrAssign<&'a Rhs> {}

/// Trait for closed bitwise XOR assignment operation.
pub trait ClosedBitXorAssign<Rhs = Self>: BitXorAssign<Rhs> {}

/// Trait for closed bitwise XOR assignment operation with the right-hand side as a reference.
pub trait ClosedBitXorAssignRef<Rhs = Self>: for<'a> BitXorAssign<&'a Rhs> {}

/// Trait for closed left shift assignment operation.
pub trait ClosedShlAssign<Rhs = Self>: ShlAssign<Rhs> {}

/// Trait for closed left shift assignment operation with the right-hand side as a reference.
pub trait ClosedShlAssignRef<Rhs = Self>: for<'a> ShlAssign<&'a Rhs> {}

/// Trait for closed right shift assignment operation.
pub trait ClosedShrAssign<Rhs = Self>: ShrAssign<Rhs> {}

/// Trait for closed right shift assignment operation with the right-hand side as a reference.
pub trait ClosedShrAssignRef<Rhs = Self>: for<'a> ShrAssign<&'a Rhs> {}

/// Trait for types with a closed zero value.
pub trait ClosedZero: Zero {}

/// Trait for types with a closed one value.
pub trait ClosedOne: One {}

/// Trait for closed Euclidean division operation
pub trait ClosedDivEuclid: Sized {
    fn div_euclid(self, rhs: Self) -> Self;
}

/// Trait for closed Euclidean remainder operation
pub trait ClosedRemEuclid: Sized {
    fn rem_euclid(self, rhs: Self) -> Self;
}

// Blanket implementations
impl<T> ClosedDivEuclid for T
where
    T: Euclid,
{
    fn div_euclid(self, rhs: Self) -> Self {
        Euclid::div_euclid(&self, &rhs)
    }
}

impl<T> ClosedRemEuclid for T
where
    T: Euclid,
{
    fn rem_euclid(self, rhs: Self) -> Self {
        Euclid::rem_euclid(&self, &rhs)
    }
}

/// Trait for closed minimum operation
pub trait ClosedMin<Rhs = Self>: Sized {
    fn min(self, other: Rhs) -> Self;
}

/// Trait for closed maximum operation
pub trait ClosedMax<Rhs = Self>: Sized {
    fn max(self, other: Rhs) -> Self;
}

impl<T, Rhs> ClosedAdd<Rhs> for T where T: Add<Rhs, Output = T> {}
impl<T, Rhs> ClosedAddRef<Rhs> for T where T: for<'a> Add<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedSub<Rhs> for T where T: Sub<Rhs, Output = T> {}
impl<T, Rhs> ClosedSubRef<Rhs> for T where T: for<'a> Sub<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedMul<Rhs> for T where T: Mul<Rhs, Output = T> {}
impl<T, Rhs> ClosedMulRef<Rhs> for T where T: for<'a> Mul<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedDiv<Rhs> for T where T: Div<Rhs, Output = T> {}
impl<T, Rhs> ClosedDivRef<Rhs> for T where T: for<'a> Div<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedRem<Rhs> for T where T: Rem<Rhs, Output = T> {}
impl<T, Rhs> ClosedRemRef<Rhs> for T where T: for<'a> Rem<&'a Rhs, Output = T> {}
impl<T> ClosedNeg for T where T: Neg<Output = T> {}
impl<T> ClosedInv for T where T: Inv<Output = T> {}

impl<T, Rhs> ClosedAddAssign<Rhs> for T where T: AddAssign<Rhs> {}
impl<T, Rhs> ClosedAddAssignRef<Rhs> for T where T: for<'a> AddAssign<&'a Rhs> {}
impl<T, Rhs> ClosedSubAssign<Rhs> for T where T: SubAssign<Rhs> {}
impl<T, Rhs> ClosedSubAssignRef<Rhs> for T where T: for<'a> SubAssign<&'a Rhs> {}
impl<T, Rhs> ClosedMulAssign<Rhs> for T where T: MulAssign<Rhs> {}
impl<T, Rhs> ClosedMulAssignRef<Rhs> for T where T: for<'a> MulAssign<&'a Rhs> {}
impl<T, Rhs> ClosedDivAssign<Rhs> for T where T: DivAssign<Rhs> {}
impl<T, Rhs> ClosedDivAssignRef<Rhs> for T where T: for<'a> DivAssign<&'a Rhs> {}
impl<T, Rhs> ClosedRemAssign<Rhs> for T where T: RemAssign<Rhs> {}
impl<T, Rhs> ClosedRemAssignRef<Rhs> for T where T: for<'a> RemAssign<&'a Rhs> {}

impl<T, Rhs> ClosedBitAnd<Rhs> for T where T: BitAnd<Rhs, Output = T> {}
impl<T, Rhs> ClosedBitAndRef<Rhs> for T where T: for<'a> BitAnd<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedBitOr<Rhs> for T where T: BitOr<Rhs, Output = T> {}
impl<T, Rhs> ClosedBitOrRef<Rhs> for T where T: for<'a> BitOr<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedBitXor<Rhs> for T where T: BitXor<Rhs, Output = T> {}
impl<T, Rhs> ClosedBitXorRef<Rhs> for T where T: for<'a> BitXor<&'a Rhs, Output = T> {}
impl<T> ClosedNot for T where T: Not<Output = T> {}
impl<T, Rhs> ClosedShl<Rhs> for T where T: Shl<Rhs, Output = T> {}
impl<T, Rhs> ClosedShlRef<Rhs> for T where T: for<'a> Shl<&'a Rhs, Output = T> {}
impl<T, Rhs> ClosedShr<Rhs> for T where T: Shr<Rhs, Output = T> {}
impl<T, Rhs> ClosedShrRef<Rhs> for T where T: for<'a> Shr<&'a Rhs, Output = T> {}

impl<T, Rhs> ClosedBitAndAssign<Rhs> for T where T: BitAndAssign<Rhs> {}
impl<T, Rhs> ClosedBitAndAssignRef<Rhs> for T where T: for<'a> BitAndAssign<&'a Rhs> {}
impl<T, Rhs> ClosedBitOrAssign<Rhs> for T where T: BitOrAssign<Rhs> {}
impl<T, Rhs> ClosedBitOrAssignRef<Rhs> for T where T: for<'a> BitOrAssign<&'a Rhs> {}
impl<T, Rhs> ClosedBitXorAssign<Rhs> for T where T: BitXorAssign<Rhs> {}
impl<T, Rhs> ClosedBitXorAssignRef<Rhs> for T where T: for<'a> BitXorAssign<&'a Rhs> {}
impl<T, Rhs> ClosedShlAssign<Rhs> for T where T: ShlAssign<Rhs> {}
impl<T, Rhs> ClosedShlAssignRef<Rhs> for T where T: for<'a> ShlAssign<&'a Rhs> {}
impl<T, Rhs> ClosedShrAssign<Rhs> for T where T: ShrAssign<Rhs> {}
impl<T, Rhs> ClosedShrAssignRef<Rhs> for T where T: for<'a> ShrAssign<&'a Rhs> {}

impl<T: Zero> ClosedZero for T {}
impl<T: One> ClosedOne for T {}

impl<T: Ord> ClosedMin for T {
    fn min(self, other: Self) -> Self {
        std::cmp::min(self, other)
    }
}

impl<T: Ord> ClosedMax for T {
    fn max(self, other: Self) -> Self {
        std::cmp::max(self, other)
    }
}

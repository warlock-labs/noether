//! Implementations of algebraic marker traits for Rust's primitive numeric types.
//!
//! This module provides implementations of the algebraic marker traits for Rust's
//! built-in primitive numeric types, which allows them to satisfy the requirements
//! for the blanket implementations of higher-level algebraic structures.
//!
//! # Implementation Notes
//!
//! - Integer types (i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize) implement traits
//!   corresponding to rings, but not fields (as they don't have multiplicative inverses for all elements).
//!
//! - Floating-point types (f32, f64) approximate fields due to finite precision, potential NaN and Infinity values,
//!   and other IEEE 754 arithmetic behavior.
//!
//! - None of Rust's primitive types are true finite fields mathematically, as true finite fields
//!   have a finite number of elements and follow specific algebraic constraints.

use crate::operations::{
    AssociativeAddition, AssociativeMultiplication, CommutativeAddition, CommutativeMultiplication,
    Distributive,
};

/// Implement marker traits for algebraic properties of primitive numeric types.
/// These properties include commutative and associative addition, associative and commutative multiplication,
/// and distributivity of multiplication over addition.
macro_rules! impl_algebraic_markers_for_primitive {
    ($t:ty) => {
        impl CommutativeAddition for $t {}
        impl AssociativeAddition for $t {}
        impl AssociativeMultiplication for $t {}
        impl CommutativeMultiplication for $t {}
        impl Distributive for $t {}
    };
}

// Apply all marker trait implementations for all primitive numeric types
impl_algebraic_markers_for_primitive!(i8);
impl_algebraic_markers_for_primitive!(i16);
impl_algebraic_markers_for_primitive!(i32);
impl_algebraic_markers_for_primitive!(i64);
impl_algebraic_markers_for_primitive!(i128);
impl_algebraic_markers_for_primitive!(isize);
impl_algebraic_markers_for_primitive!(u8);
impl_algebraic_markers_for_primitive!(u16);
impl_algebraic_markers_for_primitive!(u32);
impl_algebraic_markers_for_primitive!(u64);
impl_algebraic_markers_for_primitive!(u128);
impl_algebraic_markers_for_primitive!(usize);
impl_algebraic_markers_for_primitive!(f32);
impl_algebraic_markers_for_primitive!(f64);

#[cfg(test)]
mod tests {
    use crate::fields::{EuclideanDomain, Field};
    use crate::groups::{
        AdditiveAbelianGroup, AdditiveGroup, AdditiveMagma, AdditiveMonoid, AdditiveSemigroup,
    };
    use crate::groups::{
        MultiplicativeAbelianGroup, MultiplicativeGroup, MultiplicativeMagma, MultiplicativeMonoid,
        MultiplicativeSemigroup,
    };
    use crate::rings::{
        CommutativeRing, IntegralDomain, PrincipalIdealDomain, Ring, UniqueFactorizationDomain,
    };

    // Helper function to verify that a type satisfies the requirements for a given trait
    // This doesn't test functionality, just trait bounds
    fn assert_additive_magma<T: AdditiveMagma>() {}
    fn assert_additive_semigroup<T: AdditiveSemigroup>() {}
    fn assert_additive_monoid<T: AdditiveMonoid>() {}
    fn assert_additive_group<T: AdditiveGroup>() {}
    fn assert_additive_abelian_group<T: AdditiveAbelianGroup>() {}

    fn assert_multiplicative_magma<T: MultiplicativeMagma>() {}
    fn assert_multiplicative_semigroup<T: MultiplicativeSemigroup>() {}
    fn assert_multiplicative_monoid<T: MultiplicativeMonoid>() {}
    fn assert_multiplicative_group<T: MultiplicativeGroup>() {}
    fn assert_multiplicative_abelian_group<T: MultiplicativeAbelianGroup>() {}

    fn assert_ring<T: Ring>() {}
    fn assert_commutative_ring<T: CommutativeRing>() {}
    fn assert_integral_domain<T: IntegralDomain>() {}
    fn assert_ufd<T: UniqueFactorizationDomain>() {}
    fn assert_pid<T: PrincipalIdealDomain>() {}
    fn assert_euclidean_domain<T: EuclideanDomain>() {}
    fn assert_field<T: Field>() {}

    // Test all integer types
    #[test]
    fn test_signed_integers() {
        // i8
        assert_additive_magma::<i8>();
        assert_additive_semigroup::<i8>();
        assert_additive_monoid::<i8>();
        assert_additive_group::<i8>();
        assert_additive_abelian_group::<i8>();
        assert_multiplicative_magma::<i8>();
        assert_multiplicative_semigroup::<i8>();
        assert_multiplicative_monoid::<i8>();
        assert_ring::<i8>();
        assert_commutative_ring::<i8>();
        assert_integral_domain::<i8>();
        assert_ufd::<i8>();
        assert_pid::<i8>();
        assert_euclidean_domain::<i8>();
        // Note: Integers are not fields since they lack multiplicative inverses

        // i16
        assert_additive_abelian_group::<i16>();
        assert_multiplicative_monoid::<i16>();
        assert_ring::<i16>();
        assert_commutative_ring::<i16>();
        assert_integral_domain::<i16>();
        assert_ufd::<i16>();
        assert_pid::<i16>();
        assert_euclidean_domain::<i16>();

        // i32
        assert_additive_abelian_group::<i32>();
        assert_multiplicative_monoid::<i32>();
        assert_ring::<i32>();
        assert_commutative_ring::<i32>();
        assert_integral_domain::<i32>();
        assert_ufd::<i32>();
        assert_pid::<i32>();
        assert_euclidean_domain::<i32>();

        // i64
        assert_additive_abelian_group::<i64>();
        assert_multiplicative_monoid::<i64>();
        assert_ring::<i64>();
        assert_commutative_ring::<i64>();
        assert_integral_domain::<i64>();
        assert_ufd::<i64>();
        assert_pid::<i64>();
        assert_euclidean_domain::<i64>();

        // i128
        assert_additive_abelian_group::<i128>();
        assert_multiplicative_monoid::<i128>();
        assert_ring::<i128>();
        assert_commutative_ring::<i128>();
        assert_integral_domain::<i128>();
        assert_ufd::<i128>();
        assert_pid::<i128>();
        assert_euclidean_domain::<i128>();

        // isize
        assert_additive_abelian_group::<isize>();
        assert_multiplicative_monoid::<isize>();
        assert_ring::<isize>();
        assert_commutative_ring::<isize>();
        assert_integral_domain::<isize>();
        assert_ufd::<isize>();
        assert_pid::<isize>();
        assert_euclidean_domain::<isize>();
    }

    #[test]
    fn test_unsigned_integers() {
        // u8
        assert_additive_magma::<u8>();
        assert_additive_semigroup::<u8>();
        assert_additive_monoid::<u8>();
        assert_multiplicative_magma::<u8>();
        assert_multiplicative_semigroup::<u8>();
        assert_multiplicative_monoid::<u8>();
        // Note: u8 is not an additive group (no negation)

        // u16, u32, u64, u128, usize
        assert_additive_monoid::<u16>();
        assert_multiplicative_monoid::<u16>();

        assert_additive_monoid::<u32>();
        assert_multiplicative_monoid::<u32>();

        assert_additive_monoid::<u64>();
        assert_multiplicative_monoid::<u64>();

        assert_additive_monoid::<u128>();
        assert_multiplicative_monoid::<u128>();

        assert_additive_monoid::<usize>();
        assert_multiplicative_monoid::<usize>();
    }

    #[test]
    fn test_floating_point() {
        // f32
        assert_additive_magma::<f32>();
        assert_additive_semigroup::<f32>();
        assert_additive_monoid::<f32>();
        assert_additive_group::<f32>();
        assert_additive_abelian_group::<f32>();
        assert_multiplicative_magma::<f32>();
        assert_multiplicative_semigroup::<f32>();
        assert_multiplicative_monoid::<f32>();
        assert_multiplicative_group::<f32>();
        assert_multiplicative_abelian_group::<f32>();
        assert_ring::<f32>();
        assert_commutative_ring::<f32>();
        assert_integral_domain::<f32>();
        assert_ufd::<f32>();
        assert_pid::<f32>();
        assert_euclidean_domain::<f32>();
        assert_field::<f32>();

        // f64
        assert_additive_magma::<f64>();
        assert_additive_semigroup::<f64>();
        assert_additive_monoid::<f64>();
        assert_additive_group::<f64>();
        assert_additive_abelian_group::<f64>();
        assert_multiplicative_magma::<f64>();
        assert_multiplicative_semigroup::<f64>();
        assert_multiplicative_monoid::<f64>();
        assert_multiplicative_group::<f64>();
        assert_multiplicative_abelian_group::<f64>();
        assert_ring::<f64>();
        assert_commutative_ring::<f64>();
        assert_integral_domain::<f64>();
        assert_ufd::<f64>();
        assert_pid::<f64>();
        assert_euclidean_domain::<f64>();
        assert_field::<f64>();
    }

    #[test]
    fn test_basic_operations() {
        // Test that basic operations work as expected
        let a: i32 = 5;
        let b: i32 = 3;

        assert_eq!(a + b, 8);
        assert_eq!(a - b, 2);
        assert_eq!(a * b, 15);
        assert_eq!(a / b, 1); // Integer division

        let c: f64 = 5.0;
        let d: f64 = 2.0;

        assert_eq!(c + d, 7.0);
        assert_eq!(c - d, 3.0);
        assert_eq!(c * d, 10.0);
        assert_eq!(c / d, 2.5);
    }
}

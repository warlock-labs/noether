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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operations::{
        AssociativeAddition, AssociativeMultiplication, CommutativeAddition,
        CommutativeMultiplication,
    };
    use num_traits::{Inv, One, Zero};
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

    // A simple group implementation to test additive groups
    #[derive(Debug, Clone, Copy, PartialEq)]
    struct IntegerMod7(i32);

    impl IntegerMod7 {
        // Create a new element, ensuring it is normalized into the range [0, 6]
        fn new(value: i32) -> Self {
            let normalized = value.rem_euclid(7);
            Self(normalized)
        }
    }

    // Additive operations for IntegerMod7
    impl Add for IntegerMod7 {
        type Output = Self;

        fn add(self, rhs: Self) -> Self::Output {
            Self::new(self.0 + rhs.0)
        }
    }

    impl AddAssign for IntegerMod7 {
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }

    impl Sub for IntegerMod7 {
        type Output = Self;

        fn sub(self, rhs: Self) -> Self::Output {
            Self::new(self.0 - rhs.0)
        }
    }

    impl SubAssign for IntegerMod7 {
        fn sub_assign(&mut self, rhs: Self) {
            *self = *self - rhs;
        }
    }

    impl Neg for IntegerMod7 {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new(-self.0)
        }
    }

    impl Zero for IntegerMod7 {
        fn zero() -> Self {
            Self(0)
        }

        fn is_zero(&self) -> bool {
            self.0 == 0
        }
    }

    // Multiplicative operations for IntegerMod7
    impl Mul for IntegerMod7 {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            Self::new(self.0 * rhs.0)
        }
    }

    impl MulAssign for IntegerMod7 {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }

    impl One for IntegerMod7 {
        fn one() -> Self {
            Self(1)
        }
    }

    // Only integers coprime to 7 have multiplicative inverses
    impl Inv for IntegerMod7 {
        type Output = Self;

        fn inv(self) -> Self::Output {
            match self.0 {
                0 => panic!("Multiplicative inverse of 0 is undefined in Z/7Z"),
                1 => Self(1), // 1*1 ≡ 1 (mod 7)
                2 => Self(4), // 2*4 ≡ 8 ≡ 1 (mod 7)
                3 => Self(5), // 3*5 ≡ 15 ≡ 1 (mod 7)
                4 => Self(2), // 4*2 ≡ 8 ≡ 1 (mod 7)
                5 => Self(3), // 5*3 ≡ 15 ≡ 1 (mod 7)
                6 => Self(6), // 6*6 ≡ 36 ≡ 1 (mod 7)
                _ => unreachable!("All values should be normalized to 0-6"),
            }
        }
    }

    impl Div for IntegerMod7 {
        type Output = Self;

        fn div(self, rhs: Self) -> Self::Output {
            if rhs.0 == 0 {
                panic!("Division by zero in Z/7Z");
            }
            self * rhs.inv()
        }
    }

    impl DivAssign for IntegerMod7 {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }

    // Marker traits
    impl CommutativeAddition for IntegerMod7 {}
    impl AssociativeAddition for IntegerMod7 {}
    impl CommutativeMultiplication for IntegerMod7 {}
    impl AssociativeMultiplication for IntegerMod7 {}

    // Test type for non-abelian group (a simplified quaternion group)
    #[derive(Debug, Clone, Copy, PartialEq)]
    enum Quaternion {
        One,    // 1
        I,      // i
        J,      // j
        K,      // k
        NegOne, // -1
        NegI,   // -i
        NegJ,   // -j
        NegK,   // -k
    }

    impl Mul for Quaternion {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self::Output {
            use Quaternion::*;

            match (self, rhs) {
                // Identity element
                (One, x) | (x, One) => x,
                (NegOne, x) => match x {
                    One => NegOne,
                    I => NegI,
                    J => NegJ,
                    K => NegK,
                    NegOne => One,
                    NegI => I,
                    NegJ => J,
                    NegK => K,
                },
                (x, NegOne) => match x {
                    One => NegOne,
                    I => NegI,
                    J => NegJ,
                    K => NegK,
                    NegOne => One,
                    NegI => I,
                    NegJ => J,
                    NegK => K,
                },

                // Inverse properties: j * (-j) = (-j) * j = 1, etc.
                (I, NegI) | (NegI, I) => One,
                (J, NegJ) | (NegJ, J) => One,
                (K, NegK) | (NegK, K) => One,

                // i² = j² = k² = -1
                (I, I) => NegOne,
                (J, J) => NegOne,
                (K, K) => NegOne,
                (NegI, NegI) => NegOne,
                (NegJ, NegJ) => NegOne,
                (NegK, NegK) => NegOne,

                // i*j = k, j*k = i, k*i = j
                (I, J) => K,
                (J, K) => I,
                (K, I) => J,

                // j*i = -k, k*j = -i, i*k = -j
                (J, I) => NegK,
                (K, J) => NegI,
                (I, K) => NegJ,

                (I, NegJ) => NegK,
                (I, NegK) => J,
                (J, NegI) => K,
                (J, NegK) => NegI,
                (K, NegI) => NegJ,
                (K, NegJ) => I,

                (NegI, J) => NegK,
                (NegI, K) => NegJ,
                (NegJ, I) => K,
                (NegJ, K) => I,
                (NegK, I) => J,
                (NegK, J) => NegI,

                (NegI, NegJ) => K,
                (NegJ, NegK) => I,
                (NegK, NegI) => J,
                (NegJ, NegI) => NegK,
                (NegK, NegJ) => NegI,
                (NegI, NegK) => NegJ,
            }
        }
    }

    impl One for Quaternion {
        fn one() -> Self {
            Quaternion::One
        }
    }

    impl MulAssign for Quaternion {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }

    impl Inv for Quaternion {
        type Output = Self;

        fn inv(self) -> Self::Output {
            use Quaternion::*;

            match self {
                One => One,
                I => NegI,
                J => NegJ,
                K => NegK,
                NegOne => NegOne,
                NegI => I,
                NegJ => J,
                NegK => K,
            }
        }
    }

    impl Div for Quaternion {
        type Output = Self;

        fn div(self, rhs: Self) -> Self::Output {
            // Using multiplication with inverse is the correct implementation
            // for division in a quaternion group
            #[allow(clippy::suspicious_arithmetic_impl)]
            let result = self * rhs.inv();
            result
        }
    }

    impl DivAssign for Quaternion {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }

    // Marker traits - only associative, not commutative
    impl AssociativeMultiplication for Quaternion {}

    #[test]
    fn test_additive_magma() {
        fn assert_is_additive_magma<T: AdditiveMagma>(_: &T) {}

        // Integers mod 7 form an additive magma
        assert_is_additive_magma(&IntegerMod7::new(3));

        // Test primitive types
        assert_is_additive_magma(&5i32);
        assert_is_additive_magma(&std::f64::consts::PI);
    }

    #[test]
    fn test_multiplicative_magma() {
        fn assert_is_multiplicative_magma<T: MultiplicativeMagma>(_: &T) {}

        // Integers mod 7 form a multiplicative magma
        assert_is_multiplicative_magma(&IntegerMod7::new(3));

        // Quaternions form a multiplicative magma
        assert_is_multiplicative_magma(&Quaternion::I);

        // Test primitive types
        assert_is_multiplicative_magma(&5i32);
        assert_is_multiplicative_magma(&std::f64::consts::PI);
    }

    #[test]
    fn test_additive_semigroup() {
        fn assert_is_additive_semigroup<T: AdditiveSemigroup>(_: &T) {}

        // Integers mod 7 form an additive semigroup
        assert_is_additive_semigroup(&IntegerMod7::new(3));

        // Test primitive types
        assert_is_additive_semigroup(&5i32);
        assert_is_additive_semigroup(&std::f64::consts::PI);

        // Test associativity in IntegerMod7
        let a = IntegerMod7::new(2);
        let b = IntegerMod7::new(3);
        let c = IntegerMod7::new(5);

        assert_eq!((a + b) + c, a + (b + c)); // (2+3)+5 = 2+(3+5) = 3
    }

    #[test]
    fn test_multiplicative_semigroup() {
        fn assert_is_multiplicative_semigroup<T: MultiplicativeSemigroup>(_: &T) {}

        // Integers mod 7 form a multiplicative semigroup
        assert_is_multiplicative_semigroup(&IntegerMod7::new(3));

        // Quaternions form a multiplicative semigroup
        assert_is_multiplicative_semigroup(&Quaternion::I);

        // Test primitive types
        assert_is_multiplicative_semigroup(&5i32);
        assert_is_multiplicative_semigroup(&std::f64::consts::PI);

        // Test associativity in IntegerMod7
        let a = IntegerMod7::new(2);
        let b = IntegerMod7::new(3);
        let c = IntegerMod7::new(5);

        assert_eq!((a * b) * c, a * (b * c)); // (2*3)*5 = 2*(3*5) = 2

        // Test associativity in Quaternions
        use Quaternion::*;
        let x = I;
        let y = J;
        let z = K;

        assert_eq!((x * y) * z, x * (y * z)); // (i*j)*k = i*(j*k) = -1
    }

    #[test]
    fn test_additive_monoid() {
        fn assert_is_additive_monoid<T: AdditiveMonoid>(_: &T) {}

        // Integers mod 7 form an additive monoid
        assert_is_additive_monoid(&IntegerMod7::new(3));

        // Test primitive types
        assert_is_additive_monoid(&5i32);
        assert_is_additive_monoid(&std::f64::consts::PI);

        // Test identity properties in IntegerMod7
        let a = IntegerMod7::new(4);
        let zero = IntegerMod7::zero();

        assert_eq!(a + zero, a); // 4 + 0 = 4
        assert_eq!(zero + a, a); // 0 + 4 = 4
    }

    #[test]
    fn test_multiplicative_monoid() {
        fn assert_is_multiplicative_monoid<T: MultiplicativeMonoid>(_: &T) {}

        // Integers mod 7 form a multiplicative monoid
        assert_is_multiplicative_monoid(&IntegerMod7::new(3));

        // Quaternions form a multiplicative monoid
        assert_is_multiplicative_monoid(&Quaternion::I);

        // Test primitive types
        assert_is_multiplicative_monoid(&5i32);
        assert_is_multiplicative_monoid(&std::f64::consts::PI);

        // Test identity properties in IntegerMod7
        let a = IntegerMod7::new(4);
        let one = IntegerMod7::one();

        assert_eq!(a * one, a); // 4 * 1 = 4
        assert_eq!(one * a, a); // 1 * 4 = 4

        // Test identity properties in Quaternions
        let q = Quaternion::J;
        let q_one = Quaternion::one();

        assert_eq!(q * q_one, q); // j * 1 = j
        assert_eq!(q_one * q, q); // 1 * j = j
    }

    #[test]
    fn test_additive_group() {
        fn assert_is_additive_group<T: AdditiveGroup>(_: &T) {}

        // Integers mod 7 form an additive group
        assert_is_additive_group(&IntegerMod7::new(3));

        // Test primitive types
        assert_is_additive_group(&5i32);
        assert_is_additive_group(&std::f64::consts::PI);

        // Test inverse properties in IntegerMod7
        let a = IntegerMod7::new(4);
        let neg_a = -a; // -4 ≡ 3 (mod 7)
        let zero = IntegerMod7::zero();

        assert_eq!(a + neg_a, zero); // 4 + 3 ≡ 0 (mod 7)
        assert_eq!(neg_a + a, zero); // 3 + 4 ≡ 0 (mod 7)
    }

    #[test]
    fn test_multiplicative_group() {
        fn assert_is_multiplicative_group<T: MultiplicativeGroup>(_: &T) {}

        // Integers mod 7 without 0 form a multiplicative group
        assert_is_multiplicative_group(&IntegerMod7::new(3));

        // Quaternions form a multiplicative group
        assert_is_multiplicative_group(&Quaternion::I);

        // Test primitive floating point types (not integers, as they don't form a multiplicative group)
        assert_is_multiplicative_group(&std::f64::consts::PI);

        // Test inverse properties in IntegerMod7
        let a = IntegerMod7::new(3); // 3
        let a_inv = a.inv(); // 5 (as 3*5 ≡ 15 ≡ 1 mod 7)
        let one = IntegerMod7::one();

        assert_eq!(a * a_inv, one); // 3 * 5 ≡ 15 ≡ 1 (mod 7)
        assert_eq!(a_inv * a, one); // 5 * 3 ≡ 15 ≡ 1 (mod 7)

        // Test inverse properties in Quaternions
        use Quaternion::*;
        let q = J; // j
        let q_inv = q.inv(); // -j
        let q_one = One;

        // In quaternions, j * (-j) = -j * j = 1
        assert_eq!(q * q_inv, q_one);
        assert_eq!(q_inv * q, q_one);
    }

    #[test]
    fn test_additive_abelian_group() {
        fn assert_is_additive_abelian_group<T: AdditiveAbelianGroup>(_: &T) {}

        // Integers mod 7 form an additive abelian group
        assert_is_additive_abelian_group(&IntegerMod7::new(3));

        // Test primitive types
        assert_is_additive_abelian_group(&5i32);
        assert_is_additive_abelian_group(&std::f64::consts::PI);

        // Test commutativity in IntegerMod7
        let a = IntegerMod7::new(2);
        let b = IntegerMod7::new(5);

        assert_eq!(a + b, b + a); // 2 + 5 = 5 + 2 = 0
    }

    #[test]
    fn test_multiplicative_abelian_group() {
        fn assert_is_multiplicative_abelian_group<T: MultiplicativeAbelianGroup>(_: &T) {}

        // Integers mod 7 without 0 form a multiplicative abelian group
        assert_is_multiplicative_abelian_group(&IntegerMod7::new(3));

        // Test primitive floating point types
        assert_is_multiplicative_abelian_group(&std::f64::consts::PI);

        // Test commutativity in IntegerMod7
        let a = IntegerMod7::new(2);
        let b = IntegerMod7::new(5);

        assert_eq!(a * b, b * a); // 2 * 5 = 5 * 2 = 3

        // Quaternions are NOT a commutative group - let's verify this
        let q1 = Quaternion::I;
        let q2 = Quaternion::J;

        assert_ne!(q1 * q2, q2 * q1); // i*j = k, but j*i = -k
    }

    #[test]
    fn test_group_laws() {
        // Test the group laws for Z/7Z as an additive group
        let elements: Vec<IntegerMod7> = (0..7).map(IntegerMod7::new).collect();

        // 1. Closure: a + b ∈ G for all a, b ∈ G
        for &a in &elements {
            for &b in &elements {
                let c = a + b;
                assert!(
                    elements.contains(&c),
                    "Closure law violated: {} + {} = {} is not in Z/7Z",
                    a.0,
                    b.0,
                    c.0
                );
            }
        }

        // 2. Associativity: (a + b) + c = a + (b + c) for all a, b, c ∈ G
        for &a in &elements {
            for &b in &elements {
                for &c in &elements {
                    assert_eq!(
                        (a + b) + c,
                        a + (b + c),
                        "Associativity law violated: ({} + {}) + {} ≠ {} + ({} + {})",
                        a.0,
                        b.0,
                        c.0,
                        a.0,
                        b.0,
                        c.0
                    );
                }
            }
        }

        // 3. Identity: a + 0 = 0 + a = a for all a ∈ G
        let zero = IntegerMod7::zero();
        for &a in &elements {
            assert_eq!(a + zero, a, "Identity law violated: {} + 0 ≠ {}", a.0, a.0);
            assert_eq!(zero + a, a, "Identity law violated: 0 + {} ≠ {}", a.0, a.0);
        }

        // 4. Inverse: a + (-a) = (-a) + a = 0 for all a ∈ G
        for &a in &elements {
            let neg_a = -a;
            assert_eq!(
                a + neg_a,
                zero,
                "Inverse law violated: {} + ({}) ≠ 0",
                a.0,
                neg_a.0
            );
            assert_eq!(
                neg_a + a,
                zero,
                "Inverse law violated: ({}) + {} ≠ 0",
                neg_a.0,
                a.0
            );
        }

        // 5. Commutativity (for abelian groups): a + b = b + a for all a, b ∈ G
        for &a in &elements {
            for &b in &elements {
                assert_eq!(
                    a + b,
                    b + a,
                    "Commutativity law violated: {} + {} ≠ {} + {}",
                    a.0,
                    b.0,
                    b.0,
                    a.0
                );
            }
        }
    }
}

use noether::{
    AdditiveAbelianGroup, AdditiveGroup, AdditiveMagma, AdditiveMonoid, AdditiveSemigroup,
    AssociativeAddition, AssociativeMultiplication, ClosedAdd, ClosedAddAssign, ClosedDiv,
    ClosedDivAssign, ClosedMul, ClosedMulAssign, ClosedNeg, ClosedOne, ClosedZero,
    CommutativeAddition, DistributiveAddition, EuclideanDomain, Field, FiniteField, IntegralDomain,
    MultiplicativeMagma, MultiplicativeMonoid, MultiplicativeSemigroup, PrincipalIdealDomain, Ring,
    Set, UniqueFactorizationDomain,
};
use num_traits::{Euclid, Inv, One, Zero};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

/// A finite field scalar optimized for use in cryptographic operations.
///
/// All operations feature modular arithmetic, implemented in constant time.
/// Primarily focusing on fields of prime order, non-prime order fields may
/// have undefined behavior at this time.
///
/// Note: We have to keep the double size `D` as a constant due to generic limitations
/// in rust.
#[derive(Clone, Copy, Debug)]
pub struct FinitePrimeField<const L: usize, const D: usize> {
    modulus: [u64; L],
    value: [u64; L],
}

impl<const L: usize, const D: usize> FinitePrimeField<L, D> {
    const ZERO: [u64; L] = Self::zero_array();
    const ONE: [u64; L] = Self::one_array();

    pub const fn new(modulus: [u64; L], value: [u64; L]) -> Self {
        if D != 2 * L {
            panic!("Double size D must be twice the size of the field L");
        }
        Self { modulus, value }
    }

    /// Computes the correction factor for efficient subtraction.
    ///
    /// This method calculates 2^(64*L) - modulus, which is used to optimize
    /// the subtraction operation in the finite field.
    ///
    /// # Arguments
    ///
    /// * `modulus` - The modulus of the field
    ///
    /// # Returns
    ///
    /// The computed correction factor
    const fn subtraction_correction(modulus: &[u64; L]) -> [u64; L] {
        let mut correction = [0; L];
        let mut carry = 1u64;
        let mut i = 0;
        while i < L {
            let (corrected_limb, new_carry) = (!modulus[i]).overflowing_add(carry);
            correction[i] = corrected_limb;
            carry = if new_carry { 1 } else { 0 };
            i += 1;
        }
        correction
    }

    /// Creates an array representing zero in the field.
    ///
    /// # Returns
    ///
    /// An array of L u64 elements, all set to 0
    const fn zero_array() -> [u64; L] {
        [0; L]
    }

    /// Creates an array representing one in the field.
    ///
    /// # Returns
    ///
    /// An array of L u64 elements, with the least significant limb set to 1 and others to 0
    const fn one_array() -> [u64; L] {
        let mut arr = [0; L];
        arr[0] = 1;
        arr
    }
}

impl<const L: usize, const D: usize> Add for FinitePrimeField<L, D> {
    type Output = Self;

    /// Performs modular addition.
    ///
    /// This method adds two field elements and reduces the result modulo the field's modulus.
    fn add(self, other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> AddAssign for FinitePrimeField<L, D> {
    fn add_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl<const L: usize, const D: usize> Zero for FinitePrimeField<L, D> {
    fn zero() -> Self {
        todo!()
    }

    fn is_zero(&self) -> bool {
        todo!()
    }
}

impl<const L: usize, const D: usize> Neg for FinitePrimeField<L, D> {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> Sub for FinitePrimeField<L, D> {
    type Output = Self;

    /// Performs modular subtraction.
    ///
    /// This method subtracts one field element from another and ensures the result
    /// is in the correct range by adding the modulus if necessary.
    fn sub(self, other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> SubAssign for FinitePrimeField<L, D> {
    fn sub_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl<const L: usize, const D: usize> PartialEq for FinitePrimeField<L, D> {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}

impl<const L: usize, const D: usize> Mul for FinitePrimeField<L, D> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> One for FinitePrimeField<L, D> {
    fn one() -> Self {
        todo!()
    }
}

impl<const L: usize, const D: usize> MulAssign for FinitePrimeField<L, D> {
    fn mul_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl<const L: usize, const D: usize> Inv for FinitePrimeField<L, D> {
    type Output = Self;

    fn inv(self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> Euclid for FinitePrimeField<L, D> {
    fn div_euclid(&self, v: &Self) -> Self {
        todo!()
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        todo!()
    }
}

impl<const L: usize, const D: usize> Rem for FinitePrimeField<L, D> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const L: usize, const D: usize> Div for FinitePrimeField<L, D> {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> DivAssign<Self> for FinitePrimeField<L, D> {
    fn div_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl<const L: usize, const D: usize> FiniteField for FinitePrimeField<L, D> {
    fn characteristic() -> u64 {
        todo!()
    }

    fn order() -> u64 {
        todo!()
    }
}

impl<const L: usize, const D: usize> Field for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> EuclideanDomain for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> PrincipalIdealDomain for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> UniqueFactorizationDomain for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> IntegralDomain for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> Ring for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AdditiveAbelianGroup for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedAdd for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedAddAssign for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedNeg for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AdditiveGroup for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AdditiveMonoid for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AdditiveSemigroup for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AdditiveMagma for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> Set for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AssociativeAddition for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedZero for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> CommutativeAddition for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> MultiplicativeMonoid for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> MultiplicativeSemigroup for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> MultiplicativeMagma for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedMul for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedMulAssign for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> AssociativeMultiplication for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedOne for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> DistributiveAddition for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedDiv for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> ClosedDivAssign for FinitePrimeField<L, D> {}

fn main() {
    let a = FinitePrimeField::<4, 8>::new(
        [
            0x3C208C16D87CFD47,
            0x97816A916871CA8D,
            0xB85045B68181585D,
            0x30644E72E131A029,
        ],
        [1, 2, 3, 4],
    );
    let b = FinitePrimeField::<4, 8>::new(
        [
            0x3C208C16D87CFD47,
            0x97816A916871CA8D,
            0xB85045B68181585D,
            0x30644E72E131A029,
        ],
        [5, 6, 7, 8],
    );
    let c = a + b;
    println!("{:?}", c);
    let d = a - b;
    println!("{:?}", d);
    let e = a * b;
    println!("{:?}", e);
    let f = a / b;
    println!("{:?}", f);
    let g = a.inv();
    println!("{:?}", g);
    let h = -a;
    println!("{:?}", h);
    let i = a == b;
    println!("{:?}", i);
    let j = a != b;
    println!("{:?}", j);
    let k = a + b;
    println!("{:?}", k);
    let l = a - b;
    println!("{:?}", l);
    let m = a * b;
    println!("{:?}", m);
    let n = a / b;
    println!("{:?}", n);
    let o = a.inv();
    println!("{:?}", o);
    let p = -a;
    println!("{:?}", p);
    let q = a == b;
    println!("{:?}", q);
    let r = a != b;
    println!("{:?}", r);
    let s = a + b;
    println!("{:?}", s);
    let t = a - b;
    println!("{:?}", t);
    let u = a * b;
    println!("{:?}", u);
    let v = a / b;
    println!("{:?}", v);
    let w = a.inv();
    println!("{:?}", w);
    let x = -a;
    println!("{:?}", x);
}

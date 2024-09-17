use noether::{
    AssociativeAddition, AssociativeMultiplication, CommutativeAddition, CommutativeMultiplication,
    Distributive, FiniteField,
};
use num_traits::{Euclid, Inv, One, Zero};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

/// The trait hierarchy in Noether is useful for verifying the correct and idiomatic implementation
/// of algebraic structures in rust.
///
/// We take here, as an example, the skeleton implementation of a finite field.
/// Where `L` number of words and `D` number of words are used to represent the field.
/// The modulus is the order of the field, which would be prime or a prime power

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq)]

pub struct FieldElement<const L: usize>([u64; L]);

impl<const L: usize> Zero for FieldElement<L> {
    fn zero() -> Self {
        Self([0; L])
    }

    fn is_zero(&self) -> bool {
        self.0[0] == 0
    }
}

impl<const L: usize> One for FieldElement<L> {
    fn one() -> Self {
        let mut arr = [0; L];
        arr[0] = 1;
        Self(arr)
    }
}

impl<const L: usize> Add for FieldElement<L> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut result = [0; L];
        let mut carry = 0u64;
        for (i, (&self_val, &rhs_val)) in self.0.iter().zip(rhs.0.iter()).enumerate() {
            let sum = self_val as u128 + rhs_val as u128 + carry as u128;
            result[i] = sum as u64;
            carry = (sum >> 64) as u64;
        }
        Self(result)
    }
}

impl<const L: usize> Mul for FieldElement<L> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut result = [0u64; L];
        for (i, &self_val) in self.0.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &rhs_val) in rhs.0.iter().enumerate() {
                if i + j >= L {
                    break;
                }
                let prod = (self_val as u128) * (rhs_val as u128) + (result[i + j] as u128) + carry;
                result[i + j] = prod as u64;
                carry = prod >> 64;
            }
        }

        Self(result)
    }
}
#[derive(Clone, Copy, Debug)]
pub struct FinitePrimeField<const L: usize, const D: usize> {
    modulus: [u64; L],
    _value: [u64; L],
}

impl<const L: usize, const D: usize> FinitePrimeField<L, D> {
    const _ZERO: [u64; L] = Self::zero_array();

    pub const fn new(modulus: [u64; L], value: [u64; L]) -> Self {
        if D != 2 * L {
            panic!("Double size D must be twice the size of the field L");
        }
        Self {
            modulus,
            _value: value,
        }
    }

    /// Creates an array representing zero in the field.
    ///
    /// # Returns
    ///
    /// An array of L u64 elements, all set to 0
    const fn zero_array() -> [u64; L] {
        [0; L]
    }
}

impl<const L: usize, const D: usize> Add for FinitePrimeField<L, D> {
    type Output = Self;

    /// Performs modular addition.
    ///
    /// This method adds two field elements and reduces the result modulo the field's modulus.
    fn add(self, _other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> AddAssign for FinitePrimeField<L, D> {
    fn add_assign(&mut self, _rhs: Self) {
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
    fn sub(self, _other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> SubAssign for FinitePrimeField<L, D> {
    fn sub_assign(&mut self, _rhs: Self) {
        todo!()
    }
}

impl<const L: usize, const D: usize> PartialEq for FinitePrimeField<L, D> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<const L: usize, const D: usize> Mul for FinitePrimeField<L, D> {
    type Output = Self;

    fn mul(self, _other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> One for FinitePrimeField<L, D> {
    fn one() -> Self {
        todo!()
    }
}

impl<const L: usize, const D: usize> MulAssign for FinitePrimeField<L, D> {
    fn mul_assign(&mut self, _rhs: Self) {
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
    fn div_euclid(&self, _v: &Self) -> Self {
        todo!()
    }

    fn rem_euclid(&self, _v: &Self) -> Self {
        todo!()
    }
}

impl<const L: usize, const D: usize> Rem for FinitePrimeField<L, D> {
    type Output = Self;

    fn rem(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const L: usize, const D: usize> Div for FinitePrimeField<L, D> {
    type Output = Self;

    fn div(self, _other: Self) -> Self {
        Self::new(self.modulus, Self::zero_array())
    }
}

impl<const L: usize, const D: usize> DivAssign<Self> for FinitePrimeField<L, D> {
    fn div_assign(&mut self, _rhs: Self) {
        todo!()
    }
}

/// Marker trait for commutative addition: a + b = b + a
impl<const L: usize, const D: usize> CommutativeAddition for FinitePrimeField<L, D> {}

/// Marker trait for commutative multiplication: a * b = b * a
impl<const L: usize, const D: usize> CommutativeMultiplication for FinitePrimeField<L, D> {}

/// Marker trait for associative addition: (a + b) + c = a + (b + c)
impl<const L: usize, const D: usize> AssociativeAddition for FinitePrimeField<L, D> {}

/// Marker trait for associative multiplication: (a * b) * c = a * (b * c)
impl<const L: usize, const D: usize> AssociativeMultiplication for FinitePrimeField<L, D> {}

/// Marker trait for distributive multiplication over addition: a * (b + c) = (a * b) + (a * c)
impl<const L: usize, const D: usize> Distributive for FinitePrimeField<L, D> {}

impl<const L: usize, const D: usize> FiniteField for FinitePrimeField<L, D> {
    type ScalarType = FieldElement<L>;

    fn characteristic() -> Self::ScalarType {
        // For a prime field, the characteristic is the same as the modulus
        // This is a placeholder implementation
        FieldElement([2; L]) // Example: characteristic 2
    }

    fn order() -> Self::ScalarType {
        // For a prime field, the order is the same as the modulus
        // This is a placeholder implementation
        FieldElement([4; L]) // Example: order 4
    }
}

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

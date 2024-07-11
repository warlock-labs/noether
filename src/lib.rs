pub use num_traits::{Inv, One, Zero};
pub use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

// These traits capture the mathematical ideal of closure on standard ops traits.

/// Trait __alias__ for `Add` with result of type `Self`.
pub trait ClosedAdd<Right = Self>: Sized + Add<Right, Output = Self> {}

/// Trait __alias__ for `Sub` with result of type `Self`.
pub trait ClosedSub<Right = Self>: Sized + Sub<Right, Output = Self> {}

/// Trait __alias__ for `Mul` with result of type `Self`.
pub trait ClosedMul<Right = Self>: Sized + Mul<Right, Output = Self> {}

/// Trait __alias__ for `Div` with result of type `Self`.
pub trait ClosedDiv<Right = Self>: Sized + Div<Right, Output = Self> {}

/// Trait __alias__ for `Neg` with result of type `Self`.
pub trait ClosedNeg: Sized + Neg<Output = Self> {}

/// Trait __alias__ for `Add` and `AddAssign` with result of type `Self`.
pub trait ClosedAddAssign<Right = Self>: ClosedAdd<Right> + AddAssign<Right> {}

/// Trait __alias__ for `Sub` and `SubAssign` with result of type `Self`.
pub trait ClosedSubAssign<Right = Self>: ClosedSub<Right> + SubAssign<Right> {}

/// Trait __alias__ for `Mul` and `MulAssign` with result of type `Self`.
pub trait ClosedMulAssign<Right = Self>: ClosedMul<Right> + MulAssign<Right> {}

/// Trait __alias__ for `Div` and `DivAssign` with result of type `Self`.
pub trait ClosedDivAssign<Right = Self>: ClosedDiv<Right> + DivAssign<Right> {}

// These auto implementations exist to make the above traits easier to use.

impl<T, Right> ClosedAdd<Right> for T where T: Add<Right, Output = T> + AddAssign<Right> {}

impl<T, Right> ClosedSub<Right> for T where T: Sub<Right, Output = T> + SubAssign<Right> {}

impl<T, Right> ClosedMul<Right> for T where T: Mul<Right, Output = T> + MulAssign<Right> {}

impl<T, Right> ClosedDiv<Right> for T where T: Div<Right, Output = T> + DivAssign<Right> {}

impl<T> ClosedNeg for T where T: Neg<Output = T> {}

impl<T, Right> ClosedAddAssign<Right> for T where T: ClosedAdd<Right> + AddAssign<Right> {}

impl<T, Right> ClosedSubAssign<Right> for T where T: ClosedSub<Right> + SubAssign<Right> {}

impl<T, Right> ClosedMulAssign<Right> for T where T: ClosedMul<Right> + MulAssign<Right> {}

impl<T, Right> ClosedDivAssign<Right> for T where T: ClosedDiv<Right> + DivAssign<Right> {}

/// Additive binary operator
pub trait AdditiveOperation: ClosedAdd<Output = Self> {}

/// Multiplicative binary operator
pub trait MultiplicativeOperation: ClosedMul<Output = Self> {}

// A magma is a set `S` with a binary operation `*` that is closed.

// A semigroup is a set `S` with an associative binary operation.

// A monoid is a semigroup with an identity element.

// A group is a monoid with an inverse operation.

// A ring is a group with a second binary operation.

// An integral domain is a commutative ring with no zero divisors.

// A field is a commutative ring where every non-zero element has a multiplicative inverse.

// A finite field is a field with a finite number of elements.

// A field extension is a field that contains another field as a subfield.

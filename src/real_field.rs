use crate::Field;

/// Represents a Real Field, an ordered field that satisfies the completeness axiom.
///
/// A real field (F, +, ·, ≤) consists of:
/// - A set F
/// - Two binary operations + (addition) and · (multiplication)
/// - A total order relation ≤
///
/// Formal Definition:
/// 1. (F, +, ·) is a field
/// 2. (F, ≤) is a totally ordered set
/// 3. The order is compatible with field operations
/// 4. F satisfies the completeness axiom
pub trait RealField: Field + PartialOrd + Ord {
    /// Returns the absolute value of the number.
    fn abs(&self) -> Self;

    /// Returns the square root of the number, if it exists.
    fn sqrt(&self) -> Option<Self>;

    /// Computes the natural logarithm of the number.
    fn ln(&self) -> Self;

    /// Raises e (Euler's number) to the power of self.
    fn exp(&self) -> Self;

    /// Computes the sine of the number (assumed to be in radians).
    fn sin(&self) -> Self;

    /// Computes the cosine of the number (assumed to be in radians).
    fn cos(&self) -> Self;

    /// Computes the tangent of the number (assumed to be in radians).
    fn tan(&self) -> Self;

    /// Returns the smallest integer greater than or equal to the number.
    fn ceil(&self) -> Self;

    /// Returns the largest integer less than or equal to the number.
    fn floor(&self) -> Self;

    /// Rounds the number to the nearest integer.
    fn round(&self) -> Self;

    /// Checks if the number is finite (not infinite and not NaN).
    fn is_finite(&self) -> bool;

    /// Checks if the number is infinite.
    fn is_infinite(&self) -> bool;

    /// Checks if the number is NaN (Not a Number).
    fn is_nan(&self) -> bool;
}


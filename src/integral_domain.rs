use crate::ring::Ring;
use crate::ClosedDiv;
use std::ops::Div;

/// Represents an Integral Domain, a commutative ring with no zero divisors.
///
/// An integral domain (D, +, ·) consists of:
/// - A set D
/// - Two binary operations + (addition) and · (multiplication) on D
/// - Two distinguished elements 0 (zero) and 1 (unity) of D
///
/// Formal Definition:
/// Let (D, +, ·) be an integral domain. Then:
/// 1. (D, +, ·) is a commutative ring
/// 2. D has no zero divisors:
///    ∀ a, b ∈ D, if a · b = 0, then a = 0 or b = 0
/// 3. The zero element is distinct from the unity:
///    0 ≠ 1
pub trait IntegralDomain: Ring + ClosedDiv {}

impl<T> IntegralDomain for T where T: Ring + Div<Output = T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::Z5;
    use num_traits::{One, Zero};
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn test_z5_implements_integral_domain() {
        fn assert_integral_domain<T: IntegralDomain>() {}
        assert_integral_domain::<Z5>();
    }

    #[test]
    fn test_unity_not_zero() {
        let zero = Z5::zero();
        let one = Z5::one();
        assert_ne!(zero, one);
    }

    #[test]
    fn test_z5_division_by_zero() {
        let a = Z5::new(1);
        let zero = Z5::zero();

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _ = a / zero;
        }));

        assert!(result.is_err(), "Division by zero should panic");
    }
}

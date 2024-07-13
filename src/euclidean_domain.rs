use crate::PrincipalIdealDomain;

/// Represents a Euclidean Domain, an integral domain with a Euclidean function.
///
/// A Euclidean Domain (R, +, ·, φ) is a principal ideal domain equipped with a
/// Euclidean function φ: R\{0} → ℕ₀ that satisfies certain properties.
///
/// Formal Definition:
/// Let (R, +, ·) be an integral domain and φ: R\{0} → ℕ₀ a function. R is a Euclidean domain if:
/// 1. ∀a, b ∈ R, b ≠ 0, ∃!q, r ∈ R : a = bq + r ∧ (r = 0 ∨ φ(r) < φ(b)) (Division with Remainder)
/// 2. ∀a, b ∈ R\{0} : φ(a) ≤ φ(ab) (Multiplicative Property)
pub trait EuclideanDomain: PrincipalIdealDomain {
    /// The Euclidean function φ: R\{0} → ℕ₀
    /// Returns None if the input is zero.
    fn euclidean_function(&self) -> Option<usize>;

    /// Computes the greatest common divisor (GCD) using the Euclidean algorithm.
    fn gcd(mut a: Self, mut b: Self) -> Self
    where
        Self: Sized + Clone,
    {
        if b.is_zero() {
            return a;
        }

        while !b.is_zero() {
            let r = a.rem_euclid(&b);
            a = b;
            b = r;
        }

        a
    }
}

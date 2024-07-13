use crate::ClosedDiv;
use crate::{ClosedSub, EuclideanDomain};

/// Represents a Field, an algebraic structure that is a Euclidean domain where every non-zero element
/// has a multiplicative inverse.
///
/// A field (F, +, ·) consists of:
/// - A set F
/// - Two binary operations + (addition) and · (multiplication) on F
///
/// Formal Definition:
/// Let (F, +, ·) be a field. Then:
/// 1. (F, +, ·) is a Euclidean domain
/// 2. Every non-zero element has a multiplicative inverse
/// 3. 0 ≠ 1 (the additive identity is not equal to the multiplicative identity)
pub trait Field: EuclideanDomain + ClosedDiv + ClosedSub {}

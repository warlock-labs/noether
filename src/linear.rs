//! Linear transformations and bilinear forms.
//!
//! This module provides traits for linear maps, bilinear forms, and related concepts.
//! These are fundamental structures in linear algebra and multilinear algebra.
//!
//! # Linear Algebra Structures
//!
//! - **Linear Map**: A function between vector spaces that preserves vector addition and scalar multiplication
//! - **Bilinear Form**: A function that takes two vectors and returns a scalar, linear in each argument
//! - **Symmetric Bilinear Form**: A bilinear form where B(v,w) = B(w,v) for all vectors v, w
//! - **Positive Definite Form**: A symmetric bilinear form where B(v,v) > 0 for all non-zero vectors v

use crate::fields::Field;
use crate::spaces::VectorSpace;

/// Represents a linear map (linear transformation) between vector spaces.
///
/// # Mathematical Definition
/// Let V and W be vector spaces over a field F. A linear map T: V → W is a function
/// satisfying the following properties for all u, v ∈ V and α ∈ F:
///
/// 1. T(u + v) = T(u) + T(v) (additivity)
/// 2. T(αv) = αT(v) (homogeneity)
///
/// # Properties
/// - The kernel (or null space) ker(T) = {v ∈ V | T(v) = 0} is a subspace of V
/// - The image (or range) im(T) = {T(v) | v ∈ V} is a subspace of W
/// - The rank-nullity theorem: dim(V) = dim(ker(T)) + dim(im(T))
/// - Examples: Derivative operators, rotation matrices, projection mappings
pub trait LinearMap<F: Field, V: VectorSpace<F>, W: VectorSpace<F>> {
    /// Applies the linear map to a vector: T(v)
    fn apply(&self, v: &V) -> W;

    /// Returns the dimension of the kernel (null space): dim(ker(T))
    fn kernel_dimension(&self) -> usize;

    /// Returns the dimension of the image (range): dim(im(T))
    fn image_dimension(&self) -> usize;
}

/// Represents a bilinear form on a vector space.
///
/// # Mathematical Definition
/// Given a vector space V over a field F, a bilinear form B: V × V → F is a function
/// satisfying the following properties for all u, v, w ∈ V and α, β ∈ F:
///
/// 1. B(αu + βv, w) = αB(u, w) + βB(v, w) (linearity in first argument)
/// 2. B(u, αv + βw) = αB(u, v) + βB(u, w) (linearity in second argument)
///
/// # Properties
/// - Can be represented by a matrix in finite dimensions
/// - The quadratic form associated with B is Q(v) = B(v, v)
/// - Types include: symmetric, skew-symmetric, alternating, non-degenerate forms
/// - Examples: dot product, matrix trace, determinant of the Gram matrix
pub trait BilinearForm<F: Field, V: VectorSpace<F>> {
    /// Evaluates the bilinear form B(v1, v2) on two vectors
    fn evaluate(&self, v1: &V, v2: &V) -> F;

    /// Checks if the bilinear form is symmetric: B(v, w) = B(w, v) for all v, w ∈ V
    fn is_symmetric(&self) -> bool;

    /// Checks if the bilinear form is non-degenerate:
    /// B(v, w) = 0 for all w ∈ V implies v = 0
    fn is_non_degenerate(&self) -> bool;
}

/// Marker trait for symmetric bilinear forms.
///
/// # Mathematical Definition
/// A bilinear form B: V × V → F is symmetric if:
/// B(v, w) = B(w, v) for all v, w ∈ V
///
/// # Properties
/// - The associated quadratic form fully determines the bilinear form
/// - Can be diagonalized in finite dimensions (spectral theorem)
/// - Examples: dot product in Euclidean space, energy forms in physics
pub trait SymmetricBilinearForm<F: Field, V: VectorSpace<F>>: BilinearForm<F, V> {}

/// Marker trait for positive definite bilinear forms.
///
/// # Mathematical Definition
/// A symmetric bilinear form B: V × V → F is positive definite if:
/// B(v, v) > 0 for all non-zero v ∈ V
///
/// # PropertiesE
/// - Induces an inner product structure on the vector space
/// - Allows for definitions of length, angle, and orthogonality
/// - The Gram-Schmidt process applies to these spaces
/// - Examples: standard dot product in Rⁿ, Hermitian inner products
pub trait PositiveDefinite<F: crate::fields::OrderedField, V: VectorSpace<F>>:
    SymmetricBilinearForm<F, V>
{
}

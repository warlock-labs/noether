//! Tensor algebra structures.
//!
//! This module provides traits for tensor products, tensor spaces, and tensor operations.
//! Tensor algebra generalizes linear algebra to multilinear structures and provides
//! a unified framework for working with vectors, matrices, and higher-dimensional arrays.
//!
//! # Tensor Algebra Concepts
//!
//! - **Tensor Product**: An operation that combines vector spaces to create a new space
//! - **Tensor Space**: A space of multilinear maps or tensors of certain rank
//! - **Tensor Contraction**: Operation that reduces tensor rank by "summing out" indices
//! - **Tensor Rank**: Number of indices needed to specify tensor components

use crate::fields::Field;
use crate::spaces::VectorSpace;

/// Represents a tensor product of vector spaces.
///
/// # Mathematical Definition
/// Given vector spaces V and W over a field F, their tensor product V ⊗ W is a vector space
/// equipped with a bilinear map ⊗: V × W → V ⊗ W satisfying the universal property:
///
/// For any vector space U and any bilinear map f: V × W → U, there exists a unique linear map
/// g: V ⊗ W → U such that f = g ∘ ⊗.
///
/// # Properties
/// - If dim(V) = n and dim(W) = m, then dim(V ⊗ W) = n·m
/// - Elements of V ⊗ W are linear combinations of elementary tensors v ⊗ w
/// - For basis {vᵢ} of V and {wⱼ} of W, {vᵢ ⊗ wⱼ} forms a basis of V ⊗ W
/// - Fundamental to multilinear algebra, differential geometry, and quantum mechanics
pub trait TensorProduct<F: Field, V: VectorSpace<F>, W: VectorSpace<F>> {
    /// The result type of the tensor product
    type Product: VectorSpace<F>;

    /// Computes the tensor product of two vectors: v ⊗ w
    fn tensor_product(v: &V, w: &W) -> Self::Product;
}

/// Represents a tensor space (space of multilinear maps).
///
/// # Mathematical Definition
/// A tensor of rank (r,s) over a vector space V is a multilinear map:
/// T: V* × ... × V* × V × ... × V → F
///    ⌊--- r ---⌋  ⌊--- s ---⌋
///
/// where V* is the dual space of V, taking r dual vectors and s vectors as input.
///
/// # Properties
/// - The rank (r,s) indicates the number of contravariant and covariant indices
/// - A tensor of rank (0,0) is a scalar, (0,1) is a vector, (1,0) is a covector,
///   (0,2) is a bilinear form, (1,1) is a linear operator
/// - Operations include tensor product, contraction, and index manipulation
/// - Forms the mathematical foundation for general relativity and quantum field theory
pub trait TensorSpace<F: Field>: VectorSpace<F> {
    /// Returns the total rank of the tensor (number of indices)
    fn rank(&self) -> usize;

    /// Computes the tensor product with another tensor: self ⊗ other
    fn tensor_product<T: TensorSpace<F>>(&self, other: &T) -> Self;

    /// Performs contraction on specified indices (summing over paired indices)
    ///
    /// For a tensor T of rank (r,s), contraction on indices i and j reduces rank by 2,
    /// creating a tensor of rank (r-1,s-1) by "connecting" and summing over those indices.
    ///
    /// TODO: Future enhancement could use const generics:
    /// ```text
    /// fn contract<const I: usize, const J: usize>(&self) -> Option<Self>;
    /// ```
    fn contract(&self, i: usize, j: usize) -> Option<Self>;

    /// Performs a tensor trace (contraction of all possible paired indices)
    ///
    /// For even-ranked tensors, this results in a scalar value.
    ///
    /// TODO: Future enhancement could leverage type-level operations:
    /// ```text
    /// fn trace(&self) -> F where Self::Rank: IsEven;
    /// ```
    fn trace(&self) -> F;

    /// Transposes the tensor by swapping two indices
    ///
    /// Changes the order of indices without changing the tensor's values.
    ///
    /// TODO: Future enhancement could use const generics:
    /// ```text
    /// fn transpose<const I: usize, const J: usize>(&self) -> Self;
    /// ```
    fn transpose(&self, i: usize, j: usize) -> Self;
}

/// Marker trait for covariant tensors.
///
/// # Mathematical Definition
/// A covariant tensor of rank k is a multilinear map T: V × ... × V → F
///                                                        (k times)
/// taking k vectors as input and returning a scalar.
///
/// # Properties
/// - Transforms with the inverse of the transformation matrix under coordinate changes
/// - Written with lower indices in index notation: T_ijk
/// - Examples: metric tensor, differential forms, covectors (dual vectors)
pub trait CovariantTensor<F: Field>: TensorSpace<F> {}

/// Marker trait for contravariant tensors.
///
/// # Mathematical Definition
/// A contravariant tensor of rank k is a multilinear map T: V* × ... × V* → F
///                                                           (k times)
/// taking k dual vectors (elements of the dual space V*) as input and returning a scalar.
///
/// # Properties
/// - Transforms with the transformation matrix under coordinate changes
/// - Written with upper indices in index notation: T^ijk
/// - Examples: vectors, velocity, coordinate basis vectors
pub trait ContravariantTensor<F: Field>: TensorSpace<F> {}

/// Marker trait for mixed tensors.
///
/// # Mathematical Definition
/// A mixed tensor of rank (r,s) is a multilinear map T: V* × ... × V* × V × ... × V → F
///                                                        (r times)   (s times)
/// with r contravariant indices and s covariant indices.
///
/// # Properties
/// - Transforms with both transformation matrix and its inverse under coordinate changes
/// - Written with both upper and lower indices: T^ij_kl
/// - Examples: Riemann curvature tensor, stress-energy tensor, electromagnetic field tensor
pub trait MixedTensor<F: Field>: TensorSpace<F> {
    /// Returns the number of covariant indices (lower indices)
    ///
    /// TODO: Future enhancement could use type-level dimensions:
    /// ```text
    /// type CovariantRank: Dimension;
    /// ```
    fn covariant_rank(&self) -> usize;

    /// Returns the number of contravariant indices (upper indices)
    ///
    /// TODO: Future enhancement could use type-level dimensions:
    /// ```text
    /// type ContravariantRank: Dimension;
    /// ```
    fn contravariant_rank(&self) -> usize;
}

/// Trait representing Einstein summation convention.
///
/// # Mathematical Definition
/// Einstein summation convention is a notational convention where repeated indices
/// in a tensor expression are implicitly summed over. For example:
/// C_ik = A_ij · B^j_k implies summation: C_ik = Σ_j A_ij · B^j_k
///
/// # Properties
/// - Provides a compact notation for tensor contractions and products
/// - Each repeated index (one up, one down) indicates a contraction
/// - Fundamental to tensor calculus in physics and differential geometry
/// - Examples: matrix multiplication, dot product, trace operations
pub trait EinsteinSummation<F: Field> {
    /// The result type of the summation
    type Output: TensorSpace<F>;

    /// Performs the summation according to the specified indices
    ///
    /// The indices array specifies which indices should be contracted (summed over).
    ///
    /// TODO: Future enhancement could use const generics:
    /// ```text
    /// fn einsum<const INDICES: &'static [usize]>(&self) -> Self::Output;
    /// ```
    fn einsum(&self, indices: &[usize]) -> Self::Output;
}

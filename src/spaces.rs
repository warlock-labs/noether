//! Vector spaces and modules.
//!
//! This module provides traits for vector spaces, modules, and related algebraic structures.
//! These structures are fundamental in linear algebra and representation theory.
//!
//! # Module Theory
//!
//! Modules generalize vector spaces by allowing scalars from a ring (rather than a field).
//! The key structures in this hierarchy are:
//!
//! - **Module**: An additive abelian group with scalar multiplication from a ring
//! - **Free Module**: A module with a basis of linearly independent elements
//! - **Vector Space**: A module over a field
//! - **Inner Product Space**: A vector space with a bilinear form for computing angles/distances
//! - **Normed Vector Space**: A vector space with a norm function for measuring vector lengths

use crate::fields::Field;
use crate::groups::AdditiveAbelianGroup;
use crate::rings::Ring;

/// Represents a module over a ring R.
///
/// # Mathematical Definition
/// A module M over a ring R is an additive abelian group (M, +) together with
/// a scalar multiplication operation R × M → M, denoted (r, m) ↦ r·m,
/// satisfying the following axioms for all r, s ∈ R and m, n ∈ M:
///
/// 1. r·(m + n) = r·m + r·n
/// 2. (r + s)·m = r·m + s·m
/// 3. (r·s)·m = r·(s·m)
/// 4. 1·m = m (if R has multiplicative identity 1)
///
/// # Properties
/// - Generalizes vector spaces by allowing scalars from rings instead of fields
/// - Includes vector spaces, abelian groups, and ideals as special cases
/// - Examples: R-modules, Z-modules (abelian groups), vector spaces over fields
pub trait Module<R: Ring>: AdditiveAbelianGroup {
    /// Performs scalar multiplication
    fn scale(&self, r: &R) -> Self;

    /// Checks if this module is free (has a basis)
    fn is_free() -> bool;
}

/// Represents a free module over a ring with a finite basis.
///
/// # Mathematical Definition
/// A free module F over a ring R is a module that has a basis (a linearly independent
/// generating set). For any set S, the free module on S over R, denoted R⟨S⟩, is a module
/// with basis elements indexed by S.
///
/// Formally, a module F is free if there exists a set S and an injection ι: S → F such that
/// for any module M and any function f: S → M, there exists a unique module homomorphism
/// φ: F → M such that f = φ ∘ ι.
///
/// # Properties
/// - Every element can be written uniquely as a linear combination of basis elements
/// - The dimension (or rank) is the cardinality of any basis
/// - Examples: Rⁿ is a free module over R, vector spaces are free modules over fields
/// - Free modules generalize the concept of vector spaces to modules over arbitrary rings
pub trait FreeModule<R: Ring>: Module<R> {
    /// Returns the rank (dimension) of the free module
    fn rank() -> usize;

    /// Returns a basis element by index
    fn basis_element(index: usize) -> Self;

    /// Expresses a vector in terms of the basis (coordinate representation)
    fn coordinates(&self) -> Vec<R>;
}

/// Represents a Vector Space over a field.
///
/// # Mathematical Definition
/// A vector space V over a field F is an additive abelian group (V, +) equipped with a scalar
/// multiplication operation F × V → V, denoted (α, v) ↦ α·v, satisfying the following
/// axioms for all α, β ∈ F and u, v ∈ V:
///
/// 1. α·(u + v) = α·u + α·v (distributivity of scalar multiplication over vector addition)
/// 2. (α + β)·v = α·v + β·v (distributivity of scalar multiplication over field addition)
/// 3. (α·β)·v = α·(β·v) (compatibility with field multiplication)
/// 4. 1·v = v (scalar identity)
///
/// # Properties
/// - A vector space is a module over a field
/// - Every vector space has a basis and is therefore a free module
/// - The dimension of a vector space is the cardinality of any basis
/// - Examples: Rⁿ, function spaces, polynomial spaces, matrix spaces
/// - Vector spaces are foundational to linear algebra and functional analysis
pub trait VectorSpace<F: Field>: Module<F> {
    /// Returns the dimension of the vector space
    fn dimension() -> usize;

    /// Returns a basis for the vector space
    fn basis() -> Vec<Self>;

    /// Computes the linear combination of vectors
    fn linear_combination<I: IntoIterator<Item = (F, Self)>>(items: I) -> Self {
        let mut result = Self::zero();
        for (scalar, vector) in items {
            let scaled = vector.scale(&scalar);
            result += scaled;
        }
        result
    }
}

/// Represents an inner product space.
///
/// # Mathematical Definition
/// An inner product space (V, ⟨·,·⟩) is a vector space V over a field F (typically ℝ or ℂ)
/// equipped with an inner product ⟨·,·⟩: V × V → F satisfying the following axioms
/// for all u, v, w ∈ V and α ∈ F:
///
/// 1. ⟨u, v⟩ = ⟨v, u⟩* (conjugate symmetry, where * denotes complex conjugation)
/// 2. ⟨αu, v⟩ = α⟨u, v⟩ (linearity in first argument)
/// 3. ⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩ (additivity in first argument)
/// 4. ⟨v, v⟩ ≥ 0 for all v ∈ V (non-negativity)
/// 5. ⟨v, v⟩ = 0 if and only if v = 0 (positive definiteness)
///
/// # Properties
/// - Induces a norm through ||v|| = √⟨v, v⟩
/// - Enables concepts of angle and orthogonality between vectors
/// - Generalizes the dot product in Euclidean space
/// - Examples: Euclidean spaces, function spaces with L² inner product, Hilbert spaces
pub trait InnerProductSpace<F: Field>: VectorSpace<F> {
    /// Computes the inner product ⟨self, other⟩ of two vectors
    fn inner_product(&self, other: &Self) -> F;

    /// Computes the norm ||self|| = √⟨self, self⟩ of a vector
    fn norm(&self) -> F;

    /// Normalizes a vector to unit length: v/||v||
    fn normalize(&self) -> Self;

    /// Computes the distance ||self - other|| between two vectors
    fn distance(&self, other: &Self) -> F;

    /// Checks if two vectors are orthogonal (⟨self, other⟩ = 0)
    fn is_orthogonal(&self, other: &Self) -> bool;
}

/// Represents a normed vector space.
///
/// # Mathematical Definition
/// A normed vector space (V, ||·||) is a vector space V over a field F equipped with
/// a norm function ||·||: V → ℝ₊ satisfying the following axioms for all u, v ∈ V and α ∈ F:
///
/// 1. ||v|| ≥ 0 for all v ∈ V (non-negativity)
/// 2. ||v|| = 0 if and only if v = 0 (positive definiteness)
/// 3. ||αv|| = |α|·||v|| (homogeneity)
/// 4. ||u + v|| ≤ ||u|| + ||v|| (triangle inequality)
///
/// # Properties
/// - Makes the vector space into a metric space with distance d(u,v) = ||u-v||
/// - Generalizes the concept of "length" or "magnitude" to abstract vector spaces
/// - Weaker structure than an inner product space (every inner product induces a norm)
/// - Examples: Lᵖ spaces, spaces of continuous functions with supremum norm
pub trait NormedVectorSpace<F: crate::fields::OrderedField>: VectorSpace<F> {
    /// Computes the norm ||self|| of a vector
    fn norm(&self) -> F;

    /// Normalizes a vector to unit length: v/||v||
    fn normalize(&self) -> Self;

    /// Computes the distance ||self - other|| between two vectors
    fn distance(&self, other: &Self) -> F;
}

// VectorSpace
// Note: This cannot be implemented as a blanket impl because it requires specific vector space structure

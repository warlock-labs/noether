//! Vector spaces and related algebraic structures.
//!
//! This module provides traits for vector spaces and their specializations
//! that are compatible with multidimensional array implementations.
//!
//! # Vector Space Structures
//!
//! - **Module**: A structure with scalar multiplication from a ring
//! - **FreeModule**: A module with a basis
//! - **VectorSpace**: A space supporting scalar multiplication and vector operations
//! - **InnerProductSpace**: A vector space with an inner product operation
//! - **NormedVectorSpace**: A vector space with a norm function
//! - **EuclideanSpace**: A vector space with Euclidean properties

use crate::fields::Field;
use crate::groups::AdditiveAbelianGroup;
use crate::rings::Ring;
use num_traits::{One, Zero};
use std::ops::{Add, Neg, Sub};

/// Represents a vector space over a field.
///
/// # Mathematical Definition
/// A vector space V over a field F is a set equipped with vector addition
/// and scalar multiplication operations, satisfying the vector space axioms:
///
/// 1. (u + v) + w = u + (v + w) for all u, v, w ∈ V (associativity of addition)
/// 2. v + u = u + v for all u, v ∈ V (commutativity of addition)
/// 3. There exists 0 ∈ V such that v + 0 = v for all v ∈ V (zero vector)
/// 4. For each v ∈ V, there exists -v ∈ V such that v + (-v) = 0 (additive inverse)
/// 5. a(bv) = (ab)v for all a, b ∈ F and v ∈ V (compatibility of scalar multiplication)
/// 6. 1v = v for all v ∈ V, where 1 is the multiplicative identity in F
/// 7. a(u + v) = au + av for all a ∈ F and u, v ∈ V (distributivity over vector addition)
/// 8. (a + b)v = av + bv for all a, b ∈ F and v ∈ V (distributivity over field addition)
///
/// # Properties
/// - Supports operations like addition, subtraction, and scalar multiplication
/// - Elements can be represented as linear combinations of basis vectors
/// - The number of basis elements determines the dimension of the space
pub trait VectorSpace<F: Field>:
    Add<Output = Self> + Sub<Output = Self> + Neg<Output = Self> + Sized + Clone
{
    /// Get the dimension of this vector space
    fn dimension() -> usize;

    /// Get the shape of this vector (if multidimensional)
    fn shape(&self) -> Vec<usize>;

    /// Multiply the vector by a scalar
    fn scale(&self, scalar: &F) -> Self;

    /// Create a zero vector of the same shape as this vector
    fn zero_like(&self) -> Self;

    /// Create a vector filled with ones of the same shape as this vector
    fn ones_like(&self) -> Self;

    /// Get a basis for this vector space
    fn basis() -> Vec<Self>;

    /// Compute the linear combination of vectors with their corresponding scalars
    fn linear_combination<I: IntoIterator<Item = (F, Self)>>(items: I) -> Option<Self>
    where
        F: Zero + Clone,
    {
        let mut iter = items.into_iter();

        // Get the first item to determine the shape
        if let Some((scalar, vector)) = iter.next() {
            let mut result = vector.scale(&scalar);

            // Add remaining scaled vectors
            for (scalar, vector) in iter {
                result = result + vector.scale(&scalar);
            }

            Some(result)
        } else {
            None
        }
    }
}

/// Represents an inner product space.
///
/// # Mathematical Definition
/// An inner product space is a vector space equipped with an inner product operation
/// that allows for notions of length, angle, and orthogonality.
///
/// The inner product ⟨·,·⟩ satisfies:
/// 1. ⟨u, v⟩ = ⟨v, u⟩* (conjugate symmetry)
/// 2. ⟨au + bv, w⟩ = a⟨u, w⟩ + b⟨v, w⟩ (linearity in first argument)
/// 3. ⟨v, v⟩ > 0 for all v ≠ 0 (positive definiteness)
///
/// # Properties
/// - Induces a natural norm: ||v|| = √⟨v, v⟩
/// - Allows definition of angles between vectors
/// - Enables orthogonal decompositions
pub trait InnerProductSpace<F: Field>: VectorSpace<F> {
    /// Compute the inner product between two vectors
    fn inner_product(&self, other: &Self) -> F;

    /// Compute the squared norm of a vector (avoid sqrt when possible)
    fn squared_norm(&self) -> F {
        self.inner_product(self)
    }

    /// Compute the norm (length) of a vector
    fn norm(&self) -> F;

    /// Normalize a vector to unit length
    fn normalize(&self) -> Self
    where
        F: One + Zero,
    {
        let norm = self.norm();
        if norm == F::zero() {
            self.clone()
        } else {
            let one_over_norm = F::one() / norm;
            self.scale(&one_over_norm)
        }
    }

    /// Compute the distance between two vectors
    fn distance(&self, other: &Self) -> F {
        let diff = self.clone() - other.clone();
        diff.norm()
    }

    /// Check if two vectors are orthogonal
    fn is_orthogonal(&self, other: &Self) -> bool
    where
        F: Zero,
    {
        self.inner_product(other) == F::zero()
    }
}

/// Represents a normed vector space.
///
/// # Mathematical Definition
/// A normed vector space is a vector space equipped with a norm function
/// that assigns a non-negative length to each vector.
///
/// # Properties
/// - The norm satisfies: ||v|| ≥ 0, ||v|| = 0 iff v = 0, ||av|| = |a|·||v||, ||u+v|| ≤ ||u||+||v||
/// - Induces a metric: d(u,v) = ||u-v||
/// - Every inner product space is a normed space, but not vice versa
pub trait NormedVectorSpace<F: crate::fields::OrderedField>: VectorSpace<F> {
    /// Compute the norm (length) of a vector
    fn norm(&self) -> F;

    /// Normalize a vector to unit length
    fn normalize(&self) -> Self
    where
        F: One + Zero,
    {
        let norm = self.norm();
        if norm == F::zero() {
            self.clone()
        } else {
            let one_over_norm = F::one() / norm;
            self.scale(&one_over_norm)
        }
    }

    /// Compute the distance between two vectors
    fn distance(&self, other: &Self) -> F {
        let diff = self.clone() - other.clone();
        diff.norm()
    }
}

/// Represents a Euclidean space.
///
/// # Mathematical Definition
/// A Euclidean space is a finite-dimensional inner product space over the real numbers,
/// equipped with the standard Euclidean inner product.
///
/// # Properties
/// - Has a natural notion of distance and angle
/// - Can be identified with R^n for some n
/// - Supports geometric operations like orthogonal projections
pub trait EuclideanSpace<F: crate::fields::RealField>:
    InnerProductSpace<F> + NormedVectorSpace<F>
{
    /// Project one vector onto another
    fn project_onto(&self, other: &Self) -> Self
    where
        F: Zero + Clone,
    {
        let scalar = self.inner_product(other) / other.squared_norm();
        other.scale(&scalar)
    }
}

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
    /// Multiply by a scalar from the ring
    fn scale(&self, r: &R) -> Self;

    /// Create a zero element of this module
    fn zero() -> Self;

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
/// # Properties
/// - Every element can be written uniquely as a linear combination of basis elements
/// - The dimension (or rank) is the cardinality of any basis
/// - Examples: Rⁿ is a free module over R, vector spaces are free modules over fields
pub trait FreeModule<R: Ring>: Module<R> {
    /// Get the rank (dimension) of this free module
    fn rank() -> usize;

    /// Get a basis element by index
    fn basis_element(index: usize) -> Self;

    /// Express this element in terms of the basis
    fn coordinates(&self) -> Vec<R>;
}

//! Dimensional traits for multidimensional structures.
//!
//! This module provides traits for working with dimensions in a type-safe manner,
//! enabling compile-time dimensional analysis. This approach leverages Rust's const generics
//! to catch dimensional errors at compile time rather than runtime.
//!
//! # Dimensional Structures
//!
//! - **`Dimensional<N>`**: A trait for N-dimensional structures with shape information
//! - **`HasShape<N>`**: A trait for enforcing specific shapes at compile-time
//! - **`HasDimension<D>`**: A trait marker for fixed-dimension spaces

/// Trait for N-dimensional structures.
///
/// # Mathematical Definition
/// An N-dimensional structure has a shape represented as an N-tuple of sizes
/// (d₁, d₂, ..., dₙ), where each dᵢ represents the size of the structure along
/// the i-th dimension.
///
/// # Properties
/// - Provides shape information for N-dimensional structures
/// - Works with const generics to represent dimensionality
/// - Enables compile-time dimension checking
/// - Supports dimensional compatibility verification for operations
pub trait Dimensional<const N: usize> {
    /// Returns the shape of the N-dimensional structure
    fn shape(&self) -> [usize; N];

    /// Returns the total number of elements in the structure
    fn size(&self) -> usize {
        self.shape().iter().product()
    }

    /// Returns the size along the specified axis
    fn size_along(&self, axis: usize) -> usize {
        assert!(axis < N, "Axis out of bounds");
        self.shape()[axis]
    }
}

/// Trait for enforcing specific shapes.
///
/// # Mathematical Definition
/// A shape in the context of multi-dimensional arrays or tensors is an ordered tuple
/// (d₁, d₂, ..., dₙ) representing the size of each dimension.
///
/// # Properties
/// - Provides shape compatibility checking
/// - Useful for operations that require specific shapes
pub trait HasShape<const N: usize> {
    /// Check if this shape matches a specific expected shape
    fn has_shape(&self, shape: &[usize; N]) -> bool;
}

/// Trait marker for fixed-dimension spaces.
///
/// # Mathematical Definition
/// A dimension D in the context of vector spaces corresponds to the cardinality
/// of a basis. For a D-dimensional vector space V, there exists a basis
/// {v₁, v₂, ..., vₚ} such that any vector in V can be uniquely written as a
/// linear combination of these basis vectors.
///
/// # Properties
/// - Type-level encoding of dimensional information
/// - Enables compile-time dimension checking
/// - Useful for specialized algorithms based on dimension
pub trait HasDimension<const D: usize> {}

/// Marker trait for square matrices
pub trait IsSquare {}

// Implement for any Dimensional with equal first two dimensions
impl<T: Dimensional<2>> IsSquare for T
where
    T: Dimensional<2>,
{
    // This is automatically true when the first two dimensions are equal
    // No need for additional methods
}

/// Utility function to check if a dimension is even.
///
/// Returns true if n is divisible by 2 (n mod 2 = 0).
pub fn is_even(n: usize) -> bool {
    n % 2 == 0
}

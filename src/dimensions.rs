//! Type-level dimension handling.
//!
//! This module provides traits and types for working with dimensions in a type-safe manner,
//! enabling compile-time dimensional analysis. This approach leverages Rust's type system
//! to catch dimensional errors at compile time rather than runtime.
//!
//! # Type-Level Dimensions
//!
//! Type-level dimensions encode numeric values in the type system itself, allowing for:
//!
//! - Detection of dimensional mismatches at compile time
//! - Zero-cost abstractions for dimensional safety
//! - Specialization of algorithms based on dimension properties
//! - Advanced type-checking for linear algebra operations

/// Trait defining dimension in a type-level context.
///
/// # Mathematical Definition
/// A dimension in the context of vector spaces corresponds to the cardinality
/// of a basis. For an n-dimensional vector space V, there exists a basis
/// {v₁, v₂, ..., vₙ} such that any vector in V can be uniquely written as a
/// linear combination of these basis vectors.
///
/// # Properties
/// - Type-level encoding of dimensional information
/// - Enables compile-time dimension checking
/// - Works with const generics to parameterize types by dimension
/// - Can be used for static verification of linear algebra operations
pub trait Dimension {
    /// The numeric value of the dimension
    const VALUE: usize;
}

/// Type-level dimension representation.
///
/// # Mathematical Definition
/// Represents a fixed dimension N as a zero-sized type, allowing dimensions
/// to be tracked at the type level with no runtime overhead.
///
/// # Properties
/// - Zero-sized type (ZST) with no runtime cost
/// - Implements the Dimension trait, exposing the value N
/// - Can be used as a type parameter to dimension-parameterized types
/// - Example: A vector space of dimension N can be represented as `Vector<Dim<N>>`
pub struct Dim<const N: usize>;

impl<const N: usize> Dimension for Dim<N> {
    const VALUE: usize = N;
}

/// Trait defining shape for multi-dimensional structures.
///
/// # Mathematical Definition
/// A shape in the context of multi-dimensional arrays or tensors is an ordered tuple
/// (d₁, d₂, ..., dₙ) representing the size of each dimension. The number of dimensions n
/// is called the rank or order of the shape.
///
/// # Properties
/// - Generalizes the concept of dimension to multi-dimensional structures
/// - Used for tensor shapes, array dimensions, and matrix layouts
/// - Provides compile-time information about dimensional structure
/// - Enables shape compatibility checking for operations like matrix multiplication
pub trait Shape {
    /// The rank (number of dimensions) of the shape
    fn rank() -> usize;

    /// Returns the size of each dimension
    ///
    /// TODO: Future enhancement with const generics could use:
    /// ```text
    /// const RANK: usize;
    /// fn dimensions() -> [usize; Self::RANK];
    /// ```
    fn dimensions() -> Vec<usize>;
}

/// Type-level marker for even dimensions.
///
/// # Mathematical Definition
/// A dimension N is even if and only if N mod 2 = 0.
///
/// # Properties
/// - Used for type-level constraints on dimensions
/// - Enables specialized implementations for even-dimensioned structures
/// - Can be used for type safety in operations requiring even dimensions
/// - Examples: Certain matrix decompositions, symmetry operations, and block algorithms
pub trait IsEven: Dimension {}

/// Simple method to check if a dimension is even.
///
/// Returns true if n is divisible by 2 (n mod 2 = 0).
pub fn is_even(n: usize) -> bool {
    n % 2 == 0
}

// TODO: Future enhancements with unstable features could include:
// - Type-level equality checks (IsEqual<const N: usize>)
// - Compile-time checks for even/odd dimensions
// - More sophisticated type-level numeric operations

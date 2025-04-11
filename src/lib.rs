//! # Nœther
//!
//! Nœther provides traits and blanket implementations for algebraic structures,
//! from basic ones like magmas to more complex ones like fields. It also includes
//! linear algebra structures like vector spaces and tensors.
//!
//! Named after Emmy Nœther, a pioneering mathematician in abstract algebra,
//! this library aims to bridge the gap between abstract mathematics and practical
//! programming in Rust.

pub mod dimensions;
pub mod fields;
pub mod groups;
pub mod linear;
pub mod operations;
pub mod rings;
pub mod sets;
pub mod spaces;
pub mod tensors;

// Re-export the most commonly used traits
pub use dimensions::{Dim, Dimension, IsEven, Shape};
pub use fields::{Field, FieldExtension, FiniteField, OrderedField, RealField};
pub use groups::{
    AdditiveAbelianGroup, AdditiveGroup, AdditiveMagma, AdditiveMonoid, AdditiveSemigroup,
    MultiplicativeAbelianGroup, MultiplicativeGroup, MultiplicativeMagma, MultiplicativeMonoid,
    MultiplicativeSemigroup,
};
pub use linear::{BilinearForm, LinearMap, SymmetricBilinearForm};
pub use operations::{
    AssociativeAddition, AssociativeMultiplication, CommutativeAddition, CommutativeMultiplication,
    Distributive,
};
pub use rings::{
    CommutativeRing, IntegralDomain, PrincipalIdealDomain, Ring, UniqueFactorizationDomain,
};
pub use sets::Set;
pub use spaces::{FreeModule, InnerProductSpace, Module, NormedVectorSpace, VectorSpace};
pub use tensors::{EinsteinSummation, TensorProduct, TensorSpace};

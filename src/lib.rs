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
pub mod primitives;
pub mod rings;
pub mod sets;
pub mod spaces;
pub mod tensors;

// Re-export the most commonly used traits
pub use dimensions::*;
pub use fields::*;
pub use groups::*;
pub use linear::*;
pub use operations::*;
pub use rings::*;
pub use sets::*;
pub use spaces::*;
pub use tensors::*;

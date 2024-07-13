//! # Noether
//!
//! Noether provides traits and blanket implementations for algebraic structures,
//! from basic ones like magmas to more complex ones like fields. It leans heavily on
//! the basic traits available in std::ops and num_traits.
//!
//! The goal is to provide a common interface for working with algebraic structures
//! in Rust.
//!
//! Interestingly, these traits can be used to categorize implementations of various
//! structs based on the properties they satisfy, and be applied in most cases for
//! anything from scalar values to n-dimensional arrays.
//!
//! ## Hierarchy of Scalar Algebraic Structures
//!
//! ```text
//!                               ┌─────┐
//!                               │ Set │
//!                               └──┬──┘
//!                                  │
//!                               ┌──▼──┐
//!                               │Magma│
//!                               └──┬──┘
//!                ┌────────────────┼────────────────┐
//!                │                │                │
//!          ┌─────▼─────┐    ┌─────▼─────┐    ┌─────▼─────┐
//!          │Quasigroup │    │ Semigroup │    │Semilattice│
//!          └─────┬─────┘    └─────┬─────┘    └───────────┘
//!                │                │
//!            ┌───▼───┐        ┌───▼───┐
//!            │ Loop  │        │Monoid │
//!            └───┬───┘        └───┬───┘
//!                │                │
//!                └────────┐ ┌─────┘
//!                         │ │
//!                      ┌──▼─▼──┐
//!                      │ Group │
//!                      └───┬───┘
//!                          │
//!                 ┌────────▼────────┐
//!                 │  Abelian Group  │
//!                 └────────┬────────┘
//!                          │
//!                     ┌────▼────┐
//!                     │Semiring │
//!                     └────┬────┘
//!                          │
//!                     ┌────▼────┐
//!                     │  Ring   │
//!                     └────┬────┘
//!           ┌───────────────────────┐
//!           │                       │
//!     ┌─────▼─────┐           ┌─────▼─────┐
//!     │  Module   │           │Commutative│
//!     └───────────┘           │   Ring    │
//!                             └─────┬─────┘
//!                                   │
//!                          ┌────────▼────────┐
//!                          │ Integral Domain │
//!                          └────────┬────────┘
//!                                   │
//!                     ┌─────────────▼─────────────┐
//!                     │Unique Factorization Domain│
//!                     └─────────────┬─────────────┘
//!                                   │
//!                       ┌───────────▼───────────┐
//!                       │Principal Ideal Domain │
//!                       └───────────┬───────────┘
//!                                   │
//!                          ┌────────▼────────┐
//!                          │Euclidean Domain │
//!                          └────────┬────────┘
//!                                   │
//!                               ┌───▼───┐
//!                               │ Field │────────────────────────┐
//!                               └───┬───┘                        │
//!                         ┌─────────┴──────────┐                 │
//!                         │                    │                 │
//!                   ┌─────▼─────┐        ┌─────▼─────┐     ┌─────▼─────┐
//!                   │   Finite  │        │ Infinite  │     │  Vector   │
//!                   │   Field   │        │   Field   │     │   Space   │
//!                   └─────┬─────┘        └───────────┘     └───────────┘
//!                         │
//!                   ┌─────▼─────┐
//!                   │   Field   │
//!                   │ Extension │
//!                   └─────┬─────┘
//!                         │
//!                   ┌─────▼─────┐
//!                   │ Extension │
//!                   │   Tower   │
//!                   └───────────┘
//! ```

mod magma;
mod operator;
mod set;

pub use set::*;

pub use operator::*;

pub use magma::*;

// Concrete implementations for tests
#[cfg(test)]
pub(crate) mod concrete;

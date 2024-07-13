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
//! ## Hierarchy of Algebraic Structures
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

// Concrete implemetations for tests
#[cfg(test)]
mod concrete;

// Implemented traits
mod abelian;
mod commutative_ring;
mod euclidean_domain;
mod field;
mod field_extension;
mod finite_field;
mod group;
mod infinite_field;
mod integral_domain;
mod magma;
mod monoid;
mod operator;
mod pid;
mod ring;
mod semigroup;
mod semiring;
mod set;
mod ufd;

// Not yet implemented
// mod alg_loop;
// mod quasigroup;
// mod semilattice;
// mod module;
// mod vector_space;

// Library level re-exports

pub use set::*;

pub use operator::*;

pub use magma::*;

pub use semigroup::*;

pub use monoid::*;

pub use group::*;

pub use abelian::*;

pub use semiring::*;

pub use ring::*;

pub use commutative_ring::*;

pub use integral_domain::*;

pub use ufd::*;

pub use pid::*;

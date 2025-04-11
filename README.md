![Logo](./noether.png)

# Nœther

[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/noether)](https://crates.io/crates/noether)
[![Docs](https://img.shields.io/docsrs/noether)](https://docs.rs/noether)
![CI](https://github.com/warlock-labs/noether/actions/workflows/CI.yml/badge.svg)

Nœther provides traits and blanket implementations for algebraic structures, from basic ones like magmas to more
complex ones like fields, vector spaces, and tensors. It defines a comprehensive hierarchy of mathematical abstractions, organized in a modular structure that follows the natural progression of abstract algebra. It leans heavily on the basic traits available in std::ops and num_traits while adding rich mathematical documentation with formal definitions.

## Table of Contents

- [Background](#background)
  - [Inspirations](#inspirations)
- [Features](#features)
- [Installation](#installation)
- [Usage](#usage)
- [Core Concepts](#core-concepts)
- [Hierarchy of Algebraic Structures](#hierarchy-of-algebraic-structures)
- [Operator Traits for Algebraic Structures](#operator-traits-for-algebraic-structures)
- [API Overview](#api-overview)
- [Advanced Usage](#advanced-usage)
- [Performance](#performance)
- [Roadmap](#roadmap)
- [Contributing](#contributing)
- [License](#license)

## Background

Named after Emmy Nœther, a pioneering mathematician in abstract algebra, this library aims to bridge the gap between
abstract mathematics and practical programming in Rust. It enables developers to work with mathematical concepts in a
type-safe, efficient, and expressive manner.

The goal is to provide a common interface for working with algebraic structures in Rust. Interestingly, these traits can
be used to categorize implementations of various structs based on the properties they satisfy, and be applied in most
cases for anything from scalar values to n-dimensional arrays.

### Inspirations

Nœther draws inspiration from several existing libraries and projects in the field of computational algebra:

1. [simba](https://crates.io/crates/simba): A Rust crate for SIMD-accelerated algebra.

2. [alga](https://github.com/dimforge/alga): A Rust library for abstract algebra, providing solid mathematical
   abstractions for algebra-focused applications. alga defines and organizes basic building blocks of general algebraic
   structures through trait inheritance.

3. [algebra](https://github.com/brendanzab/algebra): A Rust library for abstract algebra that organizes a wide range of
   structures into a logically consistent framework. It aims to create composable libraries and APIs based on algebraic
   classifications.

These libraries demonstrate the power and utility of representing algebraic structures in programming languages. Nœther
builds upon their ideas, aiming to provide a comprehensive and ergonomic framework for working with algebraic structures
in Rust.

Other notable inspirations from different programming languages include:

- Haskell's [Numeric Prelude](http://www.haskell.org/haskellwiki/Numeric_Prelude) and Edward A.
  Kmett's [algebra package](http://hackage.haskell.org/package/algebra-3.1)
- Agda's [algebra module](http://www.cse.chalmers.se/~nad/listings/lib-0.7/Algebra.html)
- Idris' [algebra module](https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/Algebra.idr)
- Scala's [spire](https://github.com/non/spire)

Nœther also draws insights from academic papers in the field:

- [The Scratchpad II Type System: Domains and Subdomains](http://www.csd.uwo.ca/~watt/pub/reprints/1990-miola-spadtypes.pdf)
- [Fundamental Algebraic Concepts in Concept-Enabled C++](ftp://cgi.cs.indiana.edu/pub/techreports/TR638.pdf)

Nœther aims to bring the best ideas from these libraries and research to the Rust ecosystem, while taking advantage of
Rust's unique features like zero-cost abstractions and powerful type system.

## Features

- Traits for a wide range of algebraic structures (e.g., Magma, Semigroup, Monoid, Group, Ring, Field)
- Marker traits for important algebraic properties (e.g., Associativity, Commutativity)
- Blanket implementations to reduce boilerplate code
- Support for both built-in and custom types
- Zero-cost abstractions leveraging Rust's type system
- Modular organization by mathematical domain
- Comprehensive UTF-8 mathematical documentation with formal definitions
- Type-level dimension handling for compile-time dimensional analysis
- Linear algebra abstractions including vector spaces, modules, and tensors
- Advanced structures like bilinear forms and tensor products

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
noether = "0.3.0"
```

## Usage

Here is a rough example of Z₅ (integers modulo 5) using Nœther:

```rust
use noether::{Field};
use std::ops::{Add, Sub, Mul, Div, Neg};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Z5(u8);

impl Z5 {
    fn new(n: u8) -> Self {
        Z5(n % 5)
    }
}

impl Add for Z5 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Z5((self.0 + rhs.0) % 5)
    }
}

impl Sub for Z5 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl Mul for Z5 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Z5((self.0 * rhs.0) % 5)
    }
}

impl Div for Z5 {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        if rhs.0 == 0 {
            panic!("Division by zero in Z5");
        }
        self * rhs.multiplicative_inverse().unwrap()
    }
}

impl Neg for Z5 {
    type Output = Self;
    fn neg(self) -> Self {
        Z5((5 - self.0) % 5)
    }
}

impl Field for Z5 {
    fn multiplicative_inverse(&self) -> Option<Self> {
        match self.0 {
            0 => None,
            1 | 4 => Some(*self),
            2 => Some(Z5(3)),
            3 => Some(Z5(2)),
            _ => unreachable!(),
        }
    }
}
```

This example shows how to construct a well factored finite field using Nœther,
leveraging Rust's native operators and traits.

## Core Concepts

1. **Algebraic Structures**: Traits representing mathematical structures with specific properties and operations.
2. **Marker Traits**: Traits like `Associative` and `Commutative` for compile-time property checks.
3. **Blanket Implementations**: Automatic implementations of higher-level traits based on more fundamental ones.
4. **Zero-Cost Abstractions**: Leveraging Rust's type system for efficiency without runtime overhead.
5. **Extensibility**: The library is designed to be easily extended with new types and structures.
6. **Type Safety**: Ensuring operations maintain closure within the same type and catching errors at compile-time.

## Hierarchy of Algebraic Structures

```text
                              ┌─────┐
                              │ Set │
                              └──┬──┘
                                 │
                              ┌──▼──┐
                              │Magma│
                              └──┬──┘
               ┌────────────────┼────────────────┐
               │                │                │
         ┌─────▼─────┐    ┌─────▼─────┐    ┌─────▼─────┐
         │Quasigroup │    │ Semigroup │    │Semilattice│
         └─────┬─────┘    └─────┬─────┘    └───────────┘
               │                │
           ┌───▼───┐        ┌───▼───┐
           │ Loop  │        │Monoid │
           └───┬───┘        └───┬───┘
               │                │
               └────────┐ ┌─────┘
                        │ │
                     ┌──▼─▼──┐
                     │ Group │
                     └───┬───┘
                         │
                ┌────────▼────────┐
                │  Abelian Group  │
                └────────┬────────┘
                         │
                    ┌────▼────┐
                    │Semiring │
                    └────┬────┘
                         │
                    ┌────▼────┐
                    │  Ring   │
                    └────┬────┘
          ┌───────────────────────┐
          │                       │
    ┌─────▼─────┐           ┌─────▼─────┐
    │  Module   │           │Commutative│
    └───────────┘           │   Ring    │
                            └─────┬─────┘
                                  │
                         ┌────────▼────────┐
                         │ Integral Domain │
                         └────────┬────────┘
                                  │
                    ┌─────────────▼─────────────┐
                    │Unique Factorization Domain│
                    └─────────────┬─────────────┘
                                  │
                      ┌───────────▼───────────┐
                      │Principal Ideal Domain │
                      └───────────┬───────────┘
                                  │
                         ┌────────▼────────┐
                         │Euclidean Domain │
                         └────────┬────────┘
                                  │
                              ┌───▼───┐
                              │ Field │────────────────────────┐
                              └───┬───┘                        │
                        ┌─────────┴──────────┐                 │
                        │                    │                 │
                  ┌─────▼─────┐        ┌─────▼─────┐     ┌─────▼─────┐
                  │   Finite  │        │ Infinite  │     │  Vector   │
                  │   Field   │        │   Field   │     │   Space   │
                  └─────┬─────┘        └───────────┘     └───────────┘
                        │
                  ┌─────▼─────┐
                  │   Field   │
                  │ Extension │
                  └─────┬─────┘
                        │
                  ┌─────▼─────┐
                  │ Extension │
                  │   Tower   │
                  └───────────┘
```

## Operator Traits for Algebraic Structures

This module defines traits for various operators and their properties, providing a foundation for implementing algebraic
structures in Rust.

An algebraic structure consists of a set with one or more binary operations. Let $S$ be a set (Self) and $\bullet$ be a
binary operation on $S$. Here are the key properties a binary operation may possess, organized from simplest to most
complex:

- (Closure) $\forall a, b \in S, a \bullet b \in S$ - Guaranteed by the operators provided
- (Totality) $\forall a, b \in S, a \bullet b$ is defined - Guaranteed by Rust
- (Commutativity) $\forall a, b \in S, a \bullet b = b \bullet a$ - Marker trait
- (Associativity) $\forall a, b, c \in S, (a \bullet b) \bullet c = a \bullet (b \bullet c)$ - Marker trait
- (Distributivity) $\forall a, b, c \in S, a * (b + c) = (a * b) + (a * c)$ - Marker trait

The traits and blanket implementations provided serve several important purposes:

1. Closure: All `Closed*` traits ensure that operations on a type always produce a result of the same type. This is
   crucial for defining algebraic structures.

2. Reference Operations: The `*Ref` variants of traits allow for more efficient operations when the right-hand side can
   be borrowed, which is common in many algorithms.

3. Marker Traits: Traits like `Commutative`, `Associative`, etc., allow types to declare which algebraic properties they
   satisfy. This can be used for compile-time checks and to enable more generic implementations of algorithms.

4. Extensibility: New types that implement the standard traits (like `Add`, `Sub`, etc.) will automatically get the
   closed trait implementations, making the system more extensible and future-proof.

5. Type Safety: These traits help in catching type-related errors at compile-time, ensuring that operations maintain
   closure within the same type.

6. Generic Programming: These traits enable more expressive generic programming, allowing functions and structs to be
   generic over types that are closed under certain operations or satisfy certain algebraic properties.

## API Overview

Nœther provides traits for various algebraic structures, including:

- `Magma`: Set with a binary operation
- `Semigroup`: Associative magma
- `Monoid`: Semigroup with identity element
- `Group`: Monoid where every element has an inverse
- `Ring`: Set with two operations (addition and multiplication) satisfying certain axioms
- `Field`: Commutative ring where every non-zero element has a multiplicative inverse
- `VectorSpace`: An abelian group with scalar multiplication over a field
- `Module`: Similar to a vector space, but over a ring instead of a field
- `Polynomial`: Represents polynomials over a field
- `FieldExtension`: Represents field extensions

Each trait comes with methods defining the operations and properties of the respective algebraic structure. For a
complete list of traits and their methods, please refer to the [API documentation](https://docs.rs/noether).

## Advanced Usage

Nœther's power lies in its ability to express complex mathematical concepts and algorithms generically. Here's an
example of a function that works with any type implementing the `Field` trait:

```rust
use noether::Field;

fn polynomial_evaluation<F: Field>(coefficients: &[F], x: F) -> F {
    coefficients.iter().rev().fold(F::zero(), |acc, &c| acc * x + c)
}

// This function works for any type implementing the Field trait
```

You can use this function with any type that implements the `Field` trait, whether it's a built-in numeric type or a
custom type like our `Z5` from the earlier example.

## Performance

Nœther is designed with performance in mind, leveraging Rust's zero-cost abstractions. The use of trait-based
polymorphism allows for efficient, monomorphized code when used with concrete types.

However, as with any abstract library, be aware that extensive use of dynamic dispatch (e.g., through trait objects) may
incur some runtime cost. In most cases, the compiler can optimize away the abstractions, resulting in performance
equivalent to hand-written implementations.

## Roadmap

For detailed development plans, see the [ROADMAP.md](ROADMAP.md) file, which outlines future directions including:

- Core algebraic traits and properties
- Category theory foundations
- Advanced algebraic systems
- Abstract linear algebra and multilinear algebra
- Type system improvements for compile-time verification

## Contributing

Contributions are welcome! Please feel free to submit issues, feature requests, or pull requests on
the [GitHub repository](https://github.com/warlock-labs/noether).

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

---

We hope that Nœther will be a valuable tool for cryptographers, mathematicians, scientists, and
developers working with algebraic structures in Rust. If you have any questions, suggestions, or
feedback, please don't hesitate to open an issue on our GitHub repository or contact the
maintainers.

Happy coding with Nœther!

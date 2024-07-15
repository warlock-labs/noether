use num_traits::{Euclid, Inv, One, Zero};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

// TODO(These marker traits could actually mean something and check things)

/// Marker trait for commutative addition
pub trait CommutativeAddition {}

/// Marker trait for commutative multiplication
pub trait CommutativeMultiplication {}

/// Marker trait for associative addition
pub trait AssociativeAddition {}

/// Marker trait for associative addition
pub trait AssociativeMultiplication {}

/// Marker trait for distributive operations
pub trait DistributiveAddition {}

/// Trait for closed addition operation.
pub trait ClosedAdd<Rhs = Self>: Add<Rhs, Output = Self> {}

/// Trait for closed addition operation with the right-hand side as a reference.
pub trait ClosedAddRef<Rhs = Self>: for<'a> Add<&'a Rhs, Output = Self> {}

/// Trait for closed subtraction operation.
pub trait ClosedSub<Rhs = Self>: Sub<Rhs, Output = Self> {}

/// Trait for closed subtraction operation with the right-hand side as a reference.
pub trait ClosedSubRef<Rhs = Self>: for<'a> Sub<&'a Rhs, Output = Self> {}

/// Trait for closed multiplication operation.
pub trait ClosedMul<Rhs = Self>: Mul<Rhs, Output = Self> {}

/// Trait for closed multiplication operation with the right-hand side as a reference.
pub trait ClosedMulRef<Rhs = Self>: for<'a> Mul<&'a Rhs, Output = Self> {}

/// Trait for closed division operation.
pub trait ClosedDiv<Rhs = Self>: Div<Rhs, Output = Self> {}

/// Trait for closed division operation with the right-hand side as a reference.
pub trait ClosedDivRef<Rhs = Self>: for<'a> Div<&'a Rhs, Output = Self> {}

/// Trait for closed remainder operation.
pub trait ClosedRem<Rhs = Self>: Rem<Rhs, Output = Self> {}

/// Trait for closed remainder operation with the right-hand side as a reference.
pub trait ClosedRemRef<Rhs = Self>: for<'a> Rem<&'a Rhs, Output = Self> {}

/// Trait for closed negation operation.
pub trait ClosedNeg: Neg<Output = Self> {}

/// Trait for closed negation operation.
pub trait ClosedInv: Inv<Output = Self> {}

/// Trait for closed addition assignment operation.
pub trait ClosedAddAssign<Rhs = Self>: AddAssign<Rhs> {}

/// Trait for closed addition assignment operation with the right-hand side as a reference.
pub trait ClosedAddAssignRef<Rhs = Self>: for<'a> AddAssign<&'a Rhs> {}

/// Trait for closed subtraction assignment operation.
pub trait ClosedSubAssign<Rhs = Self>: SubAssign<Rhs> {}

/// Trait for closed subtraction assignment operation with the right-hand side as a reference.
pub trait ClosedSubAssignRef<Rhs = Self>: for<'a> SubAssign<&'a Rhs> {}

/// Trait for closed multiplication assignment operation.
pub trait ClosedMulAssign<Rhs = Self>: MulAssign<Rhs> {}

/// Trait for closed multiplication assignment operation with the right-hand side as a reference.
pub trait ClosedMulAssignRef<Rhs = Self>: for<'a> MulAssign<&'a Rhs> {}

/// Trait for closed division assignment operation.
pub trait ClosedDivAssign<Rhs = Self>: DivAssign<Rhs> {}

/// Trait for closed division assignment operation with the right-hand side as a reference.
pub trait ClosedDivAssignRef<Rhs = Self>: for<'a> DivAssign<&'a Rhs> {}

/// Trait for closed remainder assignment operation.
pub trait ClosedRemAssign<Rhs = Self>: RemAssign<Rhs> {}

/// Trait for closed remainder assignment operation with the right-hand side as a reference.
pub trait ClosedRemAssignRef<Rhs = Self>: for<'a> RemAssign<&'a Rhs> {}

/// Trait for types with a closed zero value.
pub trait ClosedZero: Zero {}

/// Trait for types with a closed one value.
pub trait ClosedOne: One {}

/// Trait for closed Euclidean division operation
pub trait ClosedDivEuclid: Euclid {
    fn div_euclid(self, rhs: Self) -> Self;
}

/// Trait for closed Euclidean remainder operation
pub trait ClosedRemEuclid {
    fn rem_euclid(self, rhs: Self) -> Self;
}

impl<T> ClosedRemEuclid for T
where
    T: Euclid,
{
    fn rem_euclid(self, rhs: Self) -> Self {
        Euclid::rem_euclid(&self, &rhs)
    }
}

/// Represents a mathematical set as defined in Zermelo-Fraenkel set theory with Choice (ZFC).
///
/// # Formal Notation
/// - ∅: empty set
/// - ∈: element of
/// - ⊆: subset of
/// - ∪: union
/// - ∩: intersection
/// - \: set difference
/// - Δ: symmetric difference
/// - |A|: cardinality of set A
///
/// # Axioms of ZFC
/// 1. Extensionality: ∀A∀B(∀x(x ∈ A ↔ x ∈ B) → A = B)
/// 2. Empty Set: ∃A∀x(x ∉ A)
/// 3. Pairing: ∀a∀b∃A∀x(x ∈ A ↔ x = a ∨ x = b)
/// 4. Union: ∀F∃A∀x(x ∈ A ↔ ∃B(x ∈ B ∧ B ∈ F))
/// 5. Power Set: ∀A∃P∀x(x ∈ P ↔ x ⊆ A)
/// 6. Infinity: ∃A(∅ ∈ A ∧ ∀x(x ∈ A → x ∪ {x} ∈ A))
/// 7. Separation: ∀A∃B∀x(x ∈ B ↔ x ∈ A ∧ φ(x)) for any formula φ
/// 8. Replacement: ∀A(∀x∀y∀z((x ∈ A ∧ φ(x,y) ∧ φ(x,z)) → y = z) → ∃B∀y(y ∈ B ↔ ∃x(x ∈ A ∧ φ(x,y))))
/// 9. Foundation: ∀A(A ≠ ∅ → ∃x(x ∈ A ∧ x ∩ A = ∅))
/// 10. Choice: ∀A(∅ ∉ A → ∃f:A → ∪A ∀B∈A(f(B) ∈ B))
///
/// TODO(There is significant reasoning to do here about what might be covered by std traits, partial equivalence relations, etc.)
pub trait Set: Sized + Clone + PartialEq {}

/// Represents an Additive Magma, an algebraic structure with a set and a closed addition operation.
///
/// An additive magma (M, +) consists of:
/// - A set M (represented by the Set trait)
/// - A binary addition operation +: M × M → M
///
/// Formal Definition:
/// Let (M, +) be an additive magma. Then:
/// ∀ a, b ∈ M, a + b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a + b is also in M.
///
/// Note: An additive magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait AdditiveMagma: Set + ClosedAdd + ClosedAddAssign {}

/// Represents a Multiplicative Magma, an algebraic structure with a set and a closed multiplication operation.
///
/// A multiplicative magma (M, ∙) consists of:
/// - A set M (represented by the Set trait)
/// - A binary multiplication operation ∙: M ∙ M → M
///
/// Formal Definition:
/// Let (M, ∙) be a multiplicative magma. Then:
/// ∀ a, b ∈ M, a ∙ b ∈ M (closure property)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a ∙ b is also in M.
///
/// Note: A multiplicative magma does not necessarily satisfy commutativity, associativity, or have an identity element.
pub trait MultiplicativeMagma: Set + ClosedMul + ClosedMulAssign {}

/// If this trait is implemented, the object implements Additive Semigroup, an
/// algebraic structure with a set and an associative closed addition operation.
///
/// An additive semigroup (S, +) consists of:
/// - A set S
/// - A binary operation +: S × S → S that is associative
///
/// Formal Definition:
/// Let (S, +) be an additive semigroup. Then:
/// ∀ a, b, c ∈ S, (a + b) + c = a + (b + c) (associativity)
///
/// Properties:
/// - Closure: ∀ a, b ∈ S, a + b ∈ S
/// - Associativity: ∀ a, b, c ∈ S, (a + b) + c = a + (b + c)
pub trait AdditiveSemigroup: AdditiveMagma + AssociativeAddition {}

/// If this trait is implemented, the object implements a Multiplicative Semigroup, an algebraic
/// structure with a set and an associative closed multiplication operation.
///
/// A multiplicative semigroup (S, ∙) consists of:
/// - A set S
/// - A binary operation ∙: S × S → S that is associative
///
/// Formal Definition:
/// Let (S, ∙) be a multiplicative semigroup. Then:
/// ∀ a, b, c ∈ S, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
///
/// Properties:
/// - Closure: ∀ a, b ∈ S, a ∙ b ∈ S
/// - Associativity: ∀ a, b, c ∈ S, (a ∙ b) ∙ c = a ∙ (b ∙ c)
pub trait MultiplicativeSemigroup: MultiplicativeMagma + AssociativeMultiplication {}

/// Represents an Additive Monoid, an algebraic structure with a set, an associative closed addition operation, and an identity element.
///
/// An additive monoid (M, +, 0) consists of:
/// - A set M (represented by the Set trait)
/// - A binary addition operation +: M × M → M that is associative
/// - An identity element 0 ∈ M
///
/// Formal Definition:
/// Let (M, +, 0) be an additive monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a + b) + c = a + (b + c) (associativity)
/// 2. ∀ a ∈ M, a + 0 = 0 + a = a (identity)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a + b is also in M.
/// - Associativity: For all a, b, and c in M, (a + b) + c = a + (b + c).
/// - Identity: There exists an element 0 in M such that for every element a in M, a + 0 = 0 + a = a.
pub trait AdditiveMonoid: AdditiveSemigroup + ClosedZero {}

/// Represents a Multiplicative Monoid, an algebraic structure with a set, an associative closed multiplication operation, and an identity element.
///
/// A multiplicative monoid (M, ∙, 1) consists of:
/// - A set M (represented by the Set trait)
/// - A binary multiplication operation ∙: M × M → M that is associative
/// - An identity element 1 ∈ M
///
/// Formal Definition:
/// Let (M, ∙, 1) be a multiplicative monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∀ a ∈ M, a ∙ 1 = 1 ∙ a = a (identity)
///
/// Properties:
/// - Closure: For all a and b in M, the result of a ∙ b is also in M.
/// - Associativity: For all a, b, and c in M, (a ∙ b) ∙ c = a ∙ (b ∙ c).
/// - Identity: There exists an element 1 in M such that for every element a in M, a ∙ 1 = 1 ∙ a = a.
pub trait MultiplicativeMonoid: MultiplicativeSemigroup + ClosedOne {}

/// Represents an Additive Group, an algebraic structure with a set, an associative closed addition operation,
/// an identity element, and inverses for all elements.
///
/// An additive group (G, +) consists of:
/// - A set G
/// - A binary operation +: G × G → G that is associative
/// - An identity element 0 ∈ G
/// - For each a ∈ G, an inverse element -a ∈ G such that a + (-a) = (-a) + a = 0
///
/// Formal Definition:
/// Let (G, +) be an additive group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
pub trait AdditiveGroup: AdditiveMonoid + ClosedNeg + Sub + SubAssign {}

/// Represents a Multiplicative Group, an algebraic structure with a set, an associative closed multiplication operation,
/// an identity element, and inverses for all elements.
///
/// A multiplicative group (G, ∙) consists of:
/// - A set G
/// - A binary operation ∙: G × G → G that is associative
/// - An identity element 1 ∈ G
/// - For each a ∈ G, an inverse element a⁻¹ ∈ G such that a ∙ a⁻¹ = a⁻¹ ∙ a = 1
///
/// Formal Definition:
/// Let (G, ∙) be a multiplicative group. Then:
/// 1. ∀ a, b, c ∈ G, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 ∙ a = a ∙ 1 = a (identity)
/// 3. ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∙ a⁻¹ = a⁻¹ ∙ a = 1 (inverse)
pub trait MultiplicativeGroup: MultiplicativeMonoid + ClosedInv {}

/// Represents an Additive Abelian Group, an algebraic structure with a commutative addition operation.
///
/// An additive abelian group (G, +) is an additive group that also satisfies:
/// - Commutativity: ∀ a, b ∈ G, a + b = b + a
///
/// Formal Definition:
/// Let (G, +) be an additive abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
/// 4. ∀ a, b ∈ G, a + b = b + a (commutativity)
pub trait AdditiveAbelianGroup: AdditiveGroup + CommutativeAddition {}

/// Represents a Multiplicative Abelian Group, an algebraic structure with a commutative multiplication operation.
///
/// A multiplicative abelian group (G, ∙) is a multiplicative group that also satisfies:
/// - Commutativity: ∀ a, b ∈ G, a ∙ b = b ∙ a
///
/// Formal Definition:
/// Let (G, ∙) be a multiplicative abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a ∙ b) ∙ c = a ∙ (b ∙ c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 ∙ a = a ∙ 1 = a (identity)
/// 3. ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∙ a⁻¹ = a⁻¹ ∙ a = 1 (inverse)
/// 4. ∀ a, b ∈ G, a ∙ b = b ∙ a (commutativity)
pub trait MultiplicativeAbelianGroup: MultiplicativeGroup + CommutativeMultiplication {}

/// Represents a Semiring, a set with two associative binary operations (addition and multiplication).
///
/// # Formal Definition
/// A semiring (R, +, ·, 0, 1) is a set R equipped with two binary operations + and · such that:
/// - (R, +, 0) is a commutative monoid
/// - (R, ·, 1) is a monoid
/// - Multiplication distributes over addition
/// - Multiplication by 0 annihilates R
///
/// # Properties
/// - Additive closure: ∀a,b ∈ R, a + b ∈ R
/// - Multiplicative closure: ∀a,b ∈ R, a · b ∈ R
/// - Additive associativity: ∀a,b,c ∈ R, (a + b) + c = a + (b + c)
/// - Multiplicative associativity: ∀a,b,c ∈ R, (a · b) · c = a · (b · c)
/// - Additive commutativity: ∀a,b ∈ R, a + b = b + a
/// - Additive identity: ∃0 ∈ R, ∀a ∈ R, a + 0 = 0 + a = a
/// - Multiplicative identity: ∃1 ∈ R, ∀a ∈ R, 1 · a = a · 1 = a
/// - Left distributivity: ∀a,b,c ∈ R, a · (b + c) = (a · b) + (a · c)
/// - Right distributivity: ∀a,b,c ∈ R, (a + b) · c = (a · c) + (b · c)
/// - Multiplication by 0 annihilates R: ∀a ∈ R, 0 · a = a · 0 = 0
pub trait Semiring:
    AdditiveMonoid + CommutativeAddition + MultiplicativeMonoid + DistributiveAddition
{
}

impl<T> Semiring for T where
    T: AdditiveMonoid + CommutativeAddition + MultiplicativeMonoid + DistributiveAddition
{
}

/// Represents a Ring, an algebraic structure with two binary operations (addition and multiplication)
/// that satisfy certain axioms.
///
/// A ring (R, +, ·) consists of:
/// - A set R
/// - Two binary operations + (addition) and · (multiplication) on R
///
/// Formal Definition:
/// Let (R, +, ·) be a ring. Then:
/// 1. (R, +) is an abelian group:
///    a. ∀ a, b, c ∈ R, (a + b) + c = a + (b + c) (associativity)
///    b. ∀ a, b ∈ R, a + b = b + a (commutativity)
///    c. ∃ 0 ∈ R, ∀ a ∈ R, a + 0 = 0 + a = a (identity)
///    d. ∀ a ∈ R, ∃ -a ∈ R, a + (-a) = (-a) + a = 0 (inverse)
/// 2. (R, ·) is a monoid:
///    a. ∀ a, b, c ∈ R, (a · b) · c = a · (b · c) (associativity)
///    b. ∃ 1 ∈ R, ∀ a ∈ R, 1 · a = a · 1 = a (identity)
/// 3. Multiplication is distributive over addition:
///    a. ∀ a, b, c ∈ R, a · (b + c) = (a · b) + (a · c) (left distributivity)
///    b. ∀ a, b, c ∈ R, (a + b) · c = (a · c) + (b · c) (right distributivity)
pub trait Ring: AdditiveAbelianGroup + MultiplicativeMonoid + DistributiveAddition {}

/// Represents a Commutative Ring, an algebraic structure where multiplication is commutative.
///
/// A commutative ring (R, +, ·) is a ring that also satisfies:
/// - Commutativity of multiplication: ∀ a, b ∈ R, a · b = b · a
///
/// Formal Definition:
/// Let (R, +, ·) be a commutative ring. Then:
/// 1. (R, +, ·) is a ring
/// 2. ∀ a, b ∈ R, a · b = b · a (commutativity of multiplication)
pub trait CommutativeRing: Ring + CommutativeMultiplication {}

/// Represents an Integral Domain, a commutative ring with no zero divisors.
///
/// An integral domain (D, +, ·) consists of:
/// - A set D
/// - Two binary operations + (addition) and · (multiplication) on D
/// - Two distinguished elements 0 (zero) and 1 (unity) of D
///
/// Formal Definition:
/// Let (D, +, ·) be an integral domain. Then:
/// 1. (D, +, ·) is a commutative ring
/// 2. D has no zero divisors:
///    ∀ a, b ∈ D, if a · b = 0, then a = 0 or b = 0
/// 3. The zero element is distinct from the unity:
///    0 ≠ 1
pub trait IntegralDomain: Ring {}

/// Represents a Unique Factorization Domain (UFD), an integral domain where every non-zero
/// non-unit element has a unique factorization into irreducible elements.
///
/// A UFD (R, +, ·) is an integral domain that satisfies:
/// 1. Every non-zero non-unit element can be factored into irreducible elements.
/// 2. This factorization is unique up to order and associates.
///
/// Formal Definition:
/// Let R be an integral domain. R is a UFD if:
/// 1. For every non-zero non-unit a ∈ R, there exist irreducible elements p₁, ..., pₙ such that
///    a = p₁ · ... · pₙ
/// 2. If a = p₁ · ... · pₙ = q₁ · ... · qₘ are two factorizations of a into irreducible elements,
///    then n = m and there exists a bijection σ: {1, ..., n} → {1, ..., n} such that pᵢ is
///    associated to qₛᵢ for all i.
pub trait UniqueFactorizationDomain: IntegralDomain {}

/// Represents a Principal Ideal Domain (PID), an integral domain where every ideal is principal.
///
/// A Principal Ideal Domain (R, +, ·) is an integral domain that satisfies:
/// 1. (R, +, ·) is an integral domain
/// 2. Every ideal in R is principal (can be generated by a single element)
///
/// Formal Definition:
/// Let R be an integral domain. R is a PID if for every ideal I ⊆ R, there exists an element a ∈ R
/// such that I = (a) = {ra | r ∈ R}.
pub trait PrincipalIdealDomain: UniqueFactorizationDomain {}

/// Represents a Euclidean Domain, an integral domain with a Euclidean function.
///
/// A Euclidean Domain (R, +, ·, φ) is a principal ideal domain equipped with a
/// Euclidean function φ: R\{0} → ℕ₀ that satisfies certain properties.
///
/// Formal Definition:
/// Let (R, +, ·) be an integral domain and φ: R\{0} → ℕ₀ a function. R is a Euclidean domain if:
/// 1. ∀a, b ∈ R, b ≠ 0, ∃!q, r ∈ R : a = bq + r ∧ (r = 0 ∨ φ(r) < φ(b)) (Division with Remainder)
/// 2. ∀a, b ∈ R\{0} : φ(a) ≤ φ(ab) (Multiplicative Property)
pub trait EuclideanDomain: PrincipalIdealDomain + Euclid {}

/// Represents a Field, an algebraic structure that is a Euclidean domain where every non-zero element
/// has a multiplicative inverse.
///
/// A field (F, +, ·) consists of:
/// - A set F
/// - Two binary operations + (addition) and · (multiplication) on F
///
/// Formal Definition:
/// Let (F, +, ·) be a field. Then:
/// 1. (F, +, ·) is a Euclidean domain
/// 2. Every non-zero element has a multiplicative inverse
/// 3. 0 ≠ 1 (the additive identity is not equal to the multiplicative identity)
pub trait Field: EuclideanDomain + ClosedDiv + ClosedDivAssign {}

/// Represents a Finite Prime Field, a field with a finite number of elements where the number of elements is prime.
///
/// A finite prime field ℤ/pℤ (also denoted as 𝔽_p or GF(p)) consists of:
/// - A set of p elements {0, 1, 2, ..., p-1}, where p is prime
/// - Addition and multiplication operations modulo p
///
/// Formal Definition:
/// Let p be a prime number. Then:
/// 1. The set is {0, 1, 2, ..., p-1}
/// 2. Addition: a +_p b = (a + b) mod p
/// 3. Multiplication: a ·_p b = (a · b) mod p
/// 4. The additive identity is 0
/// 5. The multiplicative identity is 1
/// 6. Every non-zero element has a unique multiplicative inverse
pub trait FiniteField: Field {
    // Returns the characteristic of the field.
    ///
    /// # Formal Notation
    /// The smallest positive integer n such that n · 1 = 0, where 1 is the multiplicative identity
    fn characteristic() -> u64;

    /// Returns the order (number of elements) of the finite field.
    ///
    /// # Formal Notation
    /// |F| = p^n, where p is the characteristic of F and n is its degree over the prime subfield
    fn order() -> u64;
}

/// Represents a Real Field, an ordered field that satisfies the completeness axiom.
///
/// A real field (F, +, ·, ≤) consists of:
/// - A set F
/// - Two binary operations + (addition) and · (multiplication)
/// - A total order relation ≤
///
/// Formal Definition:
/// 1. (F, +, ·) is a field
/// 2. (F, ≤) is a totally ordered set
/// 3. The order is compatible with field operations
/// 4. F satisfies the completeness axiom
/// 5. Dedekind-complete: Every non-empty subset of ℝ with an upper bound has a least upper bound in ℝ
pub trait RealField: Field + PartialOrd {}

/// Represents a Polynomial over a field.
///
/// # Formal Definition
/// A polynomial over a field F is an expression of the form:
/// a_n * X^n + a_{n-1} * X^{n-1} + ... + a_1 * X + a_0
/// where a_i ∈ F are called the coefficients, and X is called the indeterminate.
pub trait Polynomial: Clone + PartialEq + ClosedAdd + ClosedMul + Euclid {}

/// Represents a Module over a ring.
///
/// # Formal Definition
/// A module M over a ring R is an abelian group (M, +) equipped with a scalar multiplication
/// by elements of R, satisfying certain axioms.
///
/// # Properties
/// - (M, +) is an abelian group
/// - Scalar multiplication: R × M → M where a, b ∈ R and x, y ∈ M satisfying:
///   1. a(x + y) = ax + ay
///   2. (a + b)x = ax + bx
///   3. (ab)x = a(bx)
///   4. 1x = x
pub trait Module: MultiplicativeAbelianGroup {
    type Scalar: Ring;
}

/// Represents a Vector Space over a field.
///
/// # Formal Definition
/// A vector space V over a field F is an abelian group (V, +) equipped with scalar multiplication
/// by elements of F, satisfying certain axioms.
///
/// # Properties
/// - (V, +) is an abelian group
/// - Scalar multiplication: F × V → V where a, b ∈ F and u, v ∈ V satisfying:
///   1. a(u + v) = au + av
///   2. (a + b)v = av + bv
///   3. (ab)v = a(bv)
///   4. 1v = v
pub trait VectorSpace: AdditiveAbelianGroup {
    type Scalar: Field;
}

/// Represents a Field Extension.
///
/// # Formal Definition
/// A field extension L/K is a field L that contains K as a subfield.
///
/// # Properties
/// - L is a field
/// - K is a subfield of L
/// - L is a vector space over K
pub trait FieldExtension: Field + VectorSpace<Scalar = Self::BaseField> {
    type BaseField: Field;
}

/// Represents a Tower of Field Extensions.
///
/// # Formal Definition
/// A tower of field extensions is a sequence of fields K = F₀ ⊂ F₁ ⊂ ... ⊂ Fₙ = L
/// where each Fᵢ₊₁/Fᵢ is a field extension.
///
/// # Properties
/// - Each level is a field extension of the previous level
/// - The composition of the extensions forms the overall extension L/K
/// - The degree of L/K is the product of the degrees of each extension in the tower
pub trait FieldExtensionTower: FieldExtension {}

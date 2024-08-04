/* trunk-ignore-all(rustfmt) */
use num_traits::{Euclid, Inv, One, Zero};
use std::hash::Hash;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};
use std::collections::{HashMap};

// A note on the reasons why certain traits are used:
//
// The `Inv` trait is the multiplicative inverse operation.
// The `One` trait is the multiplicative identity operation.
// The `Zero` trait is the additive identity operation.
// The `Neg` trait is the additive inverse operation.

// TODO(These marker traits could actually mean something and check things)

// Marker traits for algebraic properties

/// Marker trait for commutative addition: a + b = b + a
pub trait CommutativeAddition {}

/// Marker trait for commutative multiplication: a * b = b * a
pub trait CommutativeMultiplication {}

/// Marker trait for associative addition: (a + b) + c = a + (b + c)
pub trait AssociativeAddition {}

/// Marker trait for associative multiplication: (a * b) * c = a * (b * c)
pub trait AssociativeMultiplication {}

/// Marker trait for distributive multiplication over addition: a * (b + c) = (a * b) + (a * c)
pub trait Distributive {}

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
pub trait Set: Sized + Clone + PartialEq {}

/// Represents an Additive Magma, an algebraic structure with a set and a closed addition operation.
///
/// # Mathematical Definition
/// An additive magma (M, +) consists of:
/// - A set M
/// - A binary operation +: M × M → M
///
/// # Formal Definition
/// Let (M, +) be an additive magma. Then:
/// ∀ a, b ∈ M, a + b ∈ M (closure property)
///
/// # Properties
/// - Closure: For all a and b in M, the result of a + b is also in M.
pub trait AdditiveMagma: Set + ClosedAdd + ClosedAddAssign {}

/// Represents a Multiplicative Magma, an algebraic structure with a set and a closed multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative magma (M, *) consists of:
/// - A set M
/// - A binary operation *: M × M → M
///
/// # Formal Definition
/// Let (M, *) be a multiplicative magma. Then:
/// ∀ a, b ∈ M, a * b ∈ M (closure property)
///
/// # Properties
/// - Closure: For all a and b in M, the result of a * b is also in M.
pub trait MultiplicativeMagma: Set + ClosedMul + ClosedMulAssign {}

/// Represents an Additive Semigroup, an algebraic structure with an associative addition operation.
///
/// # Mathematical Definition
/// An additive semigroup (S, +) is an additive magma where:
/// - The operation + is associative
///
/// # Formal Definition
/// Let (S, +) be an additive semigroup. Then:
/// ∀ a, b, c ∈ S, (a + b) + c = a + (b + c) (associativity)
///
/// # Properties
/// - Associativity: For all a, b, and c in S, (a + b) + c = a + (b + c)
pub trait AdditiveSemigroup: AdditiveMagma + AssociativeAddition {}

/// Represents a Multiplicative Semigroup, an algebraic structure with an associative multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative semigroup (S, *) is a multiplicative magma where:
/// - The operation * is associative
///
/// # Formal Definition
/// Let (S, *) be a multiplicative semigroup. Then:
/// ∀ a, b, c ∈ S, (a * b) * c = a * (b * c) (associativity)
///
/// # Properties
/// - Associativity: For all a, b, and c in S, (a * b) * c = a * (b * c)
pub trait MultiplicativeSemigroup: MultiplicativeMagma + AssociativeMultiplication {}

/// Represents an Additive Monoid, an algebraic structure with an associative addition operation and an identity element.
///
/// # Mathematical Definition
/// An additive monoid (M, +, 0) is an additive semigroup with:
/// - An identity element 0 ∈ M
///
/// # Formal Definition
/// Let (M, +, 0) be an additive monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a + b) + c = a + (b + c) (associativity)
/// 2. ∀ a ∈ M, a + 0 = 0 + a = a (identity)
///
/// # Properties
/// - Identity: There exists an element 0 in M such that for every element a in M, a + 0 = 0 + a = a
pub trait AdditiveMonoid: AdditiveSemigroup + ClosedZero {}

/// Represents a Multiplicative Monoid, an algebraic structure with an associative multiplication operation and an identity element.
///
/// # Mathematical Definition
/// A multiplicative monoid (M, *, 1) is a multiplicative semigroup with:
/// - An identity element 1 ∈ M
///
/// # Formal Definition
/// Let (M, *, 1) be a multiplicative monoid. Then:
/// 1. ∀ a, b, c ∈ M, (a * b) * c = a * (b * c) (associativity)
/// 2. ∀ a ∈ M, a * 1 = 1 * a = a (identity)
///
/// # Properties
/// - Identity: There exists an element 1 in M such that for every element a in M, a * 1 = 1 * a = a
pub trait MultiplicativeMonoid: MultiplicativeSemigroup + ClosedOne {}

/// Represents an Additive Group, an algebraic structure with an associative addition operation, an identity element, and inverses.
///
/// # Mathematical Definition
/// An additive group (G, +, 0) is an additive monoid where:
/// - Every element has an additive inverse
///
/// # Formal Definition
/// Let (G, +, 0) be an additive group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
///
/// # Properties
/// - Inverse: For every element a in G, there exists an element -a in G such that a + (-a) = (-a) + a = 0
pub trait AdditiveGroup: AdditiveMonoid + ClosedNeg + ClosedSub + ClosedSubAssign {}

/// Represents a Multiplicative Group, an algebraic structure with an associative multiplication operation, an identity element, and inverses.
///
/// # Mathematical Definition
/// A multiplicative group (G, *, 1) is a multiplicative monoid where:
/// - Every non-zero element has a multiplicative inverse
///
/// # Formal Definition
/// Let (G, *, 1) be a multiplicative group. Then:
/// 1. ∀ a, b, c ∈ G, (a * b) * c = a * (b * c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 * a = a * 1 = a (identity)
/// 3. ∀ a ∈ G, a ≠ 0, ∃ a^(-1) ∈ G, a * a^(-1) = a^(-1) * a = 1 (inverse)
///
/// # Properties
/// - Inverse: For every non-zero element a in G, there exists an element a^(-1) in G such that a * a^(-1) = a^(-1) * a = 1
pub trait MultiplicativeGroup:
    MultiplicativeMonoid + ClosedInv + ClosedDiv + ClosedDivAssign
{
}

/// Represents an Additive Abelian Group, an algebraic structure with a commutative addition operation.
///
/// # Mathematical Definition
/// An additive abelian group is an additive group where:
/// - The addition operation is commutative
///
/// # Formal Definition
/// Let (G, +, 0) be an additive abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a + b) + c = a + (b + c) (associativity)
/// 2. ∃ 0 ∈ G, ∀ a ∈ G, 0 + a = a + 0 = a (identity)
/// 3. ∀ a ∈ G, ∃ -a ∈ G, a + (-a) = (-a) + a = 0 (inverse)
/// 4. ∀ a, b ∈ G, a + b = b + a (commutativity)
///
/// # Properties
/// - Commutativity: For all a and b in G, a + b = b + a
pub trait AdditiveAbelianGroup: AdditiveGroup + CommutativeAddition {}

/// Represents a Multiplicative Abelian Group, an algebraic structure with a commutative multiplication operation.
///
/// # Mathematical Definition
/// A multiplicative abelian group is a multiplicative group where:
/// - The multiplication operation is commutative
///
/// # Formal Definition
/// Let (G, *, 1) be a multiplicative abelian group. Then:
/// 1. ∀ a, b, c ∈ G, (a * b) * c = a * (b * c) (associativity)
/// 2. ∃ 1 ∈ G, ∀ a ∈ G, 1 * a = a * 1 = a (identity)
/// 3. ∀ a ∈ G, a ≠ 0, ∃ a^(-1) ∈ G, a * a^(-1) = a^(-1) * a = 1 (inverse)
/// 4. ∀ a, b ∈ G, a * b = b * a (commutativity)
///
/// # Properties
/// - Commutativity: For all a and b in G, a * b = b * a
pub trait MultiplicativeAbelianGroup: MultiplicativeGroup + CommutativeMultiplication {}

/// Represents a Ring, an algebraic structure with two binary operations (addition and multiplication) that satisfy certain axioms.
///
/// # Mathematical Definition
/// A ring (R, +, ·) consists of:
/// - A set R
/// - Two binary operations + (addition) and · (multiplication) on R
///
/// # Formal Definition
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
pub trait Ring: AdditiveAbelianGroup + MultiplicativeMonoid + Distributive {}

/// Represents a Commutative Ring, an algebraic structure where multiplication is commutative.
///
/// # Mathematical Definition
/// A commutative ring (R, +, ·) is a ring where:
/// - The multiplication operation is commutative
///
/// # Formal Definition
/// Let (R, +, ·) be a commutative ring. Then:
/// 1. (R, +, ·) is a ring
/// 2. ∀ a, b ∈ R, a · b = b · a (commutativity of multiplication)
pub trait CommutativeRing: Ring + CommutativeMultiplication {}


/// Represents an Integral Domain, a commutative ring with no zero divisors.
///
/// # Mathematical Definition
/// An integral domain (D, +, ·) is a commutative ring where:
/// - The ring has no zero divisors
///
/// # Formal Definition
/// Let (D, +, ·) be an integral domain. Then:
/// 1. (D, +, ·) is a commutative ring
/// 2. D has no zero divisors:
///    ∀ a, b ∈ D, if a · b = 0, then a = 0 or b = 0
/// 3. The zero element is distinct from the unity:
///    0 ≠ 1
pub trait IntegralDomain: CommutativeRing {

    /// Checks if element is a zero divisor
    fn is_zero_divisor(&self) -> bool{
        self.is_zero()
    }
    /// Checks if element divides other elements
    fn divides(&self, other: &Self) -> bool{
        if self.is_zero(){
            other.is_zero()
        } else {
            let mut c = self.clone();
            while c * self != *other {
                c = c + Self::one();
                if c.is_zero(){
                    return false;
                }
            } true 
        }
    }
    /// Checks if element has a multiple inverse
    fn is_unit(&self)->bool{
        !self.is_zero() && self.divides(&Self::one())
    }
    ///Calculates the greatest common divisor
    fn gcd(&self, other: &Self) -> Self { //recommend defining a seperate trait for gcd to handle large numbers https://en.algorithmica.org/hpc/algorithms/gcd/
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let t = b.clone();
            b = a % b;
            a = t;
        }
        a
    }

    /// Calculates the least common multiple 
    fn lcm(&self, other: &Self) -> Self {
        if self.is_zero() && other.is_zero() {
            Self::zero()
        } else {
            (self * other) / self.gcd(other)
        }
    }

    /// Checks if two elements are associates (differ by a unit factor).
    fn are_associates(&self, other: &Self) -> bool {
        !self.is_zero() && !other.is_zero() && (self.divides(other) && other.divides(self))
    }

    /// Checks if the element is irreducible.
    fn is_irreducible(&self) -> bool {
        if self.is_unit() || self.is_zero() {
            false
        } else {
            for a in self.non_trivial_divisors() {
                if !a.is_unit() && !self.div_by(&a).is_unit() {
                    return false;
                }
            }
            true
        }
    }

    /// Returns an iterator over the non-trivial divisors of the element.
    fn non_trivial_divisors(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((Self::one()..=self.clone())
            .filter(move |x| self.divides(x) && !x.is_one() && x != self))
    }

    /// Performs division by another element, returning None if not exactly divisible.
    fn div_by(&self, other: &Self) -> Option<Self> {
        if other.is_zero() {
            None
        } else {
            let mut q = Self::zero();
            let mut r = self.clone();
            while r >= *other {
                r = r - other.clone();
                q = q + Self::one();
            }
            if r.is_zero() {
                Some(q)
            } else {
                None
            }
        }
    }

    
//TODO - tests?
} 

/// Represents a Unique Factorization Domain (UFD), an integral domain where every non-zero
/// non-unit element has a unique factorization into irreducible elements.
///
/// # Mathematical Definition
/// A UFD (R, +, ·) is an integral domain that satisfies:
/// 1. Every non-zero non-unit element can be factored into irreducible elements.
/// 2. This factorization is unique up to order and associates.
///
/// # Formal Definition
/// Let R be an integral domain. R is a UFD if:
/// 1. For every non-zero non-unit a ∈ R, there exist irreducible elements p₁, ..., pₙ such that
///    a = p₁ · ... · pₙ
/// 2. If a = p₁ · ... · pₙ = q₁ · ... · qₘ are two factorizations of a into irreducible elements,
///    then n = m and there exists a bijection σ: {1, ..., n} → {1, ..., n} such that pᵢ is
///    associated to qₛᵢ for all i.
pub trait UniqueFactorizationDomain: IntegralDomain { //simple 

    fn is_prime(&self) -> bool {
        self.is_irreducible()
    }

    ///Factoring element to its primes 
    fn factor(&self) -> Option<HashMap<Self,usize>>{
        if self.is_zero() || self.is_unit(){
            return None;

        }

        let mut factors = HashMap::new();
        let mut remainder = self.clone();

        for p in self.potential_prime_factors(){
            let mut exponent = 0;
            while let Some(q) = remainder.div_by(&p){
                exponent += 1;
                remainder = q;
            }
            if exponent > 0 {
                factors.insert(p, exponent);

            }
            if remainder.is_unit(){
                break;
            }
        }

        if factors.is_empty(){
            factors.insert(self.clone(),1);
        }
    Some(factors) }

        fn potential_prime_factors(&self) -> Box<dyn Iterator<Item = Self>>{
            Box::new(self.non_trivial_divisors().filter(|x|x.is_prime()))
        }
        fn has_unique_factorization(&self) -> bool {
            !self.is_zero() && !self.is_unit()
        }




}


/// Represents a Principal Ideal Domain (PID), an integral domain where every ideal is principal.
///
/// # Mathematical Definition
/// A Principal Ideal Domain (R, +, ·) is an integral domain where:
/// - Every ideal in R is principal (can be generated by a single element)
///
/// # Formal Definition
/// Let R be an integral domain. R is a PID if for every ideal I ⊆ R, there exists an element a ∈ R
/// such that I = (a) = {ra | r ∈ R}.
pub trait PrincipalIdealDomain: UniqueFactorizationDomain {}

/// Represents a Euclidean Domain, an integral domain with a Euclidean function.
///
/// # Mathematical Definition
/// A Euclidean Domain (R, +, ·, φ) is a principal ideal domain equipped with a
/// Euclidean function φ: R\{0} → ℕ₀ that satisfies certain properties.
///
/// # Formal Definition
/// Let (R, +, ·) be an integral domain and φ: R\{0} → ℕ₀ a function. R is a Euclidean domain if:
/// 1. ∀a, b ∈ R, b ≠ 0, ∃!q, r ∈ R : a = bq + r ∧ (r = 0 ∨ φ(r) < φ(b)) (Division with Remainder)
/// 2. ∀a, b ∈ R\{0} : φ(a) ≤ φ(ab) (Multiplicative Property)
pub trait EuclideanDomain: PrincipalIdealDomain + Euclid {}

/// Represents a Field, a commutative ring where every non-zero element has a multiplicative inverse.
///
/// # Mathematical Definition
/// A field (F, +, ·) is a commutative ring where:
/// - Every non-zero element has a multiplicative inverse
///
/// # Formal Definition
/// Let (F, +, ·) be a field. Then:
/// 1. (F, +, ·) is a commutative ring
/// 2. ∀ a ∈ F, a ≠ 0, ∃ a⁻¹ ∈ F, a · a⁻¹ = a⁻¹ · a = 1 (multiplicative inverse)
pub trait Field: EuclideanDomain + MultiplicativeAbelianGroup {}

/// Represents a Finite Field, a field with a finite number of elements.
///
/// # Mathematical Definition
/// A finite field is a field with a finite number of elements.
///
/// # Properties
/// - The number of elements is always a prime power p^n
pub trait FiniteField: Field {
    /// Returns the characteristic of the field.
    fn characteristic() -> u64;

    /// Returns the number of elements in the field.
    fn order() -> u64;
}

/// Represents an Ordered Field, a field with a total order compatible with its operations.
///
/// # Mathematical Definition
/// An ordered field is a field equipped with a total order ≤ where:
/// - If a ≤ b then a + c ≤ b + c for all c
/// - If 0 ≤ a and 0 ≤ b then 0 ≤ a · b
pub trait OrderedField: Field + PartialOrd {}

/// Represents a Real Field, a complete ordered field.
///
/// # Mathematical Definition
/// A real field is an ordered field that is Dedekind-complete:
/// - Every non-empty subset with an upper bound has a least upper bound
pub trait RealField: OrderedField {}

/// Represents a Polynomial over a field.
///
/// # Mathematical Definition
/// A polynomial over a field F is an expression of the form:
/// a_n * X^n + a_{n-1} * X^{n-1} + ... + a_1 * X + a_0
/// where a_i ∈ F are called the coefficients, and X is the indeterminate.
pub trait Polynomial: Clone + PartialEq + ClosedAdd + ClosedMul + Euclid {
    /// The type of the coefficients of the polynomial.
    type Coefficient: Ring;

    /// Returns the degree of the polynomial.
    fn degree(&self) -> usize;

    /// Gets the coefficient of the term with the given degree.
    fn coefficient(&self, degree: usize) -> Self::Coefficient;
}

/// Represents a Vector Space over a field.
///
/// # Mathematical Definition
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
    /// The scalar field over which this vector space is defined.
    type Scalar: Field;

    /// Performs scalar multiplication.
    fn scale(&self, scalar: &Self::Scalar) -> Self;

    /// Returns the dimension of the vector space, if it's finite-dimensional.
    fn dimension(&self) -> Option<usize>;
}

/// Represents a Field Extension.
///
/// # Mathematical Definition
/// A field extension L/K is a field L that contains K as a subfield.
///
/// # Properties
/// - L is a field
/// - K is a subfield of L
/// - L is a vector space over K
pub trait FieldExtension: Field + VectorSpace<Scalar = Self::BaseField> {
    /// The base field of this extension.
    type BaseField: Field;

    /// Returns the degree of the field extension.
    fn degree() -> usize;

    /// Computes the trace of an element.
    fn trace(&self) -> Self::BaseField;

    /// Computes the norm of an element.
    fn norm(&self) -> Self::BaseField;
}

/// Represents a Tower of Field Extensions.
///
/// # Mathematical Definition
/// A tower of field extensions is a sequence of fields K = F₀ ⊂ F₁ ⊂ ... ⊂ Fₙ = L
/// where each Fᵢ₊₁/Fᵢ is a field extension.
///
/// # Properties
/// - Each level is a field extension of the previous level
/// - The composition of the extensions forms the overall extension L/K
/// - The degree of L/K is the product of the degrees of each extension in the tower
pub trait FieldExtensionTower: FieldExtension {
    /// Returns the number of extensions in the tower.
    fn tower_height() -> usize;

    /// Returns the degree of the i-th extension in the tower.
    fn extension_degree(i: usize) -> usize;
}

// Blanket implementations for basic operation traits
impl<T: Add<Output = T>> ClosedAdd for T {}
impl<T: for<'a> Add<&'a T, Output = T>> ClosedAddRef for T {}
impl<T: Sub<Output = T>> ClosedSub for T {}
impl<T: for<'a> Sub<&'a T, Output = T>> ClosedSubRef for T {}
impl<T: Mul<Output = T>> ClosedMul for T {}
impl<T: for<'a> Mul<&'a T, Output = T>> ClosedMulRef for T {}
impl<T: Div<Output = T>> ClosedDiv for T {}
impl<T: for<'a> Div<&'a T, Output = T>> ClosedDivRef for T {}
impl<T: Rem<Output = T>> ClosedRem for T {}
impl<T: for<'a> Rem<&'a T, Output = T>> ClosedRemRef for T {}
impl<T: Neg<Output = T>> ClosedNeg for T {}
impl<T: Inv<Output = T>> ClosedInv for T {}

// Blanket implementations for assignment operation traits
impl<T: AddAssign> ClosedAddAssign for T {}
impl<T: for<'a> AddAssign<&'a T>> ClosedAddAssignRef for T {}
impl<T: SubAssign> ClosedSubAssign for T {}
impl<T: for<'a> SubAssign<&'a T>> ClosedSubAssignRef for T {}
impl<T: MulAssign> ClosedMulAssign for T {}
impl<T: for<'a> MulAssign<&'a T>> ClosedMulAssignRef for T {}
impl<T: DivAssign> ClosedDivAssign for T {}
impl<T: for<'a> DivAssign<&'a T>> ClosedDivAssignRef for T {}
impl<T: RemAssign> ClosedRemAssign for T {}
impl<T: for<'a> RemAssign<&'a T>> ClosedRemAssignRef for T {}

// Blanket implementations for zero and one
impl<T: Zero> ClosedZero for T {}
impl<T: One> ClosedOne for T {}

// Set
impl<T: Clone + PartialEq> Set for T {}

// AdditiveMagma
impl<T: Set + ClosedAdd + ClosedAddAssign> AdditiveMagma for T {}

// MultiplicativeMagma
impl<T: Set + ClosedMul + ClosedMulAssign> MultiplicativeMagma for T {}

// AdditiveSemigroup
impl<T: AdditiveMagma + AssociativeAddition> AdditiveSemigroup for T {}

// MultiplicativeSemigroup
impl<T: MultiplicativeMagma + AssociativeMultiplication> MultiplicativeSemigroup for T {}

// AdditiveMonoid
impl<T: AdditiveSemigroup + ClosedZero> AdditiveMonoid for T {}

// MultiplicativeMonoid
impl<T: MultiplicativeSemigroup + ClosedOne> MultiplicativeMonoid for T {}

// AdditiveGroup
impl<T: AdditiveMonoid + ClosedNeg + ClosedSub + ClosedSubAssign> AdditiveGroup for T {}

// MultiplicativeGroup
impl<T: MultiplicativeMonoid + ClosedInv + ClosedDiv + ClosedDivAssign> MultiplicativeGroup for T {}

// AdditiveAbelianGroup
impl<T: AdditiveGroup + CommutativeAddition> AdditiveAbelianGroup for T {}

// MultiplicativeAbelianGroup
impl<T: MultiplicativeGroup + CommutativeMultiplication> MultiplicativeAbelianGroup for T {}

// Ring
impl<T: AdditiveAbelianGroup + MultiplicativeMonoid + Distributive> Ring for T {}

// CommutativeRing
impl<T: Ring + CommutativeMultiplication> CommutativeRing for T {}

// IntegralDomain 
//added implementation which checks for zero divisors 

impl<T: CommutativeRing> IntegralDomain for T {}

// UniqueFactorizationDomain
impl<T: IntegralDomain> UniqueFactorizationDomain for T {}

// PrincipalIdealDomain
impl<T: UniqueFactorizationDomain> PrincipalIdealDomain for T {}

// EuclideanDomain
impl<T: PrincipalIdealDomain + Euclid> EuclideanDomain for T {}

// Field
impl<T: EuclideanDomain + MultiplicativeAbelianGroup> Field for T {}

// FiniteField
// Note: This cannot be implemented as a blanket impl because it requires specific knowledge about the field's finiteness

// OrderedField
impl<T: Field + PartialOrd> OrderedField for T {}

// RealField
// Note: This cannot be implemented as a blanket impl because it requires knowledge about completeness

// Polynomial
// Note: This cannot be implemented as a blanket impl because it requires specific polynomial representation

// VectorSpace
// Note: This cannot be implemented as a blanket impl because it requires specific vector space structure

// FieldExtension
// Note: This cannot be implemented as a blanket impl because it requires specific knowledge about the base field and extension structure

// FieldExtensionTower
// Note: This cannot be implemented as a blanket impl because it requires specific knowledge about the tower structure

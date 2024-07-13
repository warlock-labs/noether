use crate::Field;

/// Represents a field extension.
///
/// Let K and L be fields. A field extension L/K is defined as:
/// - K is a subfield of L
/// - The operations of L, when restricted to K, are the same as the operations of K
/// - L is a vector space over K
///
/// Notation:
/// - K: base field
/// - L: extension field
/// - [L:K]: degree of the extension
pub trait FieldExtension: Field {
    /// The base field of the extension.
    /// Mathematically, this is K in the extension L/K.
    type BaseField: Field;

    /// Returns the degree of the field extension.
    /// Mathematically, this is [L:K], the dimension of L as a vector space over K.
    /// For infinite extensions, this returns None.
    ///
    /// [L:K] = dim_K(L)
    fn degree() -> Option<usize>;

    /// Embeds an element from the base field into the extension field.
    /// This represents the natural inclusion map i: K → L.
    ///
    /// ∀ k ∈ K, i(k) ∈ L
    fn embed(element: Self::BaseField) -> Self;

    /// Attempts to represent an element of the extension field as an element of the base field.
    /// This is the inverse of the embed function, where possible.
    /// Returns None if the element is not in the image of K in L.
    ///
    /// For l ∈ L, if ∃ k ∈ K such that i(k) = l, return Some(k), else None
    fn project(&self) -> Option<Self::BaseField>;

    /// Returns a basis of the extension field as a vector space over the base field.
    /// For a finite extension of degree n, this returns {v₁, ..., vₙ} where:
    /// ∀ l ∈ L, ∃ unique k₁, ..., kₙ ∈ K such that l = k₁v₁ + ... + kₙvₙ
    ///
    /// For infinite extensions, this returns an infinite iterator.
    fn basis() -> Box<dyn Iterator<Item = Self>>;

    /// Expresses an element of the extension field as a linear combination of basis elements.
    /// For l ∈ L, returns [k₁, ..., kₙ] ∈ K^n such that l = k₁v₁ + ... + kₙvₙ
    /// where {v₁, ..., vₙ} is the basis of L over K.
    fn decompose(&self) -> Vec<Self::BaseField>;

    /// Constructs an element of the extension field from its decomposition in terms of the basis.
    /// Given [k₁, ..., kₙ] ∈ K^n, returns k₁v₁ + ... + kₙvₙ ∈ L
    /// where {v₁, ..., vₙ} is the basis of L over K.
    fn compose(coefficients: &[Self::BaseField]) -> Self;

    /// Returns the minimal polynomial of the extension over the base field.
    /// For a simple algebraic extension L = K(α), this is the monic irreducible polynomial
    /// p(X) ∈ K[X] such that p(α) = 0.
    ///
    /// The coefficients are given in ascending order of degree:
    /// [a₀, a₁, ..., aₙ] represents p(X) = a₀ + a₁X + ... + aₙX^n
    fn minimal_polynomial() -> Vec<Self::BaseField>;

    /// Checks if this extension is normal.
    /// A field extension L/K is normal if L is the splitting field of a polynomial over K.
    ///
    /// ∃ p(X) ∈ K[X] such that L = K(α₁, ..., αₙ) where α₁, ..., αₙ are all roots of p(X)
    fn is_normal() -> bool;

    /// Checks if this extension is separable.
    /// A field extension L/K is separable if the minimal polynomial of every element of L over K
    /// is separable (has no repeated roots in its splitting field).
    ///
    /// ∀ α ∈ L, the minimal polynomial of α over K has distinct roots in its splitting field
    fn is_separable() -> bool;

    /// Checks if this extension is algebraic.
    /// A field extension L/K is algebraic if every element of L is algebraic over K.
    ///
    /// ∀ α ∈ L, ∃ non-zero p(X) ∈ K[X] such that p(α) = 0
    fn is_algebraic() -> bool;

    /// Checks if the field extension axioms hold.
    /// This method would implement checks for the field extension properties.
    /// The exact checks would depend on whether the extension is finite or infinite,
    /// and might be computationally infeasible for some extensions.
    fn check_field_extension_axioms() -> bool;
}

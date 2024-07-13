use crate::field_extension::FieldExtension;

/// Represents a tower of field extensions.
///
/// For a tower of fields F₀ ⊆ F₁ ⊆ F₂ ⊆ ... ⊆ Fₙ,
/// where each Fᵢ₊₁ is an extension field of Fᵢ for i = 0, 1, ..., n-1.
pub trait FieldExtensionTower: FieldExtension {
    /// The type representing each level in the tower.
    type Level: FieldExtension;

    /// Returns the number of extensions in the tower.
    /// For an infinite tower, this returns None.
    fn height() -> Option<usize>;

    /// Returns the base field of the entire tower (F₀).
    fn base_field() -> Self::BaseField;

    /// Returns the top field of the tower (Fₙ).
    fn top_field() -> Self::Level;

    /// Returns an iterator over all fields in the tower, from bottom to top.
    /// Yields F₀, F₁, F₂, ..., Fₙ in order.
    fn fields() -> Box<dyn Iterator<Item = Self::Level>>;

    /// Returns the field at a specific level in the tower.
    /// Level 0 is the base field, level height()-1 is the top field.
    fn field_at_level(level: usize) -> Option<Self::Level>;

    /// Returns an iterator over the degrees of each extension in the tower.
    /// Yields [F₁:F₀], [F₂:F₁], ..., [Fₙ:Fₙ₋₁].
    fn extension_degrees() -> Box<dyn Iterator<Item = Option<usize>>>;

    /// Computes the absolute degree of the entire tower extension.
    /// [Fₙ:F₀] = [Fₙ:Fₙ₋₁] · [Fₙ₋₁:Fₙ₋₂] · ... · [F₂:F₁] · [F₁:F₀]
    fn absolute_degree(&self) -> Option<usize> {
        Self::extension_degrees().fold(Some(1), |acc, deg| acc.and_then(|a| deg.map(|d| a * d)))
    }

    /// Returns an iterator over the minimal polynomials of each extension in the tower.
    /// Each minimal polynomial is represented as a vector of coefficients in ascending order of degree.
    fn minimal_polynomials() -> Box<dyn Iterator<Item = Vec<Self::BaseField>>>;

    /// Embeds an element from any field in the tower into the top field.
    fn embed_to_top(element: &Self::Level, from_level: usize) -> Self::Level;

    /// Attempts to project an element from the top field to a lower level in the tower.
    /// Returns None if the element cannot be represented in the lower field.
    fn project_from_top(element: &Self::Level, to_level: usize) -> Option<Self::Level>;

    /// Checks if the entire tower consists of normal extensions.
    fn is_normal(&self) -> bool;

    /// Checks if the entire tower consists of separable extensions.
    fn is_separable(&self) -> bool;

    /// Checks if the entire tower consists of algebraic extensions.
    fn is_algebraic(&self) -> bool;

    /// Checks if the tower is Galois (normal and separable).
    fn is_galois(&self) -> bool {
        self.is_normal() && self.is_separable()
    }

    /// Computes the compositum of this tower with another tower over the same base field.
    /// Returns a new tower representing the smallest field containing both towers.
    fn compositum(other: &Self) -> Self;

    /// Attempts to find an isomorphic simple extension for this tower.
    /// Returns None if no such simple extension exists or cannot be computed.
    fn to_simple_extension() -> Option<Self::Level>;

    /// Checks if this tower is a refinement of another tower.
    /// A refinement means this tower includes all the fields of the other tower, possibly with additional fields in between.
    fn is_refinement_of(other: &Self) -> bool;

    /// Returns an iterator over all intermediate fields between the base and top fields.
    /// This can be an exponentially large set for some towers.
    fn intermediate_fields() -> Box<dyn Iterator<Item = Self::Level>>;

    /// Checks if the tower satisfies the axioms for a valid field extension tower.
    fn check_tower_axioms() -> bool {
        // Implementation would check:
        // 1. Each level is a valid field extension of the previous level
        // 2. The tower is properly nested (each field is a subfield of the next)
        // 3. Degree multiplicativity holds
        // 4. Other consistency checks
        unimplemented!("Axiom checking not implemented")
    }
}

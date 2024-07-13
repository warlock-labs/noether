use std::fmt::Debug;

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
pub trait Set: Sized + Clone + PartialEq + Debug {
    type Element;

    /// Returns true if the set is empty (∅).
    /// ∀x(x ∉ self)
    fn is_empty(&self) -> bool;

    /// Checks if the given element is a member of the set.
    /// element ∈ self
    fn contains(&self, element: &Self::Element) -> bool;

    /// Creates an empty set (∅).
    /// ∃A∀x(x ∉ A)
    fn empty() -> Self;

    /// Creates a singleton set containing the given element.
    /// ∃A∀x(x ∈ A ↔ x = element)
    fn singleton(element: Self::Element) -> Self;

    /// Returns the union of this set with another set.
    /// ∀x(x ∈ result ↔ x ∈ self ∨ x ∈ other)
    fn union(&self, other: &Self) -> Self;

    /// Returns the intersection of this set with another set.
    /// ∀x(x ∈ result ↔ x ∈ self ∧ x ∈ other)
    fn intersection(&self, other: &Self) -> Self;

    /// Returns the difference of this set and another set (self - other).
    /// ∀x(x ∈ result ↔ x ∈ self ∧ x ∉ other)
    fn difference(&self, other: &Self) -> Self;

    /// Returns the symmetric difference of this set and another set.
    /// ∀x(x ∈ result ↔ (x ∈ self ∧ x ∉ other) ∨ (x ∉ self ∧ x ∈ other))
    fn symmetric_difference(&self, other: &Self) -> Self;

    /// Checks if this set is a subset of another set.
    /// self ⊆ other ↔ ∀x(x ∈ self → x ∈ other)
    fn is_subset(&self, other: &Self) -> bool;

    /// Checks if two sets are equal (by the Axiom of Extensionality).
    /// self = other ↔ ∀x(x ∈ self ↔ x ∈ other)
    fn is_equal(&self, other: &Self) -> bool;

    /// Returns the cardinality of the set. Returns None if the set is infinite.
    /// |self| if self is finite, None otherwise
    fn cardinality(&self) -> Option<usize>;

    /// Returns true if the set is finite, false otherwise.
    fn is_finite(&self) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::{InfiniteRealSet, Z5};

    #[test]
    fn test_z5_set_operations() {
        let a = Z5::new(2);
        let b = Z5::new(3);
        let c = Z5::new(2);

        assert!(!a.is_empty());
        assert!(a.contains(&Z5::new(2)));
        assert!(!a.contains(&Z5::new(3)));

        assert_eq!(Z5::empty(), Z5::new(0));
        assert_eq!(Z5::singleton(Z5::new(2)), a);

        assert_eq!(a.union(&b), Z5::new(2));
        assert_eq!(a.intersection(&b), Z5::new(0));
        assert_eq!(a.intersection(&c), a);

        assert_eq!(a.difference(&b), a);
        assert_eq!(a.difference(&c), Z5::new(0));

        assert_eq!(a.symmetric_difference(&b), Z5::new(3));
        assert_eq!(a.symmetric_difference(&c), Z5::new(0));

        assert!(a.is_subset(&a));
        assert!(!a.is_subset(&b));

        assert!(a.is_equal(&c));
        assert!(!a.is_equal(&b));

        assert_eq!(a.cardinality(), Some(5));
        assert!(a.is_finite());
    }

    #[test]
    fn test_infinite_real_set_operations() {
        let a = InfiniteRealSet;
        let b = InfiniteRealSet;

        assert!(!a.is_empty());
        assert!(a.contains(&3.14));
        assert!(a.contains(&-1000.0));

        assert_eq!(InfiniteRealSet::empty(), InfiniteRealSet);
        assert_eq!(InfiniteRealSet::singleton(3.14), InfiniteRealSet);

        assert_eq!(a.union(&b), InfiniteRealSet);
        assert_eq!(a.intersection(&b), InfiniteRealSet);
        assert_eq!(a.difference(&b), InfiniteRealSet);
        assert_eq!(a.symmetric_difference(&b), InfiniteRealSet);

        assert!(a.is_subset(&b));
        assert!(a.is_equal(&b));

        assert_eq!(a.cardinality(), None);
        assert!(!a.is_finite());
    }

    #[test]
    fn test_z5_edge_cases() {
        let zero = Z5::new(0);
        let five = Z5::new(5);

        assert_eq!(zero, five);
        assert_eq!(Z5::new(7), Z5::new(2));

        assert_eq!(zero.union(&five), zero);
        assert_eq!(zero.intersection(&five), zero);
        assert_eq!(zero.difference(&five), zero);
        assert_eq!(zero.symmetric_difference(&five), zero);
    }
}

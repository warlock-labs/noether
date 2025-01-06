use noether::{AssociativeJoin, CommutativeJoin, IdempotentJoin, Join, JoinSemiLattice};
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetJoinSemilattice<T: Eq + std::hash::Hash + Clone> {
    set: HashSet<T>,
}
impl<T: Eq + std::hash::Hash + Clone> SetJoinSemilattice<T> {
    pub const fn new(set: HashSet<T>) -> Self {
        Self { set }
    }
}
impl<T: Eq + std::hash::Hash + Clone> CommutativeJoin for SetJoinSemilattice<T> {}
impl<T: Eq + std::hash::Hash + Clone> AssociativeJoin for SetJoinSemilattice<T> {}

impl<T: Eq + std::hash::Hash + Clone> IdempotentJoin for SetJoinSemilattice<T> {}

impl<T: Eq + std::hash::Hash + Clone> Join for SetJoinSemilattice<T> {
    fn join(self, other: &Self) -> Self {
        let union: HashSet<T> = self.set.union(&other.set).cloned().collect();
        Self { set: union }
    }

    /// The identity element: an empty set.
    /// Satisfies: a ⋁ {} == a
    fn identity(&self) -> Self {
        Self {
            set: HashSet::new(),
        }
    }
}

// // impl Join for  {};

impl<T: Eq + std::hash::Hash + Clone> JoinSemiLattice for SetJoinSemilattice<T> {}

fn main() {
    // Test 1: check join of different sets
    let set_a: HashSet<_> = vec![1, 2, 3].into_iter().collect();
    let set_b: HashSet<_> = vec![3, 4, 5].into_iter().collect();

    let semilattice_a = SetJoinSemilattice { set: set_a };
    let semilattice_b = SetJoinSemilattice { set: set_b };

    // Perform the join operation (union)
    let result: SetJoinSemilattice<i32> = semilattice_a.join(&semilattice_b);
    println!("Resulting Set: {:?}", result.set);

    // Test 2: check join of same element

    let set_c: HashSet<_> = vec![1, 2, 3].into_iter().collect();
    let set_d: HashSet<_> = vec![1, 2, 3].into_iter().collect();

    let semilattice_c = SetJoinSemilattice { set: set_c };
    let semilattice_d = SetJoinSemilattice { set: set_d };

    let result_same_set: SetJoinSemilattice<i32> = semilattice_c.join(&semilattice_d);
    println!("Resulting Same Set: {:?}", result_same_set.set);

    // Test 3: check join with identity element should return the same set

    let set_e: HashSet<_> = vec![1, 2, 4].into_iter().collect();

    let semilattice_e = SetJoinSemilattice { set: set_e };
    let identity = semilattice_e.identity();

    let result_identity: SetJoinSemilattice<i32> = semilattice_e.join(&identity);
    println!(
        "Resulting of join with identity should return same set {:?}",
        result_identity.set
    );
}

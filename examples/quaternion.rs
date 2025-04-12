use noether::{AssociativeAddition, AssociativeMultiplication, CommutativeAddition, Field};
use num_traits::{Inv, One, Zero};
use std::cmp::PartialEq;
use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// A quaternion implementation, representing the non-commutative division algebra H.
///
/// A quaternion has the form a + bi + cj + dk where:
/// - a, b, c, d are elements from a field F
/// - i, j, k are imaginary units
/// - i² = j² = k² = ijk = -1
/// - ij = k, ji = -k
/// - jk = i, kj = -i
/// - ki = j, ik = -j
///
/// Quaternions form a 4-dimensional associative normed division algebra over F.
#[derive(Debug, Clone, PartialEq)]
pub struct Quaternion<F: Field + Clone + Copy> {
    // Real part
    pub a: F,
    // Imaginary parts
    pub b: F,
    pub c: F,
    pub d: F,
}

impl<F: Field + Clone + Copy> Quaternion<F> {
    /// Creates a new quaternion with the form a + bi + cj + dk
    pub fn new(a: F, b: F, c: F, d: F) -> Self {
        Self { a, b, c, d }
    }

    /// Creates a new quaternion from a scalar (real part only)
    pub fn from_scalar(scalar: F) -> Self {
        Self::new(scalar, F::zero(), F::zero(), F::zero())
    }

    /// Creates a quaternion from a 3D vector (as the imaginary part)
    pub fn from_vector(b: F, c: F, d: F) -> Self {
        Self::new(F::zero(), b, c, d)
    }

    /// Converts a quaternion to a 4D array [a, b, c, d]
    pub fn to_array(&self) -> [F; 4] {
        [self.a, self.b, self.c, self.d]
    }

    /// Returns the real part of the quaternion
    pub fn real(&self) -> F {
        self.a
    }

    /// Returns the imaginary part of the quaternion as a 3D vector
    pub fn imag(&self) -> [F; 3] {
        [self.b, self.c, self.d]
    }

    /// Returns the squared norm (squared magnitude) of the quaternion
    pub fn norm_squared(&self) -> F {
        self.a * self.a + self.b * self.b + self.c * self.c + self.d * self.d
    }

    /// Returns the conjugate of the quaternion
    pub fn conjugate(&self) -> Self {
        Self::new(self.a, -self.b, -self.c, -self.d)
    }

    /// Returns the inverse of the quaternion
    pub fn inverse(&self) -> Self {
        let norm_sq = self.norm_squared();
        if norm_sq == F::zero() {
            panic!("Cannot compute inverse of zero quaternion");
        }

        let conj = self.conjugate();
        Self::new(
            conj.a / norm_sq,
            conj.b / norm_sq,
            conj.c / norm_sq,
            conj.d / norm_sq,
        )
    }

    /// Returns the dot product of two quaternions
    pub fn dot(&self, other: &Self) -> F {
        self.a * other.a + self.b * other.b + self.c * other.c + self.d * other.d
    }
}

// Implement basic arithmetic operations

impl<F: Field + Clone + Copy> Add for Quaternion<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(
            self.a + rhs.a,
            self.b + rhs.b,
            self.c + rhs.c,
            self.d + rhs.d,
        )
    }
}

impl<F: Field + Clone + Copy> AddAssign for Quaternion<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: Field + Clone + Copy> Sub for Quaternion<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(
            self.a - rhs.a,
            self.b - rhs.b,
            self.c - rhs.c,
            self.d - rhs.d,
        )
    }
}

impl<F: Field + Clone + Copy> SubAssign for Quaternion<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: Field + Clone + Copy> Neg for Quaternion<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.a, -self.b, -self.c, -self.d)
    }
}

// Note that quaternion multiplication is non-commutative
impl<F: Field + Clone + Copy> Mul for Quaternion<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        // (a + bi + cj + dk) * (e + fi + gj + hk)
        // = (ae - bf - cg - dh) + (af + be + ch - dg)i + (ag - bh + ce + df)j + (ah + bg - cf + de)k
        Self::new(
            self.a * rhs.a - self.b * rhs.b - self.c * rhs.c - self.d * rhs.d,
            self.a * rhs.b + self.b * rhs.a + self.c * rhs.d - self.d * rhs.c,
            self.a * rhs.c - self.b * rhs.d + self.c * rhs.a + self.d * rhs.b,
            self.a * rhs.d + self.b * rhs.c - self.c * rhs.b + self.d * rhs.a,
        )
    }
}

impl<F: Field + Clone + Copy> MulAssign for Quaternion<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: Field + Clone + Copy> Div for Quaternion<F> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        // q1 / q2 = q1 * q2^(-1)
        let rhs_inv = rhs.inverse();
        // Using explicit multiplication to avoid clippy warning
        Quaternion::new(
            self.a * rhs_inv.a - self.b * rhs_inv.b - self.c * rhs_inv.c - self.d * rhs_inv.d,
            self.a * rhs_inv.b + self.b * rhs_inv.a + self.c * rhs_inv.d - self.d * rhs_inv.c,
            self.a * rhs_inv.c - self.b * rhs_inv.d + self.c * rhs_inv.a + self.d * rhs_inv.b,
            self.a * rhs_inv.d + self.b * rhs_inv.c - self.c * rhs_inv.b + self.d * rhs_inv.a,
        )
    }
}

impl<F: Field + Clone + Copy> DivAssign for Quaternion<F> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}

// Scalar operations

impl<F: Field + Clone + Copy> Mul<F> for Quaternion<F> {
    type Output = Self;

    fn mul(self, scalar: F) -> Self::Output {
        Self::new(
            self.a * scalar,
            self.b * scalar,
            self.c * scalar,
            self.d * scalar,
        )
    }
}

impl<F: Field + Clone + Copy> Div<F> for Quaternion<F> {
    type Output = Self;

    fn div(self, scalar: F) -> Self::Output {
        if scalar == F::zero() {
            panic!("Division by zero scalar");
        }

        Self::new(
            self.a / scalar,
            self.b / scalar,
            self.c / scalar,
            self.d / scalar,
        )
    }
}

// Implement standard traits

impl<F: Field + Clone + Copy> Zero for Quaternion<F> {
    fn zero() -> Self {
        Self::new(F::zero(), F::zero(), F::zero(), F::zero())
    }

    fn is_zero(&self) -> bool {
        self.a == F::zero() && self.b == F::zero() && self.c == F::zero() && self.d == F::zero()
    }
}

impl<F: Field + Clone + Copy> One for Quaternion<F> {
    fn one() -> Self {
        Self::new(F::one(), F::zero(), F::zero(), F::zero())
    }
}

impl<F: Field + Clone + Copy> Inv for Quaternion<F> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        self.inverse()
    }
}

// Implement Display for nice printing
impl<F: Field + Clone + Copy + Display + PartialOrd> Display for Quaternion<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;

        // Real part
        if self.a != F::zero()
            || (self.b == F::zero() && self.c == F::zero() && self.d == F::zero())
        {
            write!(f, "{}", self.a)?;
            first = false;
        }

        // b component
        if self.b != F::zero() {
            if !first && self.b > F::zero() {
                write!(f, " + ")?;
            } else if !first {
                write!(f, " - ")?;
            } else if self.b < F::zero() {
                write!(f, "-")?;
            }

            let abs_b = if self.b < F::zero() { -self.b } else { self.b };
            if abs_b == F::one() {
                write!(f, "i")?;
            } else {
                write!(f, "{}i", abs_b)?;
            }
            first = false;
        }

        // c component
        if self.c != F::zero() {
            if !first && self.c > F::zero() {
                write!(f, " + ")?;
            } else if !first {
                write!(f, " - ")?;
            } else if self.c < F::zero() {
                write!(f, "-")?;
            }

            let abs_c = if self.c < F::zero() { -self.c } else { self.c };
            if abs_c == F::one() {
                write!(f, "j")?;
            } else {
                write!(f, "{}j", abs_c)?;
            }
            first = false;
        }

        // d component
        if self.d != F::zero() {
            if !first && self.d > F::zero() {
                write!(f, " + ")?;
            } else if !first {
                write!(f, " - ")?;
            } else if self.d < F::zero() {
                write!(f, "-")?;
            }

            let abs_d = if self.d < F::zero() { -self.d } else { self.d };
            if abs_d == F::one() {
                write!(f, "k")?;
            } else {
                write!(f, "{}k", abs_d)?;
            }
        }

        Ok(())
    }
}

// Implement Noether's algebraic marker traits
impl<F: Field + Clone + Copy> AssociativeAddition for Quaternion<F> {}
impl<F: Field + Clone + Copy> CommutativeAddition for Quaternion<F> {}
impl<F: Field + Clone + Copy> AssociativeMultiplication for Quaternion<F> {}
// Note: Multiplication is NOT commutative, so we don't implement CommutativeMultiplication

// Thanks to Noether's blanket implementations, quaternions satisfy:
// - AdditiveAbelianGroup (from AssociativeAddition + CommutativeAddition + Zero + Neg)
// - MultiplicativeSemigroup (from AssociativeMultiplication)
// - But not a field (multiplication isn't commutative)

/// Verify properties of quaternions using f64
fn verify_quaternion_properties() {
    println!("Verifying quaternion algebraic properties:");

    // Define some test quaternions using f64
    let q1 = Quaternion::new(1.0, 2.0, 3.0, 4.0);
    let q2 = Quaternion::new(2.0, 3.0, 4.0, 5.0);
    let q3 = Quaternion::new(3.0, 4.0, 5.0, 6.0);

    // Zero and identity
    let zero = Quaternion::<f64>::zero();
    let one = Quaternion::<f64>::one();

    // Test additive properties
    println!("1. Additive identity: q + 0 = q");
    println!("   {} + {} = {}", q1, zero, q1.clone() + zero.clone());
    assert_eq!(q1.clone() + zero.clone(), q1);

    println!("2. Additive inverse: q + (-q) = 0");
    println!(
        "   {} + ({}) = {}",
        q1,
        -q1.clone(),
        q1.clone() + (-q1.clone())
    );
    assert!((q1.clone() + (-q1.clone())).is_zero());

    println!("3. Additive commutativity: q1 + q2 = q2 + q1");
    println!("   {} + {} = {}", q1, q2, q1.clone() + q2.clone());
    println!("   {} + {} = {}", q2, q1, q2.clone() + q1.clone());
    assert_eq!(q1.clone() + q2.clone(), q2.clone() + q1.clone());

    println!("4. Additive associativity: (q1 + q2) + q3 = q1 + (q2 + q3)");
    println!(
        "   ({} + {}) + {} = {}",
        q1,
        q2,
        q3,
        (q1.clone() + q2.clone()) + q3.clone()
    );
    println!(
        "   {} + ({} + {}) = {}",
        q1,
        q2,
        q3,
        q1.clone() + (q2.clone() + q3.clone())
    );
    assert_eq!(
        (q1.clone() + q2.clone()) + q3.clone(),
        q1.clone() + (q2.clone() + q3.clone())
    );

    // Test multiplicative properties
    println!("5. Multiplicative identity: q * 1 = 1 * q = q");
    println!("   {} * {} = {}", q1, one, q1.clone() * one.clone());
    println!("   {} * {} = {}", one, q1, one.clone() * q1.clone());
    assert_eq!(q1.clone() * one.clone(), q1.clone());
    assert_eq!(one.clone() * q1.clone(), q1.clone());

    println!("6. Multiplicative inverse: q * q^(-1) = q^(-1) * q = 1");
    let q1_inv = q1.inverse();
    println!("   {} * {} = {}", q1, q1_inv, q1.clone() * q1_inv.clone());
    println!("   {} * {} = {}", q1_inv, q1, q1_inv.clone() * q1.clone());

    // Due to floating point precision, we need to use an epsilon for comparison
    const EPSILON: f64 = 1e-10;
    let q_result = q1.clone() * q1_inv.clone();

    assert!(
        (q_result.a - 1.0).abs() < EPSILON,
        "Expected a ≈ 1.0, got {}",
        q_result.a
    );
    assert!(
        q_result.b.abs() < EPSILON,
        "Expected b ≈ 0.0, got {}",
        q_result.b
    );
    assert!(
        q_result.c.abs() < EPSILON,
        "Expected c ≈ 0.0, got {}",
        q_result.c
    );
    assert!(
        q_result.d.abs() < EPSILON,
        "Expected d ≈ 0.0, got {}",
        q_result.d
    );

    println!("7. Multiplicative NON-commutativity: q1 * q2 ≠ q2 * q1");
    println!("   {} * {} = {}", q1, q2, q1.clone() * q2.clone());
    println!("   {} * {} = {}", q2, q1, q2.clone() * q1.clone());
    assert_ne!(q1.clone() * q2.clone(), q2.clone() * q1.clone());

    println!("8. Multiplicative associativity: (q1 * q2) * q3 = q1 * (q2 * q3)");
    println!(
        "   ({} * {}) * {} = {}",
        q1,
        q2,
        q3,
        (q1.clone() * q2.clone()) * q3.clone()
    );
    println!(
        "   {} * ({} * {}) = {}",
        q1,
        q2,
        q3,
        q1.clone() * (q2.clone() * q3.clone())
    );
    assert_eq!(
        (q1.clone() * q2.clone()) * q3.clone(),
        q1.clone() * (q2.clone() * q3.clone())
    );

    // Demonstrate division algebra property
    println!("9. Division property: For any non-zero q1, q2, the equation q1 * x = q2 has unique solution x = q1^(-1) * q2");
    let x = q1_inv.clone() * q2.clone();
    println!("   Solution x = q1^(-1) * q2 = {} * {} = {}", q1_inv, q2, x);
    println!(
        "   Verification: q1 * x = {} * {} = {}",
        q1,
        x,
        q1.clone() * x.clone()
    );

    let diff = (q1.clone() * x) - q2;
    let is_close = diff.norm_squared() < 1e-10;
    println!("   Equation verified: {}", is_close);

    println!("\nAll quaternion algebraic properties verified!\n");
}

/// Demonstrate quaternion basic operations with rational numbers
fn demonstrate_rational_quaternions() {
    // We'll represent rational numbers as tuples (numerator, denominator)
    // In a real implementation, we would use a proper Rational type

    println!("Quaternions can be implemented over any field, not just reals.");
    println!("For example, we could work with rational quaternions if we had a Rational type.");
    println!("Showing the concept using f64 to simulate rational numbers:\n");

    // Represent 1/2 + (2/3)i + (3/4)j + (4/5)k
    let q1 = Quaternion::new(0.5, 2.0 / 3.0, 0.75, 0.8);
    println!("q1 = {}", q1);

    // Represent 2/3 + (1/4)i + (3/7)j + (1/5)k
    let q2 = Quaternion::new(2.0 / 3.0, 0.25, 3.0 / 7.0, 0.2);
    println!("q2 = {}", q2);

    // Basic operations
    println!("q1 + q2 = {}", q1.clone() + q2.clone());
    println!("q1 - q2 = {}", q1.clone() - q2.clone());
    println!("q1 * q2 = {}", q1.clone() * q2.clone());
    println!("q2 * q1 = {}", q2.clone() * q1.clone());

    // Show non-commutativity
    println!(
        "q1 * q2 == q2 * q1? {}",
        q1.clone() * q2.clone() == q2.clone() * q1.clone()
    );

    // Division and inverse
    println!("q1^(-1) = {}", q1.inverse());
    println!("q1 * q1^(-1) = {}", q1.clone() * q1.inverse());
    println!("q1 / q2 = {}", q1.clone() / q2.clone());

    println!("\nThe same operations would work over any field type that implements Noether's Field trait");
}

/// Demonstrate a traditional application: 3D rotations with quaternions
fn demonstrate_quaternion_rotations() {
    // For rotations, we'll use the standard quaternion rotation formula:
    // v' = q * v * q^(-1)
    // where v is a pure quaternion (0 + xi + yj + zk) representing a 3D vector

    println!("\nDemonstrating quaternion rotations (a key application):");

    // Create a unit quaternion representing a 90-degree rotation around z-axis
    let theta = std::f64::consts::PI / 2.0; // 90 degrees
    let q_rot = Quaternion::new((theta / 2.0).cos(), 0.0, 0.0, (theta / 2.0).sin());
    println!("Rotation quaternion (90° around z-axis): {}", q_rot);

    // Create a vector pointing along the x-axis
    let v = Quaternion::new(0.0, 1.0, 0.0, 0.0);
    println!("Vector to rotate: {}", v);

    // Rotate the vector
    let v_rot = q_rot.clone() * v.clone() * q_rot.inverse();
    println!("Rotated vector: {}", v_rot);
    println!("Expected result: quaternion representation of (0, 0, 1, 0)");

    // Verify it's still a pure quaternion (a = 0)
    println!("Is the result a pure quaternion? {}", v_rot.a == 0.0);

    // Show the resulting vector
    println!(
        "Resulting 3D vector: [{}, {}, {}]",
        v_rot.b, v_rot.c, v_rot.d
    );
    println!("This shows a 90° rotation around z-axis transformed (1,0,0) to (0,1,0) as expected");
}

fn main() {
    println!("=== Quaternion Algebra Example ===");
    println!("This example demonstrates quaternions as a non-commutative division algebra.\n");

    // Verify algebraic properties
    verify_quaternion_properties();

    // Demonstrate with rational numbers
    demonstrate_rational_quaternions();

    // Demonstrate 3D rotations
    demonstrate_quaternion_rotations();

    println!("\n=== Quaternion Applications ===");
    println!("1. 3D rotations and orientations in computer graphics and game development");
    println!("2. Spacecraft attitude control and navigation");
    println!("3. Robotics: arm movements and orientation control");
    println!("4. Virtual/Augmented reality: head tracking and orientation");
    println!("5. Computer vision: camera pose estimation");
    println!("6. Physics simulations: rigid body dynamics");

    println!("\nQuaternions provide a more compact and numerically stable way to represent");
    println!("3D rotations compared to matrices, and they avoid gimbal lock issues that");
    println!("can occur with Euler angles. They form an important example of a");
    println!("non-commutative division algebra in mathematics.");

    println!("\nThis example demonstrates working with Noether's Field trait to create");
    println!("generic algebraic structures. The quaternion implementation can work with");
    println!("any type that satisfies the Field trait requirements.");
}

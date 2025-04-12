use noether::{
    AssociativeAddition, AssociativeMultiplication, CommutativeAddition, CommutativeMultiplication,
    Distributive, FiniteField,
};
use num_traits::{Euclid, Inv, One, Zero};
use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

/// A simple finite field implementation for GF(p) where p is a prime.
///
/// This example demonstrates how to implement a concrete finite field
/// using Noether's trait hierarchy and showcase mathematical properties and applications.
///
/// For multi-precision field elements or GF(p^n) extension fields, see the
/// multi_precision_finite_field.rs example which focuses on those aspects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fp<const P: u64> {
    /// Value in range [0, P-1]
    value: u64,
}

impl<const P: u64> Fp<P> {
    /// Creates a new element of the field GF(p)
    pub fn new(value: u64) -> Self {
        // We should check that P is prime, but for simplicity we'll just check it's > 1
        assert!(P > 1, "P must be at least 2");
        Self { value: value % P }
    }

    /// Gets the underlying value
    pub fn value(&self) -> u64 {
        self.value
    }

    /// Computes the multiplicative inverse using extended Euclidean algorithm
    fn inv_value(&self) -> Option<u64> {
        if self.value == 0 {
            return None;
        }

        // Extended Euclidean Algorithm to find modular inverse
        let mut a = self.value as i128;
        let mut m = P as i128;
        let mut x = 1i128;
        let mut y = 0i128;

        while a > 1 {
            // q is quotient
            let q = a / m;

            // m is remainder now, process same as Euclid's algorithm
            let temp = m;
            m = a % m;
            a = temp;

            // Update x and y
            let temp = y;
            y = x - q * y;
            x = temp;
        }

        // Make x positive
        if x < 0 {
            x += P as i128;
        }

        Some(x as u64)
    }

    /// Gets the characteristic of the field (the prime p)
    pub fn characteristic() -> u64 {
        P
    }

    /// Gets the order of the field (number of elements = p)
    pub fn order() -> u64 {
        P
    }

    /// Performs modular exponentiation efficiently
    pub fn pow(&self, exp: u64) -> Self {
        if exp == 0 {
            return Self::one();
        }

        let mut result = Self::one();
        let mut base = *self;
        let mut exp = exp;

        while exp > 0 {
            if exp % 2 == 1 {
                result *= base;
            }

            base = base * base;
            exp /= 2;
        }

        result
    }
}

// Basic arithmetic operations

impl<const P: u64> Add for Fp<P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.value + rhs.value)
    }
}

impl<const P: u64> AddAssign for Fp<P> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const P: u64> Sub for Fp<P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        // Add P to handle the case where self.value < rhs.value
        Self::new(self.value + P - rhs.value)
    }
}

impl<const P: u64> SubAssign for Fp<P> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const P: u64> Mul for Fp<P> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.value * rhs.value)
    }
}

impl<const P: u64> MulAssign for Fp<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<const P: u64> Div for Fp<P> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Division by zero in finite field");
        }

        // Multiplication by the multiplicative inverse
        self * rhs.inv()
    }
}

impl<const P: u64> DivAssign for Fp<P> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<const P: u64> Neg for Fp<P> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.value == 0 {
            self // -0 = 0
        } else {
            Self::new(P - self.value)
        }
    }
}

impl<const P: u64> Rem for Fp<P> {
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Remainder by zero in finite field");
        }

        Self::new(self.value % rhs.value)
    }
}

// Identity implementations

impl<const P: u64> Zero for Fp<P> {
    fn zero() -> Self {
        Self::new(0)
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const P: u64> One for Fp<P> {
    fn one() -> Self {
        Self::new(1)
    }
}

// Implement num_traits::Inv (multiplicative inverse)
impl<const P: u64> Inv for Fp<P> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        if self.value == 0 {
            panic!("Attempt to invert zero in finite field");
        }

        Self::new(self.inv_value().unwrap())
    }
}

// Implement Euclid trait for Euclidean division
impl<const P: u64> Euclid for Fp<P> {
    fn div_euclid(&self, v: &Self) -> Self {
        if v.value == 0 {
            panic!("Division by zero in finite field");
        }
        *self / *v
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        if v.value == 0 {
            panic!("Remainder by zero in finite field");
        }
        *self % *v
    }
}

// Formatting for display
impl<const P: u64> Display for Fp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Noether's algebraic marker traits
impl<const P: u64> CommutativeAddition for Fp<P> {}
impl<const P: u64> AssociativeAddition for Fp<P> {}
impl<const P: u64> CommutativeMultiplication for Fp<P> {}
impl<const P: u64> AssociativeMultiplication for Fp<P> {}
impl<const P: u64> Distributive for Fp<P> {}

// Due to blanket implementations in Noether, we just need to implement the marker traits.
// The Field trait is automatically implemented through blanket implementations
// based on our implementations of the marker traits.

impl<const P: u64> FiniteField for Fp<P> {
    type ScalarType = u64; // Using u64 as more compatible scalar type

    fn characteristic() -> u64 {
        P
    }

    fn order() -> u64 {
        P
    }
}

/// Verify all field axioms for a given finite field
fn verify_field_axioms<const P: u64>(elements: &[Fp<P>]) {
    println!("Verifying field axioms for GF({}):", P);

    // Verify additive identity
    let zero = Fp::<P>::zero();
    for &a in elements {
        assert_eq!(a + zero, a, "Additive identity failed for {}", a);
    }
    println!("✓ Additive identity verified");

    // Verify additive inverse
    for &a in elements {
        if a != zero {
            assert_eq!(a + (-a), zero, "Additive inverse failed for {}", a);
        }
    }
    println!("✓ Additive inverse verified");

    // Verify multiplicative identity
    let one = Fp::<P>::one();
    for &a in elements {
        assert_eq!(a * one, a, "Multiplicative identity failed for {}", a);
    }
    println!("✓ Multiplicative identity verified");

    // Verify multiplicative inverse
    for &a in elements {
        if a != zero {
            let inv = a.inv();
            assert_eq!(a * inv, one, "Multiplicative inverse failed for {}", a);
        }
    }
    println!("✓ Multiplicative inverse verified");

    // Verify commutativity
    for &a in elements {
        for &b in elements {
            let sum1 = a + b;
            let sum2 = b + a;
            assert_eq!(
                sum1, sum2,
                "Additive commutativity failed for {} and {}",
                a, b
            );
            assert_eq!(
                a * b,
                b * a,
                "Multiplicative commutativity failed for {} and {}",
                a,
                b
            );
        }
    }
    println!("✓ Commutativity verified");

    // Verify associativity (sample a few cases for larger fields)
    let test_count = if elements.len() <= 5 {
        elements.len()
    } else {
        5
    };
    for &a in elements.iter().take(test_count) {
        for &b in elements.iter().take(test_count) {
            for &c in elements.iter().take(test_count) {
                assert_eq!((a + b) + c, a + (b + c), "Additive associativity failed");
                assert_eq!(
                    (a * b) * c,
                    a * (b * c),
                    "Multiplicative associativity failed"
                );
            }
        }
    }
    println!("✓ Associativity verified (sampled)");

    // Verify distributivity (sample a few cases for larger fields)
    for &a in elements.iter().take(test_count) {
        for &b in elements.iter().take(test_count) {
            for &c in elements.iter().take(test_count) {
                assert_eq!(
                    a * (b + c),
                    (a * b) + (a * c),
                    "Distributivity failed for {}, {}, {}",
                    a,
                    b,
                    c
                );
            }
        }
    }
    println!("✓ Distributivity verified (sampled)");
}

// Create a multiplication table for a finite field
fn print_multiplication_table<const P: u64>() {
    println!("\nMultiplication Table for GF({}):", P);

    // Print header row
    print!("× | ");
    for i in 0..P {
        print!("{:2} ", i);
    }
    println!("\n--+-{}", "-".repeat(3 * P as usize));

    // Print table rows
    for i in 0..P {
        print!("{:1} | ", i);
        for j in 0..P {
            let product = Fp::<P>::new(i) * Fp::<P>::new(j);
            print!("{:2} ", product.value());
        }
        println!();
    }
    println!();
}

/// Implements the Diffie-Hellman key exchange protocol in a finite field.
fn diffie_hellman<const P: u64>(g: Fp<P>, a: u64, b: u64) -> (Fp<P>, Fp<P>, Fp<P>) {
    // g is the generator element
    // a is Alice's private key
    // b is Bob's private key

    // Compute public keys
    let alice_public = g.pow(a);
    let bob_public = g.pow(b);

    // Compute shared secrets
    let alice_secret = bob_public.pow(a);
    let bob_secret = alice_public.pow(b);

    assert_eq!(alice_secret, bob_secret, "Shared secrets must match");

    (alice_public, bob_public, alice_secret)
}

fn main() {
    println!("Finite Field Operations Example");
    println!("===============================\n");

    // Example 1: Working with GF(7)
    const P7: u64 = 7;
    println!("Example 1: Operations in GF({})", P7);

    // Create all elements of GF(7)
    let elements_gf7: Vec<Fp<P7>> = (0..P7).map(Fp::<P7>::new).collect();

    // Verify the field axioms
    verify_field_axioms(&elements_gf7);

    // Print the multiplication table
    print_multiplication_table::<P7>();

    // Demonstrate field properties
    println!("\nDemonstrating field properties:");
    println!("Field characteristic: {}", P7); // This is the field's characteristic
    println!("Field order: {}", P7); // For a prime field, the order equals the characteristic

    // Demonstrate arithmetic operations
    let a = Fp::<P7>::new(3);
    let b = Fp::<P7>::new(5);

    println!("Let a = {} and b = {} in GF({})", a, b, P7);
    println!("a + b = {}", a + b);
    println!("a - b = {}", a - b);
    println!("a * b = {}", a * b);
    println!("a / b = {}", a / b);
    println!("-a = {}", -a);
    println!("a^{} = {}", 3, a.pow(3));
    println!("1/a = {}", a.inv());

    // Example 2: Diffie-Hellman Key Exchange
    println!("\nExample 2: Diffie-Hellman Key Exchange in GF({})", P7);

    let g = Fp::<P7>::new(3); // Generator element
    let alice_private = 4; // Alice's private key
    let bob_private = 2; // Bob's private key

    let (alice_public, bob_public, shared_secret) = diffie_hellman(g, alice_private, bob_private);

    println!("Generator g = {}", g);
    println!("Alice's private key = {}", alice_private);
    println!("Bob's private key = {}", bob_private);
    println!("Alice's public key = g^a = {}", alice_public);
    println!("Bob's public key = g^b = {}", bob_public);
    println!("Shared secret = g^(ab) = {}", shared_secret);

    // Example 3: Working with a larger field GF(17)
    const P17: u64 = 17;
    println!("\nExample 3: Operations in GF({})", P17);

    let c = Fp::<P17>::new(7);
    let d = Fp::<P17>::new(11);

    println!("Let c = {} and d = {} in GF({})", c, d, P17);
    println!("c + d = {}", c + d);
    println!("c - d = {}", c - d);
    println!("c * d = {}", c * d);
    println!("c / d = {}", c / d);
    println!("-c = {}", -c);
    println!("c^{} = {}", 5, c.pow(5));
    println!("1/c = {}", c.inv());

    // Find primitive element (generator) in GF(17)
    println!("\nFinding a primitive element (generator) in GF({}):", P17);
    let mut found_generator = false;

    for i in 2..P17 {
        let g = Fp::<P17>::new(i);
        let mut powers = vec![Fp::<P17>::one()];
        let mut current = g;

        // Generate all powers of g
        for _ in 1..(P17 - 1) {
            powers.push(current);
            current *= g;
        }

        // Check if it generates all non-zero elements
        if powers.len() == (P17 - 1) as usize {
            let mut unique_powers = powers.clone();
            unique_powers.sort_by_key(|e| e.value());
            unique_powers.dedup();

            if unique_powers.len() == (P17 - 1) as usize {
                println!("Found generator {} in GF({})!", i, P17);
                found_generator = true;
                break;
            }
        }
    }

    if !found_generator {
        println!("No generator found in GF({}).", P17);
    }

    // Example 4: Pohlig-Hellman Discrete Logarithm in small field
    println!("\nExample 4: Discrete Logarithm in GF({}):", P7);
    let g = Fp::<P7>::new(3);
    let y = Fp::<P7>::new(6);

    // Brute force calculation of discrete log
    let mut found_x = false;
    for x in 1..P7 {
        if g.pow(x) == y {
            println!("Found discrete logarithm: {}^{} = {} (mod {})", g, x, y, P7);
            found_x = true;
            break;
        }
    }

    if !found_x {
        println!("No solution found for discrete logarithm.");
    }

    println!("\nThis example demonstrates how to implement and work with finite fields");
    println!("using the algebraic structure traits provided by the Noether library.");
}

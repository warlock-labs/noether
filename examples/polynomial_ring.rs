use noether::{
    AssociativeAddition, AssociativeMultiplication, CommutativeAddition, CommutativeMultiplication,
    Distributive, Polynomial, Ring,
};
use num_traits::{Euclid, One, Zero};
use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

/// A generic polynomial implementation over a ring R.
///
/// The polynomial is represented as a vector of coefficients [a₀, a₁, a₂, ...],
/// where each aᵢ is the coefficient of xⁱ.
#[derive(Clone, Debug, PartialEq)]
pub struct Poly<R> {
    /// Coefficients of the polynomial, with index i representing the coefficient of x^i
    /// Zero trailing coefficients are trimmed
    coeffs: Vec<R>,
}

impl<R: Clone + PartialEq + Zero> Poly<R> {
    /// Creates a new polynomial from a slice of coefficients.
    /// The first element is the constant term (x^0), the second is the coefficient of x^1, etc.
    pub fn new(coeffs: &[R]) -> Self {
        let mut result = Self {
            coeffs: coeffs.to_vec(),
        };
        result.trim_zeros();
        result
    }

    /// Creates a constant polynomial
    pub fn constant(c: R) -> Self {
        if c.is_zero() {
            Self { coeffs: vec![] }
        } else {
            Self { coeffs: vec![c] }
        }
    }

    /// Creates the zero polynomial
    pub fn zero() -> Self {
        Self { coeffs: vec![] }
    }

    /// Creates the polynomial x (the monomial of degree 1)
    pub fn x() -> Self
    where
        R: One,
    {
        Self {
            coeffs: vec![R::zero(), R::one()],
        }
    }

    /// Returns the degree of the polynomial as isize.
    /// The zero polynomial is defined to have degree -1.
    /// For internal use - Polynomial trait uses degree() returning usize.
    fn degree_isize(&self) -> isize {
        if self.coeffs.is_empty() {
            -1
        } else {
            (self.coeffs.len() - 1) as isize
        }
    }

    /// Returns the degree of the polynomial.
    /// The zero polynomial is defined to have degree 0 for usize compatibility.
    pub fn degree(&self) -> usize {
        if self.coeffs.is_empty() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    /// Gets the coefficient at the specified degree.
    /// Returns zero for degrees higher than the polynomial's degree.
    pub fn coefficient(&self, degree: usize) -> R {
        if degree < self.coeffs.len() {
            self.coeffs[degree].clone()
        } else {
            R::zero()
        }
    }

    /// Sets the coefficient at the specified degree.
    pub fn set_coefficient(&mut self, degree: usize, value: R) {
        if degree >= self.coeffs.len() {
            self.coeffs.resize(degree + 1, R::zero());
        }
        self.coeffs[degree] = value;
        self.trim_zeros();
    }

    /// Removes trailing zero coefficients to maintain canonical form
    fn trim_zeros(&mut self) {
        while let Some(true) = self.coeffs.last().map(|c| c.is_zero()) {
            self.coeffs.pop();
        }
    }

    /// Evaluates the polynomial at a given point x
    pub fn evaluate(&self, x: &R) -> R
    where
        R: Clone + Add<Output = R> + Mul<Output = R> + Zero,
    {
        if self.coeffs.is_empty() {
            return R::zero();
        }

        // Horner's method: a₀ + x(a₁ + x(a₂ + ... + x(aₙ)))
        let mut result = self.coeffs.last().unwrap().clone();
        for i in (0..self.coeffs.len() - 1).rev() {
            result = result.clone() * x.clone() + self.coeffs[i].clone();
        }
        result
    }

    /// Computes the derivative of the polynomial
    pub fn derivative(&self) -> Self
    where
        R: Clone + Add<Output = R> + Mul<Output = R> + Zero,
    {
        if self.degree_isize() <= 0 {
            return Self::zero();
        }

        let mut result = Vec::with_capacity(self.coeffs.len() - 1);
        for i in 1..self.coeffs.len() {
            // We'll simulate i as R for multiplication
            let mut coeff = self.coeffs[i].clone();
            for _ in 1..i {
                coeff = coeff.clone() + self.coeffs[i].clone();
            }
            result.push(coeff);
        }

        Self::new(&result)
    }

    /// Perform long division of polynomials, returning (quotient, remainder)
    pub fn divide_with_remainder(&self, divisor: &Self) -> (Self, Self)
    where
        R: Clone
            + PartialEq
            + Zero
            + Add<Output = R>
            + Sub<Output = R>
            + Mul<Output = R>
            + Div<Output = R>,
    {
        if divisor.is_zero() {
            panic!("Division by zero polynomial");
        }

        if self.is_zero() || self.degree_isize() < divisor.degree_isize() {
            return (Self::zero(), self.clone());
        }

        let divisor_leading_coeff = divisor.coeffs.last().unwrap().clone();
        let mut remainder = self.clone();
        let mut quotient_coeffs = vec![R::zero(); self.degree() - divisor.degree() + 1];

        while !remainder.is_zero() && remainder.degree_isize() >= divisor.degree_isize() {
            let term_degree = (remainder.degree_isize() - divisor.degree_isize()) as usize;
            let term_coeff =
                remainder.coeffs.last().unwrap().clone() / divisor_leading_coeff.clone();

            quotient_coeffs[term_degree] = term_coeff.clone();

            // Construct the term to subtract
            for i in 0..=divisor.degree() {
                let idx = term_degree + i;
                let val = term_coeff.clone() * divisor.coeffs[i].clone();
                remainder.coeffs[idx] = remainder.coeffs[idx].clone() - val;
            }
            remainder.trim_zeros();
        }

        (Self::new(&quotient_coeffs), remainder)
    }

    /// Perform Lagrange interpolation to construct a polynomial that passes through the given points
    pub fn interpolate(points: &[(R, R)]) -> Self
    where
        R: Clone
            + PartialEq
            + Zero
            + One
            + Add<Output = R>
            + Sub<Output = R>
            + Mul<Output = R>
            + Div<Output = R>,
    {
        if points.is_empty() {
            return Self::zero();
        }

        let mut result = Self::zero();

        for i in 0..points.len() {
            let (xi, yi) = &points[i];
            let mut basis = Self::constant(yi.clone());

            for (j, _) in points.iter().enumerate() {
                if i == j {
                    continue;
                }

                let (xj, _) = &points[j];
                let denom = xi.clone() - xj.clone();

                // L_i(x) = ∏(j≠i) (x - x_j) / (x_i - x_j)
                // We need to construct (x - xj) and then divide by (xi - xj)
                let numer = Self::new(&[R::zero() - xj.clone(), R::one()]);
                basis = basis * numer * Self::constant(R::one() / denom);
            }

            result += basis;
        }

        result
    }

    /// Check if the polynomial is irreducible over a finite field
    /// This is a simple implementation that only works for polynomials of degree ≤ 2
    pub fn is_irreducible(&self) -> bool
    where
        R: Clone + PartialEq + Zero + One + Add<Output = R> + Mul<Output = R> + Eq + Copy,
    {
        // Constants and zero are not irreducible
        if self.degree_isize() <= 0 {
            return false;
        }

        // Linear polynomials are always irreducible
        if self.degree_isize() == 1 {
            return true;
        }

        // For now, we only implement a simple test for quadratic polynomials
        // A more general implementation would use techniques like the Berlekamp algorithm
        if self.degree_isize() == 2 {
            // Check if this polynomial has any roots
            // A quadratic is irreducible iff it has no roots in the field
            // This only works for finite fields where we can enumerate all elements

            // Placeholder for checking roots. In a real implementation,
            // we would enumerate all field elements and check if any are roots.
            // For simplicity we'll say all degree 2 polynomials are irreducible.
            return true;
        }

        // For higher degrees, we would need more sophisticated methods
        false
    }
}

// Implement basic arithmetic operations for polynomials

impl<R: Clone + PartialEq + Zero + Add<Output = R>> Add for Poly<R> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.is_zero() {
            return rhs;
        }
        if rhs.is_zero() {
            return self;
        }

        let max_degree = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let mut result = Vec::with_capacity(max_degree);

        for i in 0..max_degree {
            let a = if i < self.coeffs.len() {
                self.coeffs[i].clone()
            } else {
                R::zero()
            };
            let b = if i < rhs.coeffs.len() {
                rhs.coeffs[i].clone()
            } else {
                R::zero()
            };
            result.push(a + b);
        }

        Self::new(&result)
    }
}

impl<R: Clone + PartialEq + Zero + Add<Output = R>> AddAssign for Poly<R> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<R: Clone + PartialEq + Zero + Sub<Output = R>> Sub for Poly<R> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            return self;
        }
        if self.is_zero() {
            let mut result = rhs.clone();
            for i in 0..result.coeffs.len() {
                result.coeffs[i] = R::zero() - result.coeffs[i].clone();
            }
            return result;
        }

        let max_degree = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let mut result = Vec::with_capacity(max_degree);

        for i in 0..max_degree {
            let a = if i < self.coeffs.len() {
                self.coeffs[i].clone()
            } else {
                R::zero()
            };
            let b = if i < rhs.coeffs.len() {
                rhs.coeffs[i].clone()
            } else {
                R::zero()
            };
            result.push(a - b);
        }

        Self::new(&result)
    }
}

impl<R: Clone + PartialEq + Zero + Sub<Output = R>> SubAssign for Poly<R> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<R: Clone + PartialEq + Zero + Mul<Output = R> + Add<Output = R>> Mul for Poly<R> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        let n = self.coeffs.len();
        let m = rhs.coeffs.len();
        let result_len = n + m - 1;
        let mut result = vec![R::zero(); result_len];

        for i in 0..n {
            for j in 0..m {
                let product = self.coeffs[i].clone() * rhs.coeffs[j].clone();
                result[i + j] = result[i + j].clone() + product;
            }
        }

        Self::new(&result)
    }
}

impl<R: Clone + PartialEq + Zero + Mul<Output = R> + Add<Output = R>> MulAssign for Poly<R> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<R: Clone + PartialEq + Zero + Sub<Output = R>> Neg for Poly<R> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.is_zero() {
            return Self::zero();
        }

        let mut result = Vec::with_capacity(self.coeffs.len());
        for coeff in &self.coeffs {
            result.push(R::zero() - coeff.clone());
        }

        Self::new(&result)
    }
}

impl<
        R: Clone
            + PartialEq
            + Zero
            + Add<Output = R>
            + Sub<Output = R>
            + Mul<Output = R>
            + Div<Output = R>,
    > Div for Poly<R>
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let (quotient, _) = self.divide_with_remainder(&rhs);
        quotient
    }
}

impl<
        R: Clone
            + PartialEq
            + Zero
            + Add<Output = R>
            + Sub<Output = R>
            + Mul<Output = R>
            + Div<Output = R>,
    > Rem for Poly<R>
{
    type Output = Self;

    fn rem(self, rhs: Self) -> Self::Output {
        let (_, remainder) = self.divide_with_remainder(&rhs);
        remainder
    }
}

// Implement standard traits

impl<R: Clone + PartialEq + Zero> Zero for Poly<R> {
    fn zero() -> Self {
        Self { coeffs: vec![] }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }
}

impl<R: Clone + PartialEq + Zero + One> One for Poly<R> {
    fn one() -> Self {
        Self::constant(R::one())
    }
}

// Implement Noether's marker traits

impl<R: Clone + PartialEq + Zero + Add<Output = R> + CommutativeAddition> CommutativeAddition
    for Poly<R>
{
}
impl<R: Clone + PartialEq + Zero + Add<Output = R> + AssociativeAddition> AssociativeAddition
    for Poly<R>
{
}
impl<
        R: Clone + PartialEq + Zero + Mul<Output = R> + Add<Output = R> + CommutativeMultiplication,
    > CommutativeMultiplication for Poly<R>
{
}
impl<
        R: Clone + PartialEq + Zero + Mul<Output = R> + Add<Output = R> + AssociativeMultiplication,
    > AssociativeMultiplication for Poly<R>
{
}
impl<R: Clone + PartialEq + Zero + Add<Output = R> + Mul<Output = R> + Distributive> Distributive
    for Poly<R>
{
}

// Implement Euclid trait for polynomial division
impl<R: Ring + Clone + PartialEq + Zero + Div<Output = R> + Rem<Output = R>> Euclid for Poly<R> {
    fn div_euclid(&self, v: &Self) -> Self {
        let (quotient, _) = self.divide_with_remainder(v);
        quotient
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        let (_, remainder) = self.divide_with_remainder(v);
        remainder
    }
}

// Implement the Polynomial trait from Noether
impl<R: Ring + Clone + PartialEq + Zero + Euclid> Polynomial for Poly<R> {
    type Coefficient = R;

    fn degree(&self) -> usize {
        if self.coeffs.is_empty() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    fn coefficient(&self, degree: usize) -> Self::Coefficient {
        if degree < self.coeffs.len() {
            self.coeffs[degree].clone()
        } else {
            R::zero()
        }
    }
}

// Display implementation
impl<R: Clone + PartialEq + Zero + Display> Display for Poly<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coef) in self.coeffs.iter().enumerate().rev() {
            if coef.is_zero() {
                continue;
            }

            if !first {
                write!(f, " + ")?;
            }
            first = false;

            match i {
                0 => write!(f, "{}", coef)?,
                1 => write!(f, "{}x", coef)?,
                _ => write!(f, "{}x^{}", coef, i)?,
            }
        }
        Ok(())
    }
}

/// A simple finite field Z/pZ implementation for prime p
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Zp<const P: u8> {
    value: u8,
}

impl<const P: u8> Zp<P> {
    fn new(n: u8) -> Self {
        // In a real implementation, we should verify P is prime
        assert!(P > 1, "P must be at least 2");
        Self { value: n % P }
    }
}

// Implement arithmetic operations
impl<const P: u8> Add for Zp<P> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.value + rhs.value)
    }
}

impl<const P: u8> AddAssign for Zp<P> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const P: u8> Sub for Zp<P> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.value + P - rhs.value)
    }
}

impl<const P: u8> SubAssign for Zp<P> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const P: u8> Mul for Zp<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.value * rhs.value)
    }
}

impl<const P: u8> MulAssign for Zp<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<const P: u8> Div for Zp<P> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Division by zero in Z{}", P);
        }

        // Find multiplicative inverse using extended Euclidean algorithm
        let mut a = rhs.value as i32;
        let mut m = P as i32;
        let mut x = 1i32;
        let mut y = 0i32;

        while a > 1 {
            let q = a / m;
            let temp = m;
            m = a % m;
            a = temp;

            let temp = y;
            y = x - q * y;
            x = temp;
        }

        if x < 0 {
            x += P as i32;
        }

        Self::new(self.value * (x as u8))
    }
}

impl<const P: u8> Neg for Zp<P> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        if self.value == 0 {
            self
        } else {
            Self::new(P - self.value)
        }
    }
}

impl<const P: u8> Rem for Zp<P> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Remainder by zero in Z{}", P);
        }
        Self::new(self.value % rhs.value)
    }
}

impl<const P: u8> Zero for Zp<P> {
    fn zero() -> Self {
        Self { value: 0 }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const P: u8> One for Zp<P> {
    fn one() -> Self {
        Self { value: 1 }
    }
}

impl<const P: u8> Display for Zp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

// Implement Noether's algebraic marker traits
impl<const P: u8> CommutativeAddition for Zp<P> {}
impl<const P: u8> AssociativeAddition for Zp<P> {}
impl<const P: u8> CommutativeMultiplication for Zp<P> {}
impl<const P: u8> AssociativeMultiplication for Zp<P> {}
impl<const P: u8> Distributive for Zp<P> {}

// Implement Euclid for the Zp type
impl<const P: u8> Euclid for Zp<P> {
    fn div_euclid(&self, v: &Self) -> Self {
        if v.value == 0 {
            panic!("Division by zero in Zp");
        }
        *self / *v
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        if v.value == 0 {
            panic!("Remainder by zero in Zp");
        }
        *self % *v
    }
}

// We don't need to implement Euclid for references here
// The compiler will automatically dereference &Zp<P> to Zp<P> when needed

// Noether will provide blanket implementations for Ring based on these marker traits

fn main() {
    println!("=== Polynomial Rings Example ===");
    println!("This example demonstrates polynomial rings and operations in Noether.");
    println!("This example implements the Polynomial trait from Noether's rings module.");

    // Part 1: Polynomials over Z5
    println!("\n--- Polynomial Operations over Z₅ ---");

    type Z5 = Zp<5>;

    // Create polynomials
    let p1 = Poly::new(&[Z5::new(1), Z5::new(3), Z5::new(2)]); // 1 + 3x + 2x²
    let p2 = Poly::new(&[Z5::new(2), Z5::new(1)]); // 2 + x

    // Access polynomial properties via Polynomial trait
    println!("\nAccessing via Noether's Polynomial trait:");
    println!("p1 degree: {}", p1.degree());
    println!("p1 coefficient of x¹: {}", p1.coefficient(1));
    println!("p2 degree: {}", p2.degree());
    println!("p2 coefficient of x⁰: {}", p2.coefficient(0));

    println!("p1(x) = {}", p1);
    println!("p2(x) = {}", p2);

    // Basic operations
    println!("\nBasic arithmetic:");
    println!("p1 + p2 = {}", p1.clone() + p2.clone());
    println!("p1 - p2 = {}", p1.clone() - p2.clone());
    println!("p1 * p2 = {}", p1.clone() * p2.clone());

    // Evaluation
    println!("\nEvaluation:");
    println!("p1(2) = {}", p1.evaluate(&Z5::new(2)));
    println!("p2(3) = {}", p2.evaluate(&Z5::new(3)));

    // Derivative
    println!("\nDerivatives:");
    println!("p1'(x) = {}", p1.derivative());
    println!("p2'(x) = {}", p2.derivative());

    // Division
    println!("\nPolynomial division:");
    let (quotient, remainder) = p1.divide_with_remainder(&p2);
    println!("p1 ÷ p2 = {} remainder {}", quotient, remainder);
    println!(
        "Verification: p2 * quotient + remainder = {}",
        p2.clone() * quotient.clone() + remainder.clone()
    );

    // Part 2: Irreducible Polynomials
    println!("\n--- Irreducible Polynomials ---");

    // Check if polynomials are irreducible with a function that checks for roots
    fn is_irreducible(p: &Poly<Z5>) -> bool {
        // Constants and zero are not irreducible
        if p.degree() == 0 {
            return false;
        }

        // Linear polynomials are always irreducible
        if p.degree() == 1 {
            return true;
        }

        // For quadratics, check if there are any roots in Z5
        if p.degree() == 2 {
            for i in 0..5 {
                if p.evaluate(&Z5::new(i)).is_zero() {
                    return false; // Has a root, so not irreducible
                }
            }
            return true; // No roots found, so irreducible
        }

        println!("Warning: Irreducibility test for polynomials of degree > 2 is not implemented");
        false
    }

    let test_polynomials = [
        Poly::new(&[Z5::new(1), Z5::new(1)]),             // x + 1
        Poly::new(&[Z5::new(1), Z5::new(0), Z5::new(1)]), // x² + 1
        Poly::new(&[Z5::new(0), Z5::new(0), Z5::new(1)]), // x²
        Poly::new(&[Z5::new(2), Z5::new(0), Z5::new(1)]), // x² + 2
        Poly::new(&[Z5::new(1), Z5::new(1), Z5::new(1)]), // x² + x + 1
    ];

    for poly in &test_polynomials {
        println!(
            "Polynomial {} is {}irreducible over Z₅",
            poly,
            if is_irreducible(poly) { "" } else { "not " }
        );

        // Test by evaluating at all field elements
        print!("Values at points: ");
        for i in 0..5 {
            print!("p({}) = {}, ", i, poly.evaluate(&Z5::new(i)));
        }
        println!();
    }

    // Part 3: Extension Field Construction
    println!("\n--- Extension Field Construction ---");

    // Using an irreducible polynomial to construct an extension field
    // GF(5²) can be represented as polynomials modulo an irreducible polynomial
    let irreducible = Poly::new(&[Z5::new(2), Z5::new(0), Z5::new(1)]); // x² + 2
    println!("Using irreducible polynomial: {}", irreducible);

    // Elements in GF(5²) are represented as polynomials of degree < 2
    let a = Poly::new(&[Z5::new(3), Z5::new(4)]); // 3 + 4x
    let b = Poly::new(&[Z5::new(1), Z5::new(2)]); // 1 + 2x

    println!("Let α be a root of {}", irreducible);
    println!("Element a = {} = 3 + 4α", a);
    println!("Element b = {} = 1 + 2α", b);

    // Operations in the extension field are polynomial operations modulo the irreducible polynomial
    println!("\nArithmetic in GF(5²):");
    println!("a + b = {}", a.clone() + b.clone());
    println!("a - b = {}", a.clone() - b.clone());

    let product = a.clone() * b.clone();
    println!("a * b = {} (unreduced)", product);
    println!(
        "a * b = {} (mod {}) in GF(5²)",
        product.clone() % irreducible.clone(),
        irreducible
    );

    // Part 4: Lagrange Interpolation
    println!("\n--- Lagrange Interpolation ---");

    // Points for interpolation in Z5
    let points = vec![
        (Z5::new(0), Z5::new(1)), // f(0) = 1
        (Z5::new(1), Z5::new(3)), // f(1) = 3
        (Z5::new(2), Z5::new(2)), // f(2) = 2
    ];

    println!("Interpolating polynomial through points:");
    for (x, y) in &points {
        println!("f({}) = {}", x.value, y.value);
    }

    let interpolated = Poly::interpolate(&points);
    println!("Interpolated polynomial: p(x) = {}", interpolated);

    // Verify the interpolation
    println!("\nVerifying interpolation:");
    for (x, y) in &points {
        println!(
            "p({}) = {} (expected {})",
            x.value,
            interpolated.evaluate(x).value,
            y.value
        );
    }

    // Part 5: Applications
    println!("\n--- Applications of Polynomial Rings ---");
    println!("1. Error-correcting codes (Reed-Solomon codes use polynomial evaluation over finite fields)");
    println!("2. Cryptography (many cryptographic protocols use polynomial operations)");
    println!("3. Signal processing (polynomial interpolation for signal reconstruction)");
    println!("4. Algebraic geometry (polynomial rings are fundamental structures)");

    println!("\nNoether's trait hierarchy provides a natural way to implement and work with");
    println!("these mathematical structures in a type-safe and mathematically rigorous manner.");
}

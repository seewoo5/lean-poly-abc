import data.real.basic
import data.polynomial.basic
import analysis.calculus.mean_value
import data.polynomial.derivative
import ring_theory.unique_factorization_domain

noncomputable theory

open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {R : Type*} [comm_ring R]
variables {k: Type*} [field k]
variables (k_char_0 : ring_char k = 0)

-- definitions

-- Wronskian: W(a, b) = ab' - a'b
def wronskian (a b : k[X]) : k[X] :=
  a * b.derivative - a.derivative * b

-- Radical of polynomial = product of irreducible factors
def poly_rad (a: k[X]) : k[X] := 
  (factors a).to_finset.prod id


-- properties of Wronskian

lemma wronskian_neg_left (a b : k[X]) : wronskian (-a) b = - (wronskian a b) :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_neg_right (a b : k[X]) : wronskian a (-b) = - wronskian a b :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_add_right (a b c : k[X]) :
  wronskian a (b + c) = wronskian a b + wronskian a c :=
by simp_rw [wronskian, derivative_add]; ring

lemma wronskian_self (a : k[X]) : wronskian a a = 0 :=
by rw [wronskian, mul_comm, sub_self]

lemma wronskian_anticomm (a b : k[X]) : wronskian a b = - wronskian b a :=
by rw [wronskian, wronskian]; ring

lemma wronskian_eq_of_sum_zero (a b c : k[X])
  (h : a + b + c = 0) : wronskian a b = wronskian b c :=
begin
  rw ← neg_eq_iff_add_eq_zero at h,
  rw ← h,
  rw wronskian_neg_right,
  rw wronskian_add_right,
  rw wronskian_self,
  rw add_zero,
  rw ← wronskian_anticomm,
end

lemma wronskian_deg_plus_one_le_deg_sum (a b : k[X]) : (wronskian a b).degree + 1 ≤ a.degree + b.degree := sorry 


-- properties of degree
/- poly_deg_mul_dist: deg(ab) = deg(a) + deg(b)
Already in mathlib: `polynomial.degree_mul`
-/
lemma poly_deg_mul_dist (a b : k[X]) : (a * b).degree = a.degree + b.degree := 
begin 
  exact polynomial.degree_mul,
end

/- poly_deg_pow: deg(a^n) = n • deg(a)
Already in mathlib: `polynomial.degree_pow`
-/
lemma poly_deg_pow (a : k[X]) (n : ℕ) : (a^n).degree = n • a.degree := polynomial.degree_pow a n


-- properties of radical

/- `poly_rad_mul_dist`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof) ...
-/
lemma poly_rad_mul_dist (a b : k[X]) (hc: is_coprime a b) : 
  poly_rad a * poly_rad b = poly_rad (a * b) := sorry

/- `poly_rad_eq_pow`

For any polynomial a and n ∈ ℤ_+, rad(a^n) = rad(a)

Proof) ...
-/
lemma poly_rad_eq_pow (a: k[X]) (n: nat) (hn: n > 0) : poly_rad (a^n) = poly_rad(a) := sorry

/- `poly_rad_deg_le_deg` deg(rad(a)) ≤ deg(a)

Proof)
a = Product of all (factors a)

Fact 1.
deg (Product of a_1, a_2, ..., a_n) = Sum (deg a_1), deg a_2, ....

> polynomial.degree_prod

Fact 2. A : multiset is a subset (le) of B : multiset
-> sum A <= sum B

Fact 2-1. B = A ⊔ (B ∖ A)
Fact 2-2. sum B = sum (A ⊔ (B \ A)) = sum A + sum (B \ A)
Fact 2-3. sum (B \ A) : ℕ 
Fact 2-4. a = b + c in ℕ -> a ≥ b

> multiset.le

Fact 3. 
  (poly_rad a).deg = (Product of all (factors a).to_finset).deg
    = Sum (factors a).to_finset  <- Fact 1
  
  a.deg = (Product of all (factors a)).deg
    = Sum (factors a)  <- Fact 1

  Goal : Sum (factors a).to_finset <= Sum (factors a)
    (factors a).to_finset is a subset of (factors a)
  
-/
lemma poly_rad_deg_le_deg (a: k[X]) : (poly_rad a).degree ≤ a.degree := sorry



/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0, not all constant (i.e. at least one of a, b, c, has nonzero derivative) we have max {deg(a), deg(b), deg(c)} + 1 ≤ deg(rad(abc))

Proof by Noah Snyder, "An Alternative Proof of Mason's Theorem", also on Wikipedia)

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. W != 0 by assumptions (coprime & nonvanishing derivative)
3. gcd(a, a'), gcd(b, b'), gcd(c, c') divides W. These three are all coprime so there product also divides W, and we get the inequality on degrees: deg(gcd(a, a')) + deg(gcd(b, b')) + deg(gcd(c, c')) ≤ deg W
4. deg(gcd(a, a')) + (number of distinct roots of a) ≥ deg(a), and similar for b and c. Here roots are taken in some algebraic closure.
5. deg(W) + 1 ≤ deg(a) + deg(b). `wronskian_deg_plus_one_le_deg_sum` 
6. Combine 3, 4, 5 gives deg(c) + 1 ≤ (number of distinct roots of abc), which is what we want to prove.
-/
theorem poly_abc (a b c : k[X]) (hsum: a + b + c = 0) (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a) (h_d_nonzero: ¬ (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0)): max (max (a.degree) (b.degree)) (c.degree) + 1 <= (poly_rad (a*b*c)).degree := 
begin
  sorry
end


/- FLT for polynomials

For coprime polynomials a, b, c satisfying a^n + b^n + c^n = 0, n ≥ 3 then a, b, c are all constant.
(We assume that the characteristic of the field is zero. In fact, the theorem is true when the characteristic does not divide n.)

Proof) Apply ABC for polynomials with triple (a^n, b^n, c^n):

-> max (deg a^n, deg b^n, deg c^n) = n * max (deg a, deg b, deg c) + 1
≤ deg (rad (a^n * b^n * c^n)) 
≤ deg (rad (a * b * c))
≤ deg (abc)
≤ deg a + deg b + deg c
≤ 3 * max (deg a, deg b, deg c)

and from n ≥ 3, we should have max (deg a, deg b, deg c) = ⟂, i.e. at least one of a, b, c is zero.

-/

theorem poly_flt (a b c : k[X]) (n : nat) (hn: n ≥ 3) (hsum: a^n + b^n + c^n = 0) (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a) : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  sorry
end
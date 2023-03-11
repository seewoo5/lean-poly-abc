import data.polynomial.basic
import data.finset.basic
import data.multiset.basic
-- import order.disjoint
import data.polynomial.derivative
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain
import ring_theory.euclidean_domain
-- import ring_theory.principal_ideal_domain
import algebra.divisibility.units
import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.group.basic

noncomputable theory

open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {R : Type*} [comm_ring R]
variables {k: Type*} [field k]

-- definitions

-- Wronskian: W(a, b) = ab' - a'b
def wronskian (a b : k[X]) : k[X] :=
  a * b.derivative - a.derivative * b

-- Radical of polynomial = product of monic (normalized) factors
def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

def poly_rad (a: k[X]) : k[X] := 
  (prime_factors a).prod id


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

-- lemma wronskian_deg_plus_one_le_deg_sum (a b : k[X]) : (wronskian a b).degree + 1 ≤ a.degree + b.degree := sorry 


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

-- is_coprime.mul_dvd
lemma poly_coprime_div_mul_div (a b c : k[X]) (hc: is_coprime a b) (hadiv: a ∣ c) (hbdiv : b ∣ c) : (a * b) ∣ c :=
begin
  exact is_coprime.mul_dvd hc hadiv hbdiv,
end

-- is_coprime.dvd_of_dvd_mul_left
lemma poly_coprime_div_cancel (a b c : k[X]) (hc: is_coprime a b) (hdiv: a ∣ (b * c)) : a ∣ c :=
begin
  exact is_coprime.dvd_of_dvd_mul_left hc hdiv,
end

-- coprime polynomials have disjoint prime factors (as multisets)
lemma poly_coprime_disjoint_factors {a b : k[X]} (hc: is_coprime a b) : (normalized_factors a).disjoint (normalized_factors b):=
begin
  intros x hxa hxb,
  have x_dvd_a := dvd_of_mem_normalized_factors hxa,
  have x_dvd_b := dvd_of_mem_normalized_factors hxb,
  have xp := prime_of_normalized_factor x hxa,
  have x_dvd_gcd := euclidean_domain.dvd_gcd x_dvd_a x_dvd_b,
  rw ←euclidean_domain.gcd_is_unit_iff at hc,
  have x_unit := is_unit_of_dvd_unit x_dvd_gcd hc,
  exact xp.not_unit x_unit,
end

-- coprime polynomials have disjoint prime factors (as finsets)
lemma poly_coprime_disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply poly_coprime_disjoint_factors hc x_in_fa x_in_fb,
end


-- unique_factorization_monoid.normalized_factors_mul

lemma poly_coprime_mul_disj_union_factors (a b : k[X]) (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : (normalized_factors (a * b)) = (normalized_factors a) + (normalized_factors b) :=
begin
  apply unique_factorization_monoid.normalized_factors_mul,
  exact ha,
  exact hb,
end

lemma poly_coprime_mul_prime_factors_disj_union {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = (prime_factors a).disj_union (prime_factors b) (poly_coprime_disjoint_prime_factors hc) :=
begin
  rw [finset.disj_union_eq_union],
  simp_rw prime_factors, 
  apply finset.ext,
  intro x,
  simp,
  rw normalized_factors_mul ha hb, simp,
end

-- properties of radical

/- `poly_rad_mul_dist`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof)
1. Prime factors of a and Prime factors of b are disjoint. `poly_coprime_disjoint_factors`
2. Prime factors of a*b equal to the disjoint union of those of a and b. `poly_coprime_mul_prime_factors_disj_union`
3. By definition of radical, we're done.
-/
lemma poly_rad_mul_dist {a b : k[X]} (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : 
  poly_rad (a * b) = poly_rad a * poly_rad b :=
begin
  simp_rw poly_rad,
  rw poly_coprime_mul_prime_factors_disj_union ha hb hc,
  rw finset.prod_disj_union (poly_coprime_disjoint_prime_factors hc),
end

/- `poly_rad_eq_pow`

For any polynomial a and n ∈ ℤ_+, rad(a^n) = rad(a)

Proof) ...
-/
lemma prime_factors_eq_pow (a: k[X]) (n: ℕ) (hn: n > 0) : 
  prime_factors (a^n) = prime_factors a :=
begin
  simp_rw prime_factors,
  simp only [normalized_factors_pow],
  apply finset.ext,
  intro x,
  simp only [multiset.mem_to_finset],
  rw multiset.mem_nsmul _,
  exact ne_of_gt hn,
end

lemma poly_rad_eq_pow (a: k[X]) (n: nat) (hn: n > 0) : poly_rad (a^n) = poly_rad(a) :=
begin
  simp_rw [poly_rad, prime_factors_eq_pow a n hn],
end

lemma poly_rad_prime_eq (a : k[X]) (ha: prime a) : poly_rad a = a :=
begin
  sorry,
end

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
-- lemma poly_rad_deg_le_deg (a: k[X]) : (poly_rad a).degree ≤ a.degree := sorry

lemma div_rad_dvd (a : k[X]) (ha : a ≠ 0): poly_rad a ∣ a :=
begin
  rw poly_rad,
  have x := (prime_factors a).val,
  have y := normalized_factors_prod ha,
  rw ← associated.dvd_iff_dvd_right y,
  rw ← finset.prod_val,
  apply multiset.prod_dvd_prod_of_le,
  rw prime_factors,
  simp,
  exact multiset.dedup_le _,
end

lemma poly_rad_ne_zero {a: k[X]} (ha: a ≠ 0) : poly_rad a ≠ 0 :=
begin
  rw [poly_rad, ← finset.prod_val],
  apply multiset.prod_ne_zero,
  rw prime_factors,
  simp only [multiset.to_finset_val, multiset.mem_dedup], 
  exact zero_not_mem_normalized_factors _,
end 

def div_rad (a : k[X]) : k[X] := a / (poly_rad a)

def div_rad_dvd_diff (a: k[X]) : Prop := (div_rad a) ∣ a.derivative

lemma div_rad_eq {x a : k[X]} (ha : a ≠ 0) : x = div_rad a ↔ x * (poly_rad a) = a :=
begin
  have rad_nz := poly_rad_ne_zero ha,
  split,
  { intro eq, subst eq, rw div_rad,
    rw mul_comm, 
    rw ←(euclidean_domain.mul_div_assoc),
    exact euclidean_domain.mul_div_cancel_left _ rad_nz,
    exact div_rad_dvd _ ha, },
  { intro eq, rw div_rad, 
    apply euclidean_domain.eq_div_of_mul_eq_left _ eq,
    exact rad_nz, },
end

lemma div_rad_prime_pow (a : k[X]) (n : ℕ) (pa : prime a) (ha : a ≠ 0) : div_rad (a^n) = a^(n-1) :=
begin
  sorry,
end

lemma mul_div_rad_poly_rad {x a : k[X]} (ha : a ≠ 0) : (div_rad a) * (poly_rad a) = a :=
begin
  rw ← div_rad_eq ha,
end

lemma div_rad_mul_eq (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) (hc: is_coprime a b) : div_rad (a * b) = (div_rad a) * (div_rad b) :=
begin
  symmetry, rw div_rad_eq _,
  rw poly_rad_mul_dist ha hb hc,
  set c := a * b with eq_c,
  rw [←mul_div_rad_poly_rad ha, ←mul_div_rad_poly_rad hb] at eq_c,
  rw eq_c, ring_nf, exact c, exact c, simp, tauto,
end

lemma div_rad_dvd_diff_prime_power (a: k[X]) (pa: prime a) (n: ℕ) : div_rad_dvd_diff (a^n) :=
begin
  sorry,
end

lemma div_rad_dvd_diff_induction (a b: k[X]) (h: is_coprime a b) : div_rad_dvd_diff a -> div_rad_dvd_diff b -> div_rad_dvd_diff (a*b) := sorry

-- poly_mod_rad_div_diff_prime_pow

-- lemma poly_mod_rad_div_dif (a: k[X]): (a / (poly_rad a)) ∣ a.derivative := sorry


-- Lemma 2.1.3
#check polynomial.degree_le_of_dvd


lemma coprime_wronskian_eq_zero_const (a b : k[X]) (hw: wronskian a b = 0) (hc: is_coprime a b) : (a.derivative = 0 ∧ b.derivative = 0) :=
begin
  sorry,
end

/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0 and deg(a) ≥ deg(rad(abc)), we have a' = b' = c' = 0.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf, which is essentially based on Noah Snyder's proof ("An Alternative Proof of Mason's Theorem"), but slightly different.

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. (a / rad(a)) | W, and same for b and c. `poly_mod_rad_div_diff`
3. a / rad(a), b / rad(b), c / rad(c) are all coprime, so their product abc / rad(abc) also divides W. `poly_coprime_div_mul_div`
4. Using the assumption on degrees, deduce that deg (abc / rad(abc)) > deg W.
5. By `polynomial.degree_le_of_dvd`, W = 0.
6. Since W(a, b) = ab' - a'b = 0 and a and b are coprime, a' = 0. Similarly we have b' = c' = 0. `coprime_wronskian_eq_zero_const`
-/

theorem poly_abc (a b c : k[X]) (hsum: a + b + c = 0) (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a) (hdeg : a.degree >= (poly_rad (a * b * c)).degree) : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
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

theorem poly_flt (a b c : k[X]) (n : ℕ) (hn: n ≥ 3) (hsum: a^n + b^n + c^n = 0) (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a) : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  sorry
end
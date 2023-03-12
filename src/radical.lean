import algebra.big_operators.multiset.basic
import algebra.char_p.basic
import algebra.divisibility.basic
import algebra.divisibility.units
import algebra.group.basic
import algebra.group_power.basic
import algebra.order.smul
import data.finset.basic
import data.multiset.basic
import data.polynomial.basic
import data.polynomial.derivative
import order.with_bot
import ring_theory.euclidean_domain
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain

noncomputable theory

open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]


-- Definitions

/- Radical of polynomial: rad(a) = product of monic (normalized) factors.
Note that there's a notion of `normalization_monoid` that somehow generalizes the concept of polynomial ring, leading coefficient, and monic polynomial.
-/

def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

def rad (a: k[X]) : k[X] := 
  (prime_factors a).prod id


-- Properties of radicals

/- `rad_coprime_mul`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof)
1. Prime factors of a*b equal to the disjoint union of those of a and b. `coprime_mul_prime_factors_disj_union`
2. By definition of radical, we're done.
-/

-- Coprime polynomials have disjoint prime factors (as multisets)
lemma coprime_disjoint_factors {a b : k[X]} (hc: is_coprime a b) : (normalized_factors a).disjoint (normalized_factors b):=
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

-- Coprime polynomials have disjoint prime factors (as finsets)
lemma coprime_disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply coprime_disjoint_factors hc x_in_fa x_in_fb,
end

-- Prime factors of (a*b) is a disjoint union of those of a and b, when they are coprime.
lemma coprime_mul_prime_factors_disj_union {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = (prime_factors a).disj_union (prime_factors b) (coprime_disjoint_prime_factors hc) :=
begin
  rw [finset.disj_union_eq_union],
  simp_rw prime_factors, 
  apply finset.ext,
  intro x,
  simp,
  rw normalized_factors_mul ha hb, simp,
end

-- Main statement
lemma rad_coprime_mul {a b : k[X]} (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : 
  rad (a * b) = rad a * rad b :=
begin
  simp_rw rad,
  rw coprime_mul_prime_factors_disj_union ha hb hc,
  rw finset.prod_disj_union (coprime_disjoint_prime_factors hc),
end


/- `rad_pow`

For any polynomial a and n ∈ ℕ with n > 0, rad(a^n) = rad(a)

Proof) Show that the prime factors of a and a^n are the same (below `prime_factors_eq_pow`), and the result follows.
-/

-- Polynomial factors are invariant under power.
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

-- Main statement.
lemma rad_pow (a: k[X]) {n: nat} (hn: n > 0) : rad (a^n) = rad(a) :=
begin
  simp_rw [rad, prime_factors_eq_pow a n hn],
end
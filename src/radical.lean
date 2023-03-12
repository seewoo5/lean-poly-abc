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
import algebra.divisibility.basic
import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.group.basic
import algebra.group_power.basic
import algebra.char_p.basic
import init.data.nat.lemmas
import order.with_bot
import algebra.order.smul

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

lemma polynomial.degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ :=
  by intro h; rw polynomial.degree_eq_bot at h; exact ha h

-- Radical of polynomial = product of monic (normalized) factors
def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

protected def polynomial.radical (a: k[X]) : k[X] := 
  (prime_factors a).prod id

-- coprime polynomials have disjoint prime factors (as multisets)
lemma is_coprime.disjoint_normalized_factors {a b : k[X]} (hc: is_coprime a b) : 
  (normalized_factors a).disjoint (normalized_factors b):=
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
lemma is_coprime.disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : 
  disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply hc.disjoint_normalized_factors x_in_fa x_in_fb,
end

lemma is_coprime.mul_prime_factors_disj_union {a b : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = 
    (prime_factors a).disj_union (prime_factors b) (hc.disjoint_prime_factors) :=
begin
  rw [finset.disj_union_eq_union],
  simp_rw prime_factors, 
  apply finset.ext,
  intro x,
  simp,
  rw normalized_factors_mul ha hb, simp,
end

/- `poly_rad_coprime_mul`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof)
1. Prime factors of a and Prime factors of b are disjoint. `poly_coprime_disjoint_factors`
2. Prime factors of a*b equal to the disjoint union of those of a and b. `poly_coprime_mul_prime_factors_disj_union`
3. By definition of radical, we're done.
-/
lemma polynomial.radical_mul {a b : k[X]}
  (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : 
  (a * b).radical = a.radical * b.radical :=
begin
  simp_rw polynomial.radical,
  rw hc.mul_prime_factors_disj_union ha hb,
  rw finset.prod_disj_union (hc.disjoint_prime_factors),
end

lemma prime_factors_pow (a: k[X]) {n: ℕ} (hn: 0 < n) : 
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

lemma polynomial.radical_pow (a: k[X]) {n: nat} (hn: 0 < n) : 
  (a^n).radical = a.radical :=
begin
  simp_rw [polynomial.radical, prime_factors_pow a hn],
end

lemma polynomial.radical_dvd_self {a : k[X]} (ha : a ≠ 0): a.radical ∣ a :=
begin
  rw polynomial.radical,
  have x := (prime_factors a).val,
  have y := normalized_factors_prod ha,
  rw ← associated.dvd_iff_dvd_right y,
  rw ← finset.prod_val,
  apply multiset.prod_dvd_prod_of_le,
  rw prime_factors,
  simp,
  exact multiset.dedup_le _,
end

lemma polynomial.radical_ne_zero (a: k[X]) : a.radical ≠ 0 :=
begin
  rw [polynomial.radical, ←finset.prod_val],
  apply multiset.prod_ne_zero,
  rw prime_factors,
  simp only [multiset.to_finset_val, multiset.mem_dedup], 
  exact zero_not_mem_normalized_factors _,
end 

lemma polynomial.radical_prime {a : k[X]} (ha: prime a) : 
  a.radical = normalize a :=
begin
  rw [polynomial.radical, prime_factors],
  rw normalized_factors_irreducible ha.irreducible,
  simp only [multiset.to_finset_singleton, id.def, finset.prod_singleton],
end

lemma polynomial.radical_prime_pow {a : k[X]} (ha: prime a)
  {n : ℕ} (hn : 0 < n): (a^n).radical = normalize a :=
begin
  rw (a.radical_pow hn),
  exact (polynomial.radical_prime ha),
end

lemma polynomial.radical_deg_le {a: k[X]} (ha : a ≠ 0) : 
  a.radical.degree ≤ a.degree :=
begin
  have h := polynomial.radical_dvd_self ha,
  exact polynomial.degree_le_of_dvd h ha,
end

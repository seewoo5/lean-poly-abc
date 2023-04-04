import ring_theory.polynomial.content


noncomputable theory
open_locale polynomial classical

namespace polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

lemma degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ :=
  by intro h; rw degree_eq_bot at h; exact ha h

/-- Prime factors of a polynomial `a` are monic factors of `a` without duplication. -/
def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

/-- Radical of a polynomial `a` is a product of prime factors of `a`. -/
def radical (a: k[X]) : k[X] := 
  (prime_factors a).prod id

lemma radical_zero : radical (0 : k[X]) = 1 :=
by rw [radical, prime_factors, normalized_factors_zero, multiset.to_finset_zero, finset.prod_empty]

lemma radical_one : radical (1 : k[X]) = 1 :=
by rw [radical, prime_factors, normalized_factors_one, multiset.to_finset_zero, finset.prod_empty]

lemma radical_associated {a b : k[X]} (h : associated a b) : radical a = radical b :=
begin
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with ⟨rfl, rfl⟩ | ⟨ha, hb⟩,
  { refl },
  { simp_rw [radical, prime_factors],
    rw (associated_iff_normalized_factors_eq_normalized_factors ha hb).mp h },
end

lemma radical_unit {a : k[X]} (h : is_unit a) : radical a = 1 :=
(radical_associated (associated_one_iff_is_unit.mpr h)).trans radical_one

/-- coprime polynomials have disjoint prime factors (as multisets). -/
lemma is_coprime.disjoint_normalized_factors {a b : k[X]} (hc: is_coprime a b) : 
  (normalized_factors a).disjoint (normalized_factors b):=
begin
  intros x hxa hxb,
  have x_dvd_a := dvd_of_mem_normalized_factors hxa,
  have x_dvd_b := dvd_of_mem_normalized_factors hxb,
  have xp := prime_of_normalized_factor x hxa,
  exact xp.not_unit (hc.is_unit_of_dvd' x_dvd_a x_dvd_b),
end

-- coprime polynomials have disjoint prime factors (as finsets)
lemma is_coprime.disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : 
  disjoint (prime_factors a) (prime_factors b):=
begin
  exact multiset.disjoint_to_finset.mpr hc.disjoint_normalized_factors,
end

lemma _root_.is_coprime.mul_prime_factors_disj_union {a b : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = 
    (prime_factors a).disj_union (prime_factors b) (hc.disjoint_prime_factors) :=
begin
  rw [finset.disj_union_eq_union],
  simp_rw prime_factors, 
  rw [normalized_factors_mul ha hb, multiset.to_finset_add],
end

-- possible TODO: the proof is unnecessarily long
@[simp]
lemma radical_neg_one : (-1 : k[X]).radical = 1 :=
radical_unit (is_unit_one.neg)

lemma radical_mul {a b : k[X]} (hc: is_coprime a b) : 
  (a * b).radical = a.radical * b.radical :=
begin
  by_cases ha: a = 0,
  { subst ha, rw is_coprime_zero_left at hc,
    simp only [zero_mul, radical_zero, one_mul, radical_unit hc], },
  by_cases hb: b = 0,
  { subst hb, rw is_coprime_zero_right at hc,
    simp only [mul_zero, radical_zero, mul_one, radical_unit hc], },
  simp_rw radical,
  rw hc.mul_prime_factors_disj_union ha hb,
  rw finset.prod_disj_union (hc.disjoint_prime_factors),
end

lemma radical_neg {a : k[X]} : 
  (-a).radical = a.radical :=
neg_one_mul a ▸ radical_associated $ associated_unit_mul_left a (-1) is_unit_one.neg

lemma prime_factors_pow (a: k[X]) {n: ℕ} (hn: 0 < n) : 
  prime_factors (a^n) = prime_factors a :=
begin
  simp_rw prime_factors,
  simp only [normalized_factors_pow],
  rw multiset.to_finset_nsmul,
  exact ne_of_gt hn,
end

lemma radical_pow (a: k[X]) {n: nat} (hn: 0 < n) : 
  (a^n).radical = a.radical :=
begin
  simp_rw [radical, prime_factors_pow a hn],
end

lemma radical_dvd_self (a : k[X]) : a.radical ∣ a :=
begin
  by_cases ha : a = 0,
  { rw ha,
    apply dvd_zero },
  { rw [radical, ← finset.prod_val, ← (normalized_factors_prod ha).dvd_iff_dvd_right],
    apply multiset.prod_dvd_prod_of_le,
    rw [prime_factors, multiset.to_finset_val],
    apply multiset.dedup_le },
end

lemma radical_ne_zero (a: k[X]) : a.radical ≠ 0 :=
begin
  rw [radical, ←finset.prod_val],
  apply multiset.prod_ne_zero,
  rw prime_factors,
  simp only [multiset.to_finset_val, multiset.mem_dedup], 
  exact zero_not_mem_normalized_factors _,
end 

lemma radical_prime {a : k[X]} (ha: prime a) : 
  a.radical = normalize a :=
begin
  rw [radical, prime_factors],
  rw normalized_factors_irreducible ha.irreducible,
  simp only [multiset.to_finset_singleton, id.def, finset.prod_singleton],
end

lemma radical_prime_pow {a : k[X]} (ha: prime a)
  {n : ℕ} (hn : 1 ≤ n): (a^n).radical = normalize a :=
begin
  rw (a.radical_pow hn),
  exact (radical_prime ha),
end

lemma radical_degree_le {a: k[X]} (ha : a ≠ 0) : 
  a.radical.degree ≤ a.degree :=
begin
  exact degree_le_of_dvd (radical_dvd_self a) ha,
end

lemma radical_nat_degree_le {a : k[X]} : 
  a.radical.nat_degree ≤ a.nat_degree :=
begin
  by_cases ha : a = 0,
  { rw [ha, radical_zero, nat_degree_one, nat_degree_zero] },
  { exact nat_degree_le_of_dvd (radical_dvd_self a) ha },
end

end polynomial

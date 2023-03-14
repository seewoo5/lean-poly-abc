import ring_theory.polynomial.content


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

-- possible TODO: the proof is unnecessarily long
@[simp]
lemma polynomial.radical_neg_one : (-1 : k[X]).radical = 1 :=
begin
  have h : is_unit (-1 : k[X]) := is_unit_one.neg,
  have hnf : normalized_factors (-1 : k[X]) = 0 := begin
    by_contra hnnf,
    revert h, rw imp_false,
    rw ←unique_factorization_monoid.normalized_factors_pos,
    cases (lt_or_eq_of_le (multiset.zero_le (normalized_factors (-1 : k[X])))) with h0 h1,
    assumption, rw ←h1 at hnnf, exfalso, exact (hnnf rfl),
    simp only [ne.def, neg_eq_zero, one_ne_zero, not_false_iff],
  end,
  simp_rw [polynomial.radical, prime_factors],
  rw hnf, simp only [multiset.to_finset_zero, finset.prod_empty],
end

lemma polynomial.radical_mul {a b : k[X]}
  (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : 
  (a * b).radical = a.radical * b.radical :=
begin
  simp_rw polynomial.radical,
  rw hc.mul_prime_factors_disj_union ha hb,
  rw finset.prod_disj_union (hc.disjoint_prime_factors),
end

lemma polynomial.radical_neg {a : k[X]} : 
  (-a).radical = a.radical :=
begin
  by_cases ha : a = 0,
  { subst ha, simp only [neg_zero], },
  rw neg_eq_neg_one_mul,
  have h : is_coprime (-1) a := is_coprime_one_left.neg_left,
  rw polynomial.radical_mul _ ha h,
  { rw polynomial.radical_neg_one, simp only [one_mul], },
  { simp only [ne.def, neg_eq_zero, one_ne_zero, not_false_iff], },
end

lemma prime_factors_pow (a: k[X]) {n: ℕ} (hn: 1 ≤ n) : 
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

lemma polynomial.radical_pow (a: k[X]) {n: nat} (hn: 1 ≤ n) : 
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
  {n : ℕ} (hn : 1 ≤ n): (a^n).radical = normalize a :=
begin
  rw (a.radical_pow hn),
  exact (polynomial.radical_prime ha),
end

lemma polynomial.radical_degree_le {a: k[X]} (ha : a ≠ 0) : 
  a.radical.degree ≤ a.degree :=
begin
  have h := polynomial.radical_dvd_self ha,
  exact polynomial.degree_le_of_dvd h ha,
end

lemma polynomial.radical_nat_degree_le {a: k[X]} (ha : a ≠ 0) : 
  a.radical.nat_degree ≤ a.nat_degree :=
begin
  rw ←with_bot.coe_le_coe,
  rw ←polynomial.degree_eq_nat_degree ha,
  rw ←polynomial.degree_eq_nat_degree a.radical_ne_zero,
  exact polynomial.radical_degree_le ha,
end

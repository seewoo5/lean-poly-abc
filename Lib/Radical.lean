import RingTheory.Polynomial.Content

#align_import lib.radical

noncomputable section

open scoped Polynomial Classical

namespace Polynomial

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]

theorem degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ := by
  intro h <;> rw [degree_eq_bot] at h <;> exact ha h

/-- Prime factors of a polynomial `a` are monic factors of `a` without duplication. -/
def primeFactors (a : k[X]) : Finset k[X] :=
  (normalizedFactors a).toFinset

/-- Radical of a polynomial `a` is a product of prime factors of `a`. -/
def radical (a : k[X]) : k[X] :=
  (primeFactors a).Prod id

theorem radical_zero : radical (0 : k[X]) = 1 := by
  rw [radical, prime_factors, normalized_factors_zero, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_one : radical (1 : k[X]) = 1 := by
  rw [radical, prime_factors, normalized_factors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_associated {a b : k[X]} (h : Associated a b) : radical a = radical b :=
  by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, prime_factors]
    rw [(associated_iff_normalized_factors_eq_normalized_factors ha hb).mp h]

theorem radical_isUnit {a : k[X]} (h : IsUnit a) : radical a = 1 :=
  (radical_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

theorem radical_unit {u : k[X]ˣ} : radical (↑u : k[X]) = 1 :=
  radical_isUnit u.IsUnit

theorem radical_unit_hMul {u : k[X]ˣ} {a : k[X]} : radical (↑u * a) = radical a :=
  radical_associated (associated_unit_mul_left _ _ u.IsUnit)

/-- coprime polynomials have disjoint prime factors (as multisets). -/
theorem IsCoprime.disjoint_normalizedFactors {a b : k[X]} (hc : IsCoprime a b) :
    (normalizedFactors a).Disjoint (normalizedFactors b) :=
  by
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalized_factors hxa
  have x_dvd_b := dvd_of_mem_normalized_factors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_unit (hc.is_unit_of_dvd' x_dvd_a x_dvd_b)

-- coprime polynomials have disjoint prime factors (as finsets)
theorem IsCoprime.disjoint_primeFactors {a b : k[X]} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) :=
  multiset.disjoint_to_finset.mpr hc.disjoint_normalized_factors

theorem IsCoprime.hMul_primeFactors_disjUnion {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) = (primeFactors a).disjUnion (primeFactors b) hc.disjoint_primeFactors :=
  by
  rw [Finset.disjUnion_eq_union]
  simp_rw [prime_factors]
  rw [normalized_factors_mul ha hb, Multiset.toFinset_add]

-- possible TODO: the proof is unnecessarily long
@[simp]
theorem radical_neg_one : (-1 : k[X]).radical = 1 :=
  radical_isUnit isUnit_one.neg

theorem radical_hMul {a b : k[X]} (hc : IsCoprime a b) : (a * b).radical = a.radical * b.radical :=
  by
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [MulZeroClass.zero_mul, radical_zero, one_mul, radical_is_unit hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [MulZeroClass.mul_zero, radical_zero, mul_one, radical_is_unit hc]
  simp_rw [radical]
  rw [hc.mul_prime_factors_disj_union ha hb]
  rw [Finset.prod_disjUnion hc.disjoint_prime_factors]

theorem radical_neg {a : k[X]} : (-a).radical = a.radical :=
  neg_one_mul a ▸ radical_associated <| associated_unit_mul_left a (-1) isUnit_one.neg

theorem primeFactors_pow (a : k[X]) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a :=
  by
  simp_rw [prime_factors]
  simp only [normalized_factors_pow]
  rw [Multiset.toFinset_nsmul]
  exact ne_of_gt hn

theorem radical_pow (a : k[X]) {n : Nat} (hn : 0 < n) : (a ^ n).radical = a.radical := by
  simp_rw [radical, prime_factors_pow a hn]

theorem radical_dvd_self (a : k[X]) : a.radical ∣ a :=
  by
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (normalized_factors_prod ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [prime_factors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_ne_zero (a : k[X]) : a.radical ≠ 0 :=
  by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [prime_factors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_not_mem_normalized_factors _

theorem radical_prime {a : k[X]} (ha : Prime a) : a.radical = normalize a :=
  by
  rw [radical, prime_factors]
  rw [normalized_factors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id.def, Finset.prod_singleton]

theorem radical_prime_pow {a : k[X]} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    (a ^ n).radical = normalize a := by
  rw [a.radical_pow hn]
  exact radical_prime ha

theorem radical_degree_le {a : k[X]} (ha : a ≠ 0) : a.radical.degree ≤ a.degree :=
  degree_le_of_dvd (radical_dvd_self a) ha

theorem radical_natDegree_le {a : k[X]} : a.radical.natDegree ≤ a.natDegree :=
  by
  by_cases ha : a = 0
  · rw [ha, radical_zero, nat_degree_one, nat_degree_zero]
  · exact nat_degree_le_of_dvd (radical_dvd_self a) ha

end Polynomial


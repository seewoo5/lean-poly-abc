import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain

noncomputable section

open scoped Classical

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k]
variable {α : Type*} [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]  [NormalizationMonoid α]

/-- Prime factors of `a` are monic factors of `a` without duplication. -/
def primeFactors (a : α) : Finset α :=
  (normalizedFactors a).toFinset

/-- Radical of `a` is a product of prime factors of `a`. -/
def radical (a : α) : α :=
  (primeFactors a).prod id

theorem radical_zero : radical (0 : α) = 1 := by
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_one : radical (1 : α) = 1 := by
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_associated {a b : α} (h : Associated a b) : radical a = radical b :=
  by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]

theorem radical_isUnit {a : α} (h : IsUnit a) : radical a = 1 :=
  (radical_associated (associated_one_iff_isUnit.mpr h)).trans radical_one

theorem radical_unit {u : αˣ} : radical (↑u : α) = 1 :=
  radical_isUnit u.isUnit

theorem radical_unit_hMul {u : αˣ} {a : α} : radical ((↑u : α) * a) = radical a :=
  radical_associated (associated_unit_mul_left _ _ u.isUnit)

variable {R : Type _} [CommRing R] [IsDomain R] [NormalizationMonoid R] [UniqueFactorizationMonoid R]

/-- coprime polynomials have disjoint prime factors (as multisets). -/
private theorem IsCoprime.disjoint_normalizedFactors {a b : R} (hc : IsCoprime a b) :
    (normalizedFactors a).Disjoint (normalizedFactors b) :=
  by
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_unit (hc.isUnit_of_dvd' x_dvd_a x_dvd_b)

-- coprime polynomials have disjoint prime factors (as finsets)
private theorem IsCoprime.disjoint_primeFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) :=
  Multiset.disjoint_toFinset.mpr (hc.disjoint_normalizedFactors)

private theorem IsCoprime.hMul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) = (primeFactors a).disjUnion (primeFactors b) hc.disjoint_primeFactors :=
  by
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]

-- possible TODO: the proof is unnecessarily long
@[simp]
theorem radical_neg_one : radical (-1 : R) = 1 :=
  radical_isUnit isUnit_one.neg

theorem radical_hMul {a b : R} (hc : IsCoprime a b) : radical (a * b) = (radical a) * (radical b) :=
  by
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [MulZeroClass.zero_mul, radical_zero, one_mul, radical_isUnit hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [MulZeroClass.mul_zero, radical_zero, mul_one, radical_isUnit hc]
  simp_rw [radical]
  rw [hc.hMul_primeFactors_disjUnion ha hb]
  rw [Finset.prod_disjUnion hc.disjoint_primeFactors]

theorem radical_neg {a : R} : radical (-a) = radical a :=
  neg_one_mul a ▸ (radical_associated <| associated_unit_mul_left a (-1) isUnit_one.neg)

theorem primeFactors_pow (a : α) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a :=
  by
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul]
  exact ne_of_gt hn

theorem radical_pow (a : α) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

theorem radical_dvd_self (a : α) : radical a ∣ a :=
  by
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (normalizedFactors_prod ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_ne_zero (a : R) : radical a ≠ 0 :=
  by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_not_mem_normalizedFactors _

theorem radical_prime {a : R} (ha : Prime a) : radical a = normalize a :=
  by
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

theorem radical_prime_pow {a : R} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_prime ha

namespace Polynomial

theorem radical_degree_le {a : k[X]} (ha : a ≠ 0) : (radical a).degree ≤ a.degree :=
  degree_le_of_dvd (radical_dvd_self a) ha

theorem radical_natDegree_le {a : k[X]} : (radical a).natDegree ≤ a.natDegree :=
  by
  by_cases ha : a = 0
  · rw [ha, radical_zero, natDegree_one, natDegree_zero]
  · exact natDegree_le_of_dvd (radical_dvd_self a) ha

end Polynomial

import Lib.Radical
import Lib.Wronskian

#align_import lib.div_radical

/-
On `div_radical(a) = a / radical(a)`. The purpose of this file is to prove our "main lemma" that `div_radical(a)` divides `a'` for any nonzero polynomial `a`.
The proof is based on induction (`unique_factorization_domain.induction_on_coprime`).
-/
/-
On `div_radical(a) = a / radical(a)`. The purpose of this file is to prove our "main lemma" that `div_radical(a)` divides `a'` for any nonzero polynomial `a`.
The proof is based on induction (`unique_factorization_domain.induction_on_coprime`).
-/
noncomputable section

open scoped Polynomial Classical

namespace Polynomial

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]

/--
For a given polynomial `a`, `div_radical(a)` is `a` divided by its radical `rad(a)`. This is the key to our implementation. -/
def divRadical (a : k[X]) : k[X] :=
  a / a.radical

theorem hMul_radical_divRadical (a : k[X]) : a.radical * a.divRadical = a :=
  by
  rw [div_radical]
  rw [← EuclideanDomain.mul_div_assoc]
  refine' mul_div_cancel_left₀ _ _
  exact a.radical_ne_zero
  exact radical_dvd_self a

theorem divRadical_ne_zero {a : k[X]} (ha : a ≠ 0) : a.divRadical ≠ 0 :=
  by
  rw [← mul_radical_div_radical a] at ha
  exact right_ne_zero_of_mul ha

theorem divRadical_isUnit {u : k[X]} (hu : IsUnit u) : IsUnit u.divRadical := by
  rwa [div_radical, radical_is_unit hu, EuclideanDomain.div_one]

theorem eq_divRadical {a x : k[X]} (h : a.radical * x = a) : x = a.divRadical :=
  by
  apply EuclideanDomain.eq_div_of_mul_eq_left a.radical_ne_zero
  rwa [mul_comm]

theorem divRadical_hMul {a b : k[X]} (hc : IsCoprime a b) :
    (a * b).divRadical = a.divRadical * b.divRadical :=
  by
  by_cases ha : a = 0
  · rw [ha, MulZeroClass.zero_mul, div_radical, EuclideanDomain.zero_div, MulZeroClass.zero_mul]
  by_cases hb : b = 0
  · rw [hb, MulZeroClass.mul_zero, div_radical, EuclideanDomain.zero_div, MulZeroClass.mul_zero]
  symm; apply eq_div_radical
  rw [radical_mul hc]
  rw [mul_mul_mul_comm, mul_radical_div_radical, mul_radical_div_radical]

theorem divRadical_dvd_self (a : k[X]) : a.divRadical ∣ a :=
  by
  rw [div_radical]
  apply EuclideanDomain.div_dvd_of_dvd
  exact radical_dvd_self a

/- Main lemma: a / rad(a) ∣ a'.
Proof uses `induction_on_coprime` of `unique_factorization_domain`.
-/
theorem divRadical_dvd_derivative (a : k[X]) : a.divRadical ∣ a.derivative :=
  by
  apply induction_on_coprime a
  · -- When a is zero.
    rw [derivative_zero]
    apply dvd_zero
  ·-- When a is unit.
    exact fun a ha => (div_radical_is_unit ha).Dvd
  · -- When a = p^i for some prime p.
    rintro p (_ | i) hp
    · rw [pow_zero, derivative_one]
      apply dvd_zero
    rw [← mul_dvd_mul_iff_left (radical_ne_zero (p ^ i.succ)), mul_radical_div_radical,
      radical_prime_pow hp i.succ_pos, derivative_pow_succ, ← mul_assoc]
    apply dvd_mul_of_dvd_left
    rw [mul_comm, mul_assoc]
    apply dvd_mul_of_dvd_right
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff]
  · -- If it holds for coprime pair a and b, then it also holds for a * b.
    intro x y hpxy hx hy
    have hc : IsCoprime x y :=
      EuclideanDomain.isCoprime_of_dvd
        (fun ⟨hx, hy⟩ => not_isUnit_zero (hpxy 0 (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
        fun p hp _ hpx hpy => hp (hpxy p hpx hpy)
    rw [div_radical_mul hc, derivative_mul]
    exact dvd_add (mul_dvd_mul hx y.div_radical_dvd_self) (mul_dvd_mul x.div_radical_dvd_self hy)

theorem divRadical_dvd_wronskian_left (a b : k[X]) : a.divRadical ∣ wronskian a b :=
  by
  rw [wronskian]
  apply dvd_sub
  · apply dvd_mul_of_dvd_left
    exact div_radical_dvd_self a
  · apply dvd_mul_of_dvd_left
    exact div_radical_dvd_derivative a

theorem divRadical_dvd_wronskian_right (a b : k[X]) : b.divRadical ∣ wronskian a b :=
  by
  rw [wronskian_anticomm, dvd_neg]
  exact b.div_radical_dvd_wronskian_left _

end Polynomial


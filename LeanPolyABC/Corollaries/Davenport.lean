import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import LeanPolyABC.MasonStothers

noncomputable section

open scoped Polynomial Classical

open Polynomial

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]

/- Davenport's theorem
For any nonzero polynomial a, b ∈ k[t] with k of characteristic zero,
deg(a) + 2 ≤ 2 * deg(a^3 - b^2).

Proof) Apply ABC for (-a^3, b^2, a^3 - b^2).
-/
lemma ne_zero_of_natDegree_gt_0 {a : k[X]} (ha : a.natDegree > 0) : a ≠ 0 := λ h ↦ by
  simp only [h, natDegree_zero, gt_iff_lt, lt_self_iff_false] at ha

theorem Polynomial.davenport [CharZero k] {a b : k[X]}
    (ha : a.natDegree > 0) (hb : b.natDegree > 0) (hnz : a ^ 3 - b ^ 2 ≠ 0) :
    a.natDegree + 2 ≤ 2 * (a ^ 3 - b ^ 2).natDegree := by
  have ha3 : -a^3 ≠ 0 := neg_ne_zero.mpr <| pow_ne_zero 3 <| ne_zero_of_natDegree_gt_0 ha
  have hb2 : b^2 ≠ 0 := pow_ne_zero 2 <| ne_zero_of_natDegree_gt_0 hb
  cases' abc'_char0 ha3 hb2 hnz (by ring_nf) with heq hineq
  · simp only [natDegree_neg, natDegree_pow] at heq
    omega
  · rw [Nat.succ_le_iff] at hineq
    simp only [Nat.max₃, natDegree_neg, natDegree_pow,
      radical_neg, Nat.ofNat_pos, radical_pow, max_lt_iff] at hineq
    nlinarith only [hineq.1, hineq.2, radical_natDegree_le a, radical_natDegree_le b]

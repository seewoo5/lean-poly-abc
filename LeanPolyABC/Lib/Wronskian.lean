import Mathlib.RingTheory.Polynomial.Content

#align_import lib.wronskian

noncomputable section

open scoped Polynomial Classical

open Polynomial

variable {k : Type _} [Field k]

/-- Wronskian: W(a, b) = ab' - a'b. -/
def wronskian (a b : k[X]) : k[X] :=
  a * (derivative b) - (derivative a) * b

@[simp]
theorem wronskian_zero_left (a : k[X]) : wronskian 0 a = 0 := by
  simp_rw [wronskian]; simp only [MulZeroClass.zero_mul, derivative_zero, sub_self]

@[simp]
theorem wronskian_zero_right (a : k[X]) : wronskian a 0 = 0 := by
  simp_rw [wronskian]; simp only [derivative_zero, MulZeroClass.mul_zero, sub_self]

theorem wronskian_neg_left (a b : k[X]) : wronskian (-a) b = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

theorem wronskian_neg_right (a b : k[X]) : wronskian a (-b) = -wronskian a b := by
  simp_rw [wronskian, derivative_neg]; ring

theorem wronskian_add_right (a b c : k[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  by simp_rw [wronskian, derivative_add]; ring

theorem wronskian_self (a : k[X]) : wronskian a a = 0 := by rw [wronskian, mul_comm, sub_self]

theorem wronskian_anticomm (a b : k[X]) : wronskian a b = -wronskian b a := by
  rw [wronskian, wronskian]; ring

theorem wronskian_eq_of_sum_zero {a b c : k[X]} (h : a + b + c = 0) :
    wronskian a b = wronskian b c :=
  by
  rw [← neg_eq_iff_add_eq_zero] at h
  rw [← h]
  rw [wronskian_neg_right]
  rw [wronskian_add_right]
  rw [wronskian_self]
  rw [add_zero]
  rw [← wronskian_anticomm]

private theorem degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ := by
  intro h <;> rw [Polynomial.degree_eq_bot] at h <;> exact ha h

theorem wronskian.degree_lt_add {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) :
    (wronskian a b).degree < a.degree + b.degree :=
  by
  calc
    (wronskian a b).degree ≤ max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]; constructor <;> rw [degree_mul]
      · rw [WithBot.add_lt_add_iff_left (degree_ne_bot ha)]
        exact Polynomial.degree_derivative_lt hb
      · rw [WithBot.add_lt_add_iff_right (degree_ne_bot hb)]
        exact Polynomial.degree_derivative_lt ha

-- Note: the following is false!
-- Counterexample: b = a = 1 →
-- (wronskian a b).nat_degree = a.nat_degree = b.nat_degree = 0
/-
lemma wronskian.nat_degree_lt_add {a b : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) :
  (wronskian a b).nat_degree < a.nat_degree + b.nat_degree := sorry
-/
theorem wronskian.natDegree_lt_add {a b : k[X]} (hw : wronskian a b ≠ 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree :=
  by
  have ha : a ≠ 0 := by intro h <;> subst h <;> rw [wronskian_zero_left] at hw <;> exact hw rfl
  have hb : b ≠ 0 := by intro h <;> subst h <;> rw [wronskian_zero_right] at hw <;> exact hw rfl
  rw [← WithBot.coe_lt_coe, WithBot.coe_add]
  convert ← wronskian.degree_lt_add ha hb
  exact Polynomial.degree_eq_natDegree hw
  exact Polynomial.degree_eq_natDegree ha
  exact Polynomial.degree_eq_natDegree hb

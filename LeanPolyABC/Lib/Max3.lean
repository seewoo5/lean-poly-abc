import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat

#align_import lib.max3

-- Utility library for three maxes of ℕ
-- Utility library for three maxes of ℕ
/-- maximum of three natural numbers. -/
def max3 (a b c : ℕ) : ℕ :=
  max (max a b) c

theorem max3_hMul_left (a b c d : ℕ) : max3 (a * b) (a * c) (a * d) = a * max3 b c d := by
  rw [Nat.mul_comm a (max3 b c d)]
  simp_rw [max3]
  rw [max_mul_of_nonneg _ _ (zero_le a)]
  rw [max_mul_of_nonneg _ _ (zero_le a)]
  repeat' rw [Nat.mul_comm a _]

theorem max3_add_add_right (a b c d : ℕ) : max3 (a + d) (b + d) (c + d) = max3 a b c + d :=
  by
  simp_rw [max3]
  rw [← max_add_add_right (max a b) c d]
  rw [← max_add_add_right a b d]

theorem le_max3_first (a b c : ℕ) : a ≤ max3 a b c :=
  le_max_of_le_left (le_max_left _ _)

theorem le_max3_second (a b c : ℕ) : b ≤ max3 a b c :=
  le_max_of_le_left (le_max_right _ _)

theorem le_max3_third (a b c : ℕ) : c ≤ max3 a b c :=
  le_max_right _ _

theorem max3_lt_iff {a b c d : ℕ} : max3 a b c < d ↔ a < d ∧ b < d ∧ c < d := by
  rw [max3]
  simp only [max_lt_iff]
  tauto

theorem max3_le_iff {a b c d : ℕ} : max3 a b c ≤ d ↔ a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  rw [max3]
  simp only [max_le_iff]
  tauto

theorem add3_le_three_hMul_max3 (a b c : ℕ) : a + b + c ≤ 3 * max3 a b c :=
  by
  rw [show 3 = 2 + 1 from rfl]
  rw [Nat.succ_mul, two_mul]
  apply Nat.add_le_add _ (le_max3_third _ _ _)
  apply Nat.add_le_add _ (le_max3_second _ _ _)
  exact le_max3_first _ _ _

theorem weighted_average_le_max3 {p q r a b c : ℕ} :
    p * a + q * b + r * c ≤ (p + q + r) * max3 a b c :=
  by
  simp_rw [add_mul]
  apply Nat.add_le_add
  apply Nat.add_le_add
  exact Nat.mul_le_mul (le_refl _) (le_max3_first _ _ _)
  exact Nat.mul_le_mul (le_refl _) (le_max3_second _ _ _)
  exact Nat.mul_le_mul (le_refl _) (le_max3_third _ _ _)

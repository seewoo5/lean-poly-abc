import tactic.simp_rw
import data.nat.order.basic
import order.min_max
import algebra.group.defs
import algebra.order.ring.defs
import algebra.order.monoid.defs
import algebra.order.monoid.min_max

-- Utility library for three maxes of ℕ

def max3 (a b c : ℕ) : ℕ := max (max a b) c

theorem max3_mul_left (a b c d : ℕ) :
  max3 (a * b) (a * c) (a * d) = a * max3 b c d :=
begin
  -- This is hard: should I use `max_mul_of_nonneg`
  -- or `max_mul_mul_left`?
  rw nat.mul_comm a (max3 b c d),
  simp_rw max3,
  rw max_mul_of_nonneg _ _ (zero_le a),
  rw max_mul_of_nonneg _ _ (zero_le a),
  repeat {rw nat.mul_comm a _},
end

theorem le_max3_first (a b c : ℕ) : a ≤ max3 a b c :=
  le_max_of_le_left (le_max_left _ _)

theorem le_max3_second (a b c : ℕ) : b ≤ max3 a b c :=
  le_max_of_le_left (le_max_right _ _)

theorem le_max3_third (a b c : ℕ) : c ≤ max3 a b c :=
  le_max_right _ _

theorem max3_lt_iff {a b c d : ℕ} : 
  max3 a b c < d ↔ a < d ∧ b < d ∧ c < d :=
begin
  rw max3, simp only [max_lt_iff], tauto,
end
import data.nat.order.basic

-- Utility library for three maxes of ℕ

/-- maximum of three natural numbers. -/
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

theorem add3_le_three_mul_max3 (a b c : ℕ) : 
  a + b + c ≤ 3 * max3 a b c :=
begin
  rw (show 3 = 2 + 1, by exact rfl),
  rw [nat.succ_mul, two_mul],
  apply nat.add_le_add _ (le_max3_third _ _ _),
  apply nat.add_le_add _ (le_max3_second _ _ _),
  exact le_max3_first _ _ _,
end

theorem weighted_average_le_max3 {p q r a b c: ℕ} :
  p*a + q*b + r*c ≤ (p+q+r)*(max3 a b c) := 
begin
  simp_rw add_mul,
  apply nat.add_le_add,
  apply nat.add_le_add,
  exact nat.mul_le_mul (le_refl _) (le_max3_first _ _ _),
  exact nat.mul_le_mul (le_refl _) (le_max3_second _ _ _),
  exact nat.mul_le_mul (le_refl _) (le_max3_third _ _ _),
end
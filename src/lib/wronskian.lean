import ring_theory.polynomial.content


noncomputable theory
open_locale polynomial classical

open polynomial

variables {k: Type*} [field k]

/-- Wronskian: W(a, b) = ab' - a'b. -/
def wronskian (a b : k[X]) : k[X] :=
  a * b.derivative - a.derivative * b

@[simp]
lemma wronskian_zero_left (a : k[X]) : wronskian 0 a = 0 :=
by simp_rw wronskian; simp only [zero_mul, derivative_zero, sub_self]

@[simp]
lemma wronskian_zero_right (a : k[X]) : wronskian a 0 = 0 :=
by simp_rw wronskian; simp only [derivative_zero, mul_zero, sub_self]

lemma wronskian_neg_left (a b : k[X]) : wronskian (-a) b = - (wronskian a b) :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_neg_right (a b : k[X]) : wronskian a (-b) = - wronskian a b :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_add_right (a b c : k[X]) :
  wronskian a (b + c) = wronskian a b + wronskian a c :=
by simp_rw [wronskian, derivative_add]; ring

lemma wronskian_self (a : k[X]) : wronskian a a = 0 :=
by rw [wronskian, mul_comm, sub_self]

lemma wronskian_anticomm (a b : k[X]) : wronskian a b = - wronskian b a :=
by rw [wronskian, wronskian]; ring

lemma wronskian_eq_of_sum_zero {a b c : k[X]}
  (h : a + b + c = 0) : wronskian a b = wronskian b c :=
begin
  rw ← neg_eq_iff_add_eq_zero at h,
  rw ← h,
  rw wronskian_neg_right,
  rw wronskian_add_right,
  rw wronskian_self,
  rw add_zero,
  rw ← wronskian_anticomm,
end

private lemma degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ :=
  by intro h; rw polynomial.degree_eq_bot at h; exact ha h

lemma wronskian.degree_lt_add {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) : 
  (wronskian a b).degree < a.degree + b.degree :=
begin
  calc (wronskian a b).degree ≤ 
    max (a * b.derivative).degree (a.derivative * b).degree : 
      polynomial.degree_sub_le _ _
    ... < a.degree + b.degree : _,
  rw max_lt_iff, split; rw degree_mul,
  { rw with_bot.add_lt_add_iff_left (degree_ne_bot ha),
    exact polynomial.degree_derivative_lt hb, },
  { rw with_bot.add_lt_add_iff_right (degree_ne_bot hb),
    exact polynomial.degree_derivative_lt ha, },
end

-- Note: the following is false!
-- Counterexample: b = a = 1 → 
-- (wronskian a b).nat_degree = a.nat_degree = b.nat_degree = 0
/-
lemma wronskian.nat_degree_lt_add {a b : k[X]} 
  (ha : a ≠ 0) (hb : b ≠ 0) : 
  (wronskian a b).nat_degree < a.nat_degree + b.nat_degree := sorry
-/

lemma wronskian.nat_degree_lt_add {a b : k[X]} 
  (hw : wronskian a b ≠ 0) : 
  (wronskian a b).nat_degree < a.nat_degree + b.nat_degree :=
begin
  have ha : a ≠ 0 := 
    by intro h; subst h; rw wronskian_zero_left at hw; exact hw rfl,
  have hb : b ≠ 0 := 
    by intro h; subst h; rw wronskian_zero_right at hw; exact hw rfl,
  rw [←with_bot.coe_lt_coe, with_bot.coe_add],
  convert ←wronskian.degree_lt_add ha hb,
  exact polynomial.degree_eq_nat_degree hw,
  exact polynomial.degree_eq_nat_degree ha,
  exact polynomial.degree_eq_nat_degree hb,
end

import algebra.char_p.basic
import algebra.euclidean_domain.defs

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

lemma is_coprime_nonzero_c {a b : k[X]} (h : is_coprime a b) (ha : a.derivative ≠ 0)
  : a^3 - b^2 ≠ 0 :=
begin
  by_contra h_eq_zero,
  rw sub_eq_zero at h_eq_zero,
  have hp : is_coprime (a^3) (b^2) := h.pow,
  rw [←h_eq_zero, is_coprime_self, is_unit_pow_iff, is_unit_iff] at hp,
  rcases hp with ⟨ r, r_unit, eq_a ⟩,
  rw ←eq_a at ha, exact ha derivative_C,
  norm_num, -- 3 ≠ 0
end

/- Davenport's theorem
For any coprime polynomial a, b ∈ k[t] with nonzero derivatives,
deg(a) + 2 ≤ 2 * deg(a^3 - b^2).

Proof) Apply ABC for (-a^3, b^2, a^3 - b^2).
-/
theorem polynomial.davenport
  {a b : k[X]} (hab : is_coprime a b) (haderiv : a.derivative ≠ 0) (hbderiv : b.derivative ≠ 0) :
    a.nat_degree + 2 ≤ 2 * (a^3 - b^2).nat_degree :=
begin
  have hnz : a^3 - b^2 ≠ 0 := is_coprime_nonzero_c hab haderiv,
  have ha : a ≠ 0 := λ ha, haderiv (ha.symm ▸ derivative_zero),
  have hb : b ≠ 0 := λ hb, hbderiv (hb.symm ▸ derivative_zero),
  have h1 : is_coprime (a ^ 3) (a ^ 3 - b ^ 2),
  { rwa [←is_coprime.neg_right_iff, neg_sub, sub_eq_add_neg, neg_eq_neg_one_mul,
      is_coprime.add_mul_right_right_iff, is_coprime.pow_iff three_pos two_pos] },
  have h2 : is_coprime (b ^ 2) (a ^ 3 - b ^ 2),
  { rwa [sub_eq_add_neg, neg_eq_neg_one_mul,
      is_coprime.add_mul_right_right_iff, is_coprime.pow_iff two_pos three_pos, is_coprime_comm] },
  cases abc (neg_ne_zero.mpr (pow_ne_zero 3 ha)) (pow_ne_zero 2 hb) hnz hab.pow.neg_left h2 h1.neg_left.symm
      (by rw [sub_eq_add_neg, add_add_add_comm, neg_add_self, add_neg_self, add_zero]) with h h,
  { rw [nat_degree_neg, max3, max_eq_left (nat_degree_sub_le _ _), neg_mul, neg_mul, radical_neg,
        radical_mul (h1.mul_left h2), radical_mul hab.pow, radical_pow a three_pos, radical_pow b two_pos,
        nat_degree_mul (mul_ne_zero a.radical_ne_zero b.radical_ne_zero) (radical_ne_zero _),
        nat_degree_mul a.radical_ne_zero b.radical_ne_zero, nat_degree_pow, nat_degree_pow, ←max_add_add_right] at h,
    replace h := le_trans h (add_le_add (add_le_add radical_nat_degree_le radical_nat_degree_le) radical_nat_degree_le),
    rw max_le_iff at h,
    nlinarith only [add_le_add h.1 h.2] },
  { rw [derivative_neg, neg_eq_zero, derivative_pow, derivative_pow, nat.succ_sub_one, nat.succ_sub_one,
      mul_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero, or_iff_left haderiv, or_iff_left hbderiv,
      or_iff_left (pow_ne_zero 2 ha), or_iff_left (pow_ne_zero 1 hb)] at h,
    replace h := h.1.trans h.2.1.symm,
    rw [←sub_eq_zero, ←C_sub, ←nat.cast_sub (nat.le_succ 2), nat.cast_one, C_1] at h,
    exact (one_ne_zero h).elim },
end

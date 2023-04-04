import algebra.char_p.basic
import algebra.euclidean_domain.defs

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

lemma le_double {a : ℕ} : a ≤ 2 * a :=
begin
  apply (one_mul a).symm.trans_le,
  apply nat.mul_le_mul_right a,
  dec_trivial,
end

lemma ne_nat_degree_add_max_nat_degree {a b : k[X]} (hdeg : a.nat_degree ≠ b.nat_degree)
: (a + b).nat_degree = max a.nat_degree b.nat_degree :=
begin
  -- combine
  -- nat_degree_add_eq_left_of_nat_degree_lt
  -- nat_degree_add_eq_right_of_nat_degree_lt
  -- divide cases?
  sorry,
end

lemma ne_nat_degree_sub_max_nat_degree {a b : k[X]} (hdeg : a.nat_degree ≠ b.nat_degree)
: (a - b).nat_degree = max a.nat_degree b.nat_degree :=
begin
  have hdeg : a.nat_degree ≠ (-b).nat_degree :=
  begin
    by_contra hdeg',
    rw nat_degree_neg at hdeg',
    tauto,
  end,
  by calc (a - b).nat_degree = (a + (-b)).nat_degree : by ring_nf
  ... = max a.nat_degree (-b).nat_degree : ne_nat_degree_add_max_nat_degree hdeg
  ... = max a.nat_degree b.nat_degree : by rw nat_degree_neg,
end

lemma nat_degree_sub_le_nat_degree {a b : k[X]} : (a - b).nat_degree ≤ max a.nat_degree b.nat_degree :=
begin
  by calc (a - b).nat_degree = (a + (-b)).nat_degree : by ring_nf
  ... ≤ max a.nat_degree (-b).nat_degree : nat_degree_add_le a (-b)
  ... = max a.nat_degree b.nat_degree : by rw nat_degree_neg,
end

lemma derivative_ne_zero_nat_degree_ge_one {a : k[X]} (h : a.derivative ≠ 0) : 1 ≤ a.nat_degree :=
begin
  
  sorry,
end

/- Davenport's theorem
For any nonconstant coprime polynomial a, b ∈ k[t], if a^3 ≠ b^2, then
(1 / 2) * deg(a) + 1 ≤ deg(a^3 - b^2).

Proof) Apply ABC for (-a^3, b^2, a^3 - b^2). Need to divide cases whether
deg(a^3) = deg(b^2) or not.
-/
theorem polynomial.davenport
  {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hab : is_coprime a b) (hnz : a^3 - b^2 ≠ 0) (haderiv : a.derivative ≠ 0) (hbderiv : b.derivative ≠ 0) :
    a.nat_degree + 2 ≤ 2 * (a^3 - b^2).nat_degree :=
begin
  have h1 : is_coprime (a ^ 3) (a ^ 3 - b ^ 2),
  { rwa [←is_coprime.neg_right_iff, neg_sub, sub_eq_add_neg, neg_eq_neg_one_mul,
      is_coprime.add_mul_right_right_iff, is_coprime.pow_iff three_pos two_pos] },
  have h2 : is_coprime (b ^ 2) (a ^ 3 - b ^ 2),
  { rwa [sub_eq_add_neg, neg_eq_neg_one_mul,
      is_coprime.add_mul_right_right_iff, is_coprime.pow_iff two_pos three_pos, is_coprime_comm] },
  cases abc (neg_ne_zero.mpr (pow_ne_zero 3 ha)) (pow_ne_zero 2 hb) hnz hab.pow.neg_left h2
      (by rwa [is_coprime.neg_right_iff, is_coprime_comm])
      (by rw [sub_eq_add_neg, add_add_add_comm, neg_add_self, add_neg_self, add_zero]) with h h,
  { rw [nat_degree_neg, max3, max_eq_left (nat_degree_sub_le _ _), neg_mul, neg_mul, radical_neg,
        radical_mul (h1.mul_left h2), radical_mul hab.pow, radical_pow a sorry, radical_pow b sorry, -- change hypothesis to 0 < n
        nat_degree_mul (mul_ne_zero a.radical_ne_zero b.radical_ne_zero) (radical_ne_zero _),
        nat_degree_mul a.radical_ne_zero b.radical_ne_zero, nat_degree_pow, nat_degree_pow] at h,
    replace h := h.trans_le (add_le_add (add_le_add radical_nat_degree_le radical_nat_degree_le) radical_nat_degree_le),
    rw [max_lt_iff, ←nat.one_add_le_iff, ←nat.one_add_le_iff] at h,
    replace h := add_le_add h.1 h.2,
    nlinarith only [h] },
  { rw [derivative_neg, neg_eq_zero, derivative_pow, derivative_pow,
      mul_eq_zero, mul_eq_zero, mul_eq_zero, mul_eq_zero,
      or_iff_left haderiv, or_iff_left hbderiv,
      pow_eq_zero_iff, pow_eq_zero_iff,
      or_iff_left ha, or_iff_left hb] at h,
    replace h := h.1.trans h.2.1.symm,
    rw [←sub_eq_zero, ←C_sub, ←nat.cast_sub, nat.succ_sub, nat.sub_self, nat.cast_one, C_1] at h,
    exact (one_ne_zero h).elim,
    all_goals { norm_num } },
end

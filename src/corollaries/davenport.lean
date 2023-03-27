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

lemma nat_lt_add_one_le {a b : ℕ} (h : a < b) : a + 1 ≤ b :=
begin
  sorry,
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


/- Davenport's theorem
For any nonconstant coprime polynomial a, b ∈ k[t], if a^3 ≠ b^2, then
(1 / 2) * deg(a) + 1 ≤ deg(a^3 - b^2).

Proof) Apply ABC for (-a^3, b^2, a^3 - b^2). Need to divide cases whether
deg(a^3) = deg(b^2) or not.
-/
theorem polynomial.davenport
  (ch2 : ¬(ring_char k ∣ 2)) (ch3 : ¬(ring_char k ∣ 3))
  {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hab : is_coprime a b) (hnz : a^3 - b^2 ≠ 0) :
    a.nat_degree + 2 ≤ 2 * (a^3 - b^2).nat_degree ∨
    (a.derivative = 0 ∧ b.derivative = 0) :=
begin
  set c := a^3 - b^2 with def_c,
  
  -- nonzero
  -- too much here...
  have hap : -a^3 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ha),
  have hbp : b^2 ≠ 0 := pow_ne_zero _ hb,
  have habp_nz : (-a^3) * (b^2) ≠ 0 := mul_ne_zero hap hbp, 
  have hab_nz : a * b ≠ 0 := mul_ne_zero ha hb,
  have habc : a * b * c ≠ 0 := mul_ne_zero hab_nz hnz, 
  have har : a.radical ≠ 0 := radical_ne_zero a,
  have hbr : b.radical ≠ 0 := radical_ne_zero b,
  have hcr : c.radical ≠ 0 := radical_ne_zero c,
  have habr : a.radical * b.radical ≠ 0 := mul_ne_zero har hbr,
  have habr' : (a * b).radical ≠ 0 :=
    by calc (a * b).radical = a.radical * b.radical : radical_mul hab
    ... ≠ 0 : habr, 

  -- coprime
  have habp : is_coprime (-a^3) (b^2) := (is_coprime.pow hab).neg_left,
  have hbcp : is_coprime (b^2) c := sorry,
  have hcap : is_coprime c (-a^3) := sorry,
  have hab_cp : is_coprime ((-a^3) * (b^2)) c := sorry,
  have hab_cp' : is_coprime (a * b) c := sorry,

  -- degree of c = a^3 - b^2
  -- have deg_c_le : c.nat_degree ≤ max (3 * a.nat_degree) (2 * b.nat_degree) :=
  --   by calc c.nat_degree = (a^3 - b^2).nat_degree : by rw def_c
  --   -- ... ≤ max (a^3).nat_degree (b^2).nat_degree : sorry
  --   ... = max (3 * a.nat_degree) (2 * b.nat_degree) : by simp_rw nat_degree_pow,
  have heq : (-a^3) + b^2 + c = 0 :=
    by calc (-a^3) + b^2 + c = (-a^3) + b^2 + (a^3 - b^2) : by rw def_c
    ... = 0 : by ring_nf,
  -- why below is not working?
  -- have heq : (-a^3) + b^2 + c = 0 := by [rw def_c, ring_nf],
  
  -- apply ABC
  cases (polynomial.abc hap hbp hnz habp hbcp hcap heq) with deg_ineq dr0, swap,
  { rw [polynomial.derivative_neg, neg_eq_zero] at dr0,
    rw [pow_derivative_eq_zero ch3 ha,
        pow_derivative_eq_zero ch2 hb] at dr0,
        tauto, },

  -- divide into two cases: deg(a^3) = deg(b^2) or not
  by_cases hdeg : (a^3).nat_degree = (b^2).nat_degree,
  {
    have t1 : 3 * a.nat_degree = 2 * b.nat_degree :=
    begin
      simp_rw nat_degree_pow at hdeg,
      exact hdeg,
    end,
    have t2 : max3 (a^3).nat_degree (b^2).nat_degree (c.nat_degree) = 3 * a.nat_degree :=
    begin
      have h1 : c.nat_degree ≤ max (a^3).nat_degree (b^2).nat_degree := nat_degree_sub_le_nat_degree,
      by calc max3 (a^3).nat_degree (b^2).nat_degree (c.nat_degree) = max (a^3).nat_degree (b^2).nat_degree : max_eq_left h1
      ... = max (a^3).nat_degree (a^3).nat_degree : by rw hdeg
      ... = (a^3).nat_degree : max_self _
      ... = 3 * a.nat_degree : by simp only [nat_degree_pow],
    end,
    have t2' : (a * b).nat_degree ≤ a.nat_degree + b.nat_degree := nat_degree_mul_le,
    have t3 :=
    by calc 3 * a.nat_degree + 1 = max3 (a^3).nat_degree (b^2).nat_degree c.nat_degree + 1: by rw t2
    ... = max3 (-a^3).nat_degree (b^2).nat_degree c.nat_degree + 1 : by rw nat_degree_neg
    ... ≤ ((-a^3) * (b^2) * c).radical.nat_degree : nat_lt_add_one_le deg_ineq
    ... = ((-a^3) * (b^2)).radical.nat_degree + c.radical.nat_degree : sorry
    ... = (-a^3).radical.nat_degree + (b^2).radical.nat_degree + c.radical.nat_degree : sorry
    ... = (a^3).radical.nat_degree + (b^2).radical.nat_degree + c.radical.nat_degree : by rw radical_neg
    ... = a.radical.nat_degree + b.radical.nat_degree + c.radical.nat_degree : sorry -- why 1 ≤ 2 and 1 ≤ 3?
    ... = (a.radical * b.radical).nat_degree + c.radical.nat_degree : by rw← (nat_degree_mul har hbr)
    ... = (a * b).radical.nat_degree + c.radical.nat_degree : by rw← radical_mul hab
    ... = ((a * b).radical * c.radical).nat_degree : by rw← (nat_degree_mul habr' hcr)
    ... = (a * b * c).radical.nat_degree : by rw← (radical_mul hab_cp')
    ... ≤ (a * b * c).nat_degree : radical_nat_degree_le
    ... = (a * b).nat_degree + c.nat_degree : nat_degree_mul hab_nz hnz
    ... = a.nat_degree + b.nat_degree + c.nat_degree : by rw [nat_degree_mul ha hb],

    have t4 : 5 * a.nat_degree + (a.nat_degree + 2) ≤ 5 * a.nat_degree + (2 * c.nat_degree) :=
    by calc 5 * a.nat_degree + a.nat_degree + 2 = 2 * (3 * a.nat_degree + 1) : by ring_nf
    ... ≤ 2 * (a.nat_degree + b.nat_degree + c.nat_degree) : sorry
    ... = 2 * a.nat_degree + 2 * b.nat_degree + 2 * c.nat_degree : by ring_nf
    ... = 2 * a.nat_degree + 3 * a.nat_degree + 2 * c.nat_degree : by rw t1
    ... = 5 * a.nat_degree + (2 * c.nat_degree) : by ring_nf,
    have t5 : a.nat_degree + 2 ≤ 2 * c.nat_degree := by linarith, -- avoid to use linarith
    tauto,
  },
  {
    have hcdeg : c.nat_degree = max (3 * a.nat_degree) (2 * b.nat_degree) :=
    begin
      by calc c.nat_degree = (a^3 - b^2).nat_degree : by rw def_c
      ... = max (a^3).nat_degree (b^2).nat_degree : ne_nat_degree_sub_max_nat_degree hdeg
      ... = max (3 * a.nat_degree) (2 * b.nat_degree) : by simp only [nat_degree_pow],
    end,
    have a_nat_degree_nz : a.nat_degree ≠ 0 := sorry, 
    have hadeg : 1 ≤ a.nat_degree :=
    begin
      rw nat.one_le_iff_ne_zero, -- why not rw← ?
      exact a_nat_degree_nz,
    end,
    have deg_ineq2 : a.nat_degree + 2 ≤ 2 * c.nat_degree :=
      by calc a.nat_degree + 2 ≤ a.nat_degree + 2 * a.nat_degree : sorry
      ... = 3 * a.nat_degree : by ring_nf
      ... ≤ 2 * (3 * a.nat_degree) : le_double 
      ... ≤ 2 * (max (3 * a.nat_degree) (2 * b.nat_degree)) : by simp only [mul_le_mul_left, nat.succ_pos', le_max_iff, le_refl, true_or]
      ... = 2 * c.nat_degree : by rw hcdeg,
    tauto,
  },
end

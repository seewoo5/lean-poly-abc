import algebra.char_p.basic
import algebra.euclidean_domain.defs

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

theorem polynomial.davenport
  (ch2 : ¬(ring_char k ∣ 2)) (ch3 : ¬(ring_char k ∣ 3))
  {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hab : is_coprime a b) (hnz : a^3 - b^2 ≠ 0) :
    a.nat_degree + 2 ≤ 2 * (a^3 - b^2).nat_degree ∨
    (a.derivative = 0 ∧ b.derivative = 0) :=
begin
  set c := a^3 - b^2 with def_c,
  
  -- nonzero
  have hap : -a^3 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ ha),
  have hbp : b^2 ≠ 0 := pow_ne_zero _ hb,
  have hab_nz : a * b ≠ 0 := mul_ne_zero ha hb,
  have habc : a * b * c ≠ 0 := mul_ne_zero hab_nz hnz, 

  -- coprime
  have habp : is_coprime (-a^3) (b^2) := (is_coprime.pow hab).neg_left,
  have hbcp : is_coprime (b^2) c := sorry,
  have hcap : is_coprime c (-a^3) := sorry,

  -- degree of c = a^3 - b^2
  have deg_c_le : c.nat_degree ≤ max (3 * a.nat_degree) (2 * b.nat_degree) :=
    by calc c.nat_degree = (a^3 - b^2).nat_degree : by rw def_c
    ... ≤ max (a^3).nat_degree (b^2).nat_degree : sorry
    ... = max (3 * a.nat_degree) (2 * b.nat_degree) : by simp_rw nat_degree_pow,
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

  by_cases hdeg : (a^3).nat_degree = (b^2).nat_degree,
  {
    have t1 : 3 * a.nat_degree = 2 * b.nat_degree := sorry,
    have t2 : max3 (3 * a.nat_degree) (2 * b.nat_degree) (c.nat_degree) = 3 * a.nat_degree := sorry,
    have t3 :=
    by calc 3 * a.nat_degree + 1 = max3 (3 * a.nat_degree) (2 * b.nat_degree) (c.nat_degree) + 1: by rw t2
    ... = max3 (a^3).nat_degree (b^2).nat_degree c.nat_degree + 1: sorry
    ... = max3 (-a^3).nat_degree (b^2).nat_degree c.nat_degree + 1: sorry
    ... ≤ ((-a^3) * (b^2) * c).radical.nat_degree : sorry
    ... = (a * b * c).radical.nat_degree : sorry
    ... ≤ (a * b * c).nat_degree : sorry -- radical_degree_le
    ... = a.nat_degree + b.nat_degree + c.nat_degree : sorry, 
    have t4 : 5 * a.nat_degree + (a.nat_degree + 2) ≤ 5 * a.nat_degree + (2 * c.nat_degree) :=
    by calc 5 * a.nat_degree + a.nat_degree + 2 = 2 * (3 * a.nat_degree + 1) : by ring_nf
    ... ≤ 2 * (a.nat_degree + b.nat_degree + c.nat_degree) : sorry
    ... = 2 * a.nat_degree + 2 * b.nat_degree + 2 * c.nat_degree : by ring_nf
    ... = 2 * a.nat_degree + 3 * a.nat_degree + 2 * c.nat_degree : by rw t1
    ... = 5 * a.nat_degree + (2 * c.nat_degree) : by ring_nf,
    have t5 : a.nat_degree + 2 ≤ 2 * c.nat_degree :=
    -- exact lt_of_add_lt_add_left t4,
    sorry,
    tauto,
  },
  {
    have hcdeg : c.nat_degree = max (3 * a.nat_degree) (2 * b.nat_degree) := sorry,
    have hadeg : 1 ≤ a.nat_degree := sorry,
    have deg_ineq2 : a.nat_degree + 2 ≤ 2 * c.nat_degree :=
      by calc a.nat_degree + 2 ≤ a.nat_degree + 2 * a.nat_degree : sorry
      ... = 3 * a.nat_degree : by ring_nf
      ... ≤ 2 * (3 * a.nat_degree) : sorry
      ... ≤ 2 * (max (3 * a.nat_degree) (2 * b.nat_degree)) : by simp only [mul_le_mul_left, nat.succ_pos', le_max_iff, le_refl, true_or]
      ... = 2 * c.nat_degree : by rw hcdeg,
    tauto,
  },
end

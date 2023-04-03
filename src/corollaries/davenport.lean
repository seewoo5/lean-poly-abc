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
  (ch2 : ¬(ring_char k ∣ 2)) (ch3 : ¬(ring_char k ∣ 3))
  {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hab : is_coprime a b) (hnz : a^3 - b^2 ≠ 0) (haderiv : a.derivative ≠ 0) (hbderiv : b.derivative ≠ 0) :
    a.nat_degree + 2 ≤ 2 * (a^3 - b^2).nat_degree :=
begin
  set c := a^3 - b^2 with def_c,
  have hac : is_coprime a c,
  { rwa [def_c, pow_succ, sub_eq_add_neg, is_coprime.mul_add_left_right_iff,
      is_coprime.neg_right_iff, is_coprime.pow_right_iff two_pos] },
  have hbc : is_coprime b c,
  { rwa [def_c, ←is_coprime.neg_right_iff, neg_sub, pow_succ, sub_eq_add_neg, is_coprime.mul_add_left_right_iff,
      is_coprime.neg_right_iff, is_coprime.pow_right_iff three_pos, is_coprime_comm] },
  
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
  -- have hbcp : is_coprime (b^2) c :=
  -- begin
  --   have hbap : is_coprime (b^2) (a^3) := (is_coprime.pow hab).symm,
  --   have t := is_coprime.mul_add_right_right hbap (-1),
  --   have tt : (-1) * b^2 + a^3 = c :=
  --   begin
  --     rw def_c,
  --     ring_nf,
  --   end,
  --   rw← tt,
  --   exact t,
  -- end,
  -- have hbcp' : is_coprime b c :=
  -- begin
  --   have h1 : 0 < 1 := by norm_num,
  --   have h2 : 0 < 2 := by norm_num,
  --   rw← is_coprime.pow_iff h2 h1,
  --   simp only [pow_one],
  --   exact hbcp,
  -- end,
  -- have hcap : is_coprime c (-a^3) := 
  -- begin
  --   have t : is_coprime (-b^2) (-a^3) := (is_coprime.pow hab).symm.neg_right.neg_left,
  --   have tt : is_coprime ((-1)*(-a^3) + (-b^2)) (-a^3) := is_coprime.mul_add_right_left t (-1),
  --   have ttt : ((-1)*(-a^3) + (-b^2)) = c := by ring_nf,
  --   rw← ttt,
  --   exact tt,
  -- end,
  -- have hcap' : is_coprime c a :=
  -- begin
  --   have t : is_coprime c (a^3) :=
  --   begin
  --     rw← is_coprime.neg_right_iff,
  --     exact hcap,
  --   end,
  --   have h1 : 0 < 1 := by norm_num,
  --   have h3 : 0 < 3 := by norm_num,
  --   rw← is_coprime.pow_iff h1 h3,
  --   simp only [pow_one],
  --   exact t, 
  -- end,
  have hab_cp : is_coprime ((-a^3) * (b^2)) c := sorry,
  have hab_cp' : is_coprime (a * b) c := sorry,

  -- better way to do below?
  have heq : (-a^3) + b^2 + c = 0 :=
    by calc (-a^3) + b^2 + c = (-a^3) + b^2 + (a^3 - b^2) : by rw def_c
    ... = 0 : by ring_nf,
  
  -- apply ABC
  cases (polynomial.abc hap hbp hnz habp sorry sorry heq) with deg_ineq dr0, swap,
  { rw [polynomial.derivative_neg, neg_eq_zero] at dr0,
    rw [pow_derivative_eq_zero ch3 ha,
        pow_derivative_eq_zero ch2 hb] at dr0,
        tauto, },
  rw [nat_degree_neg, radical_mul, radical_mul, radical_neg, radical_pow, radical_pow,
      nat_degree_mul, nat_degree_mul, nat_degree_pow, nat_degree_pow] at deg_ineq,


  -- divide into two cases: deg(a^3) = deg(b^2) or not
  -- by_cases hdeg : (a^3).nat_degree = (b^2).nat_degree,
  -- {
  --   have t1 : 3 * a.nat_degree = 2 * b.nat_degree :=
  --   begin
  --     simp_rw nat_degree_pow at hdeg,
  --     exact hdeg,
  --   end,
  --   have t2 : max3 (a^3).nat_degree (b^2).nat_degree (c.nat_degree) = 3 * a.nat_degree :=
  --   begin
  --     have h1 : c.nat_degree ≤ max (a^3).nat_degree (b^2).nat_degree := nat_degree_sub_le_nat_degree,
  --     by calc max3 (a^3).nat_degree (b^2).nat_degree (c.nat_degree) = max (a^3).nat_degree (b^2).nat_degree : max_eq_left h1
  --     ... = max (a^3).nat_degree (a^3).nat_degree : by rw hdeg
  --     ... = (a^3).nat_degree : max_self _
  --     ... = 3 * a.nat_degree : by simp only [nat_degree_pow],
  --   end,
  --   have t2' : (a * b).nat_degree ≤ a.nat_degree + b.nat_degree := nat_degree_mul_le,
  --   have t3 : 3 * a.nat_degree + 1 ≤ a.nat_degree + b.nat_degree + c.nat_degree :=
  --   begin
  --     calc 3 * a.nat_degree + 1 = max3 (-a^3).nat_degree (b^2).nat_degree c.nat_degree + 1 : by rw [←t2, nat_degree_neg]
  --     ... ≤ ((-a^3) * (b^2) * c).radical.nat_degree : _ -- I don't want to use underscore trick here
  --     -- ... = ((-a^3).radical * (b^2).radical * c.radical).nat_degree : 
  --     ... = ((a^3).radical * (b^2).radical * c.radical).nat_degree : by rw [radical_mul sorry, radical_mul sorry, radical_neg]
  --     ... = (a.radical * b.radical * c.radical).nat_degree: _ -- Same for here ...
  --     ... = ((a * b).radical * c.radical).nat_degree : by rw radical_mul hab
  --     ... = (a * b * c).radical.nat_degree : by rw radical_mul hab_cp'
  --     ... ≤ (a * b * c).nat_degree : radical_nat_degree_le
  --     ... = a.nat_degree + b.nat_degree + c.nat_degree : by rw [nat_degree_mul hab_nz hnz, nat_degree_mul ha hb],
  --     { rw nat.lt_iff_add_one_le at deg_ineq, exact deg_ineq, },
  --     { rw radical_pow a, rw radical_pow b, norm_num, norm_num, },
  --   end,

  --   have t4 : 5 * a.nat_degree + (a.nat_degree + 2) ≤ 5 * a.nat_degree + (2 * c.nat_degree) :=
  --   begin
  --     calc 5 * a.nat_degree + a.nat_degree + 2 = 2 * (3 * a.nat_degree + 1) : by ring_nf
  --     ... ≤ 2 * (a.nat_degree + b.nat_degree + c.nat_degree) : _ 
  --     ... = 2 * a.nat_degree + 2 * b.nat_degree + 2 * c.nat_degree : by rw [mul_add, mul_add]
  --     ... = 2 * a.nat_degree + 3 * a.nat_degree + 2 * c.nat_degree : by rw t1
  --     ... = 5 * a.nat_degree + (2 * c.nat_degree) : by ring_nf,
  --     {simp only [mul_le_mul_left, nat.succ_pos'], exact t3, },
  --   end,
  --   rwa [add_le_add_iff_left] at t4, -- avoid to use linarith
  --   -- tauto,
  -- },
  -- {
  --   have hcdeg : c.nat_degree = max (3 * a.nat_degree) (2 * b.nat_degree) :=
  --   begin
  --     by calc c.nat_degree = (a^3 - b^2).nat_degree : by rw def_c
  --     ... = max (a^3).nat_degree (b^2).nat_degree : ne_nat_degree_sub_max_nat_degree hdeg
  --     ... = max (3 * a.nat_degree) (2 * b.nat_degree) : by simp only [nat_degree_pow],
  --   end,
  --   have hadeg : 1 ≤ a.nat_degree := derivative_ne_zero_nat_degree_ge_one haderiv,
  --   have deg_ineq2 : a.nat_degree + 2 ≤ 2 * c.nat_degree :=
  --   begin
  --     calc a.nat_degree + 2 ≤ a.nat_degree + 2 * a.nat_degree : _ 
  --     ... = 3 * a.nat_degree : by ring_nf
  --     ... ≤ 2 * (3 * a.nat_degree) : le_double 
  --     ... ≤ 2 * (max (3 * a.nat_degree) (2 * b.nat_degree)) : by simp only [mul_le_mul_left, nat.succ_pos', le_max_iff, le_refl, true_or]
  --     ... = 2 * c.nat_degree : by rw hcdeg,
  --     {simp only [add_le_add_iff_left, le_mul_iff_one_le_right, nat.succ_pos'], exact hadeg, },
  --   end,
  --   tauto,
  -- },
end

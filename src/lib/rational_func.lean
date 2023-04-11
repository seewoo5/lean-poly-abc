import tactic.core
import ring_theory.euclidean_domain
import ring_theory.polynomial.content
-- for no_zero_divisors instance
import algebra.euclidean_domain.basic
import data.polynomial.ring_division
import algebra.euclidean_domain.instances
import data.polynomial.field_division
import algebra.associated

import ring_theory.unique_factorization_domain
import field_theory.ratfunc


noncomputable theory
open_locale classical polynomial

open ratfunc

variables {k: Type*} [field k]

private lemma aux_is_unit {a : k[X]} (ha : a ≠ 0) : 
  is_unit (polynomial.C (a.leading_coeff⁻¹)) :=
begin
  rw polynomial.is_unit_C, 
  apply is_unit.inv,
  rw ←polynomial.leading_coeff_ne_zero at ha, 
  exact ne.is_unit ha,
end

private lemma div_mul_eq {a b : k[X]} (h : a ∣ b) : 
  b / a * a = b :=
begin
  rw ←euclidean_domain.mod_eq_zero at h,
  have t := euclidean_domain.div_add_mod b a,
  rw [h, add_zero, mul_comm] at t, exact t,
end

theorem is_coprime.num_denom (x : ratfunc k) : is_coprime x.num x.denom :=
begin
  apply ratfunc.induction_on x,
  intros p q q_nz,
  rw [ratfunc.num_div, ratfunc.denom_div _ q_nz],
  have hnz : q / gcd p q ≠ 0 := begin 
    intro h, apply q_nz,
    rw ←(div_mul_eq (gcd_dvd_right p q)),
    rw [h, zero_mul],
  end,
  rw is_coprime_mul_unit_left_left 
    (aux_is_unit hnz) (p / gcd p q) _,
  rw is_coprime_mul_unit_left_right 
    (aux_is_unit hnz) (p / gcd p q) _,
  clear hnz,
  rw ←gcd_is_unit_iff,
  have hnz : gcd p q ≠ 0 := gcd_ne_zero_of_right _ _ q_nz,
  refine is_unit_of_associated_mul _ hnz,
  apply associated.trans (gcd_mul_left' _ _ _).symm,
  rw [mul_comm (gcd p q), mul_comm (gcd p q)],
  rw [div_mul_eq (gcd_dvd_left p q), div_mul_eq (gcd_dvd_right p q)],
end

def is_const (x : ratfunc k) := ∃ c : k, x = ratfunc.C c

theorem associates_pow_eq_pow_iff {A B : associates k[X]} {n : ℕ} 
  (hn : 0 < n) : A^n = B^n ↔ A = B :=
begin
  by_cases hA : A = 0,
  { subst hA, 
    rw [zero_pow hn, eq_comm, pow_eq_zero_iff hn, eq_comm],
    exact associates.no_zero_divisors, },
  by_cases hB : B = 0,
  { subst hB, 
    rw [zero_pow hn, pow_eq_zero_iff hn],
    exact associates.no_zero_divisors, },

  split, swap,
  { intro h, subst h, },
  intro h,
  apply associates.eq_of_eq_counts hA hB,
  intros p hp,
  apply nat.eq_of_mul_eq_mul_left hn,
  rw [←associates.count_pow hA hp n,
    ←associates.count_pow hB hp n, h],
end

example (p q : ℕ) (f: ℕ -> ℕ) (h : p = q) : f p = f q := congr_arg f h

lemma is_const_of_associated {f : ratfunc k} (h : associated f.num f.denom) : 
  is_const f := 
begin
  rcases h.symm with ⟨u, heq⟩,
  rcases (polynomial.is_unit_iff.mp u.is_unit) with ⟨c, uc, eq_c⟩,
  rw ←eq_c at heq,
  have tt := congr_arg (algebra_map (polynomial k) (ratfunc k)) heq.symm,
  rw [map_mul, mul_comm] at tt,
  have uu := div_eq_of_eq_mul (algebra_map_ne_zero f.denom_ne_zero) tt,
  rw [f.num_div_denom, ratfunc.algebra_map_C] at uu,
  use c, exact uu,
end

lemma is_const_of_root_unity {n : ℕ} (hn : 0 < n) {f : ratfunc k}
  (h : f^n = 1) : is_const f :=
begin
  rw [←f.num_div_denom, div_pow, ←map_pow, ←map_pow] at h,
  have nz : algebra_map k[X] (ratfunc k) (f.denom ^ n) ≠ 0,
  apply algebra_map_ne_zero, apply pow_ne_zero, exact f.denom_ne_zero,
  rw [←mul_left_inj' nz, div_mul_cancel 
    (algebra_map k[X] (ratfunc k) (f.num ^ n)) nz, one_mul] at h,
  have hh := congr_arg associates.mk (algebra_map_injective k h),
  rw [associates.mk_pow, associates.mk_pow,
    associates_pow_eq_pow_iff hn,
    associates.mk_eq_mk_iff_associated] at hh, 
  exact is_const_of_associated hh,
end

theorem associated_pow_pow_coprime_iff {a b : k[X]} {m n : ℕ}
  (ha : a ≠ 0) (hb : b ≠ 0) (hm : 0 < m) (hn : 0 < n)
  (h : associated (a^m) (b^n)) (hcp : m.coprime n)
  : ∃ c : k[X], c ≠ 0 ∧ associated a (c^n) ∧ associated b (c^m) :=
begin
  -- change to associates
  simp_rw [←associates.mk_eq_mk_iff_associated,
    associates.mk_pow] at ⊢ h,
  rw ←associates.mk_ne_zero at ha hb,
  set A := associates.mk a with eq_A,
  set B := associates.mk b with eq_B,
  rw ←eq_A at ha, rw ←eq_B at hb,
  rename ha hA, rename hb hB,
  clear_value A B, clear' eq_A eq_B a b,
  suffices goal : ∃ C, A = C^n ∧ B = C^m,
  rcases goal with ⟨C, hC⟩,
  use C.out, simp only [associates.mk_out],
  refine ⟨_, hC⟩,
  rw [←associates.mk_ne_zero, associates.mk_out,
    ←pow_ne_zero_iff hn, ←hC.1],
  exact hA, exact associates.no_zero_divisors,
  
  have subgoal : ∃ C, A = C^n,
  { apply associates.is_pow_of_dvd_count hA,
    intros p hp,
    apply hcp.symm.dvd_of_dvd_mul_left,
    rw [←associates.count_pow hA hp, h, associates.count_pow hB hp],
    exact nat.dvd_mul_right _ _, },
  
  rcases subgoal with ⟨C, eq_ACn⟩,
  refine ⟨C, eq_ACn, _⟩,
  rw [eq_ACn, pow_right_comm,
    associates_pow_eq_pow_iff hn] at h,
  exact h.symm,
end

import tactic.core
import ring_theory.euclidean_domain
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain
import field_theory.ratfunc

import .flt_catalan

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

namespace unique_factorization_monoid

theorem associated_pow_pow_iff {a b : k[X]} {m n : ℕ}
  (h : associated (a^m) (b^n)) (hcp : m.coprime n)
  : ∃ 

end unique_factorization_monoid

theorem no_parametrization_y2_x3_1 
  {x y : ratfunc k} (eqn : y^2 = x^3 + 1) : is_const x ∧ is_const y :=
begin
  have eq_x := x.num_div_denom.symm,
  have eq_y := y.num_div_denom.symm,
  have nz_M := x.denom_ne_zero,
  have nz_N := y.denom_ne_zero,
  have cp_mM := is_coprime.num_denom x,
  have cp_nN := is_coprime.num_denom y,

  set m := x.num with eq_m,
  set M := x.denom with eq_M,
  set n := y.num with eq_n,
  set N := y.denom with eq_N,
  clear_value m M n N,
  rw [eq_x, eq_y] at eqn,
  simp only [div_pow] at eqn,

  revert m M n N eq_m eq_M eq_n eq_N nz_M nz_N eq_x eq_y eqn cp_mM cp_nN,
  intros m M n N eq_m eq_M eq_n eq_N nz_M nz_N eq_x eq_y eqn cp_mM cp_nN,

  have flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2,
  { have nz_rM := ratfunc.algebra_map_ne_zero nz_M,
    have nz_rN := ratfunc.algebra_map_ne_zero nz_N,
    rw ←(ratfunc.algebra_map_injective k).eq_iff,
    simp_rw [ring_hom.map_mul, ring_hom.map_add, ring_hom.map_pow],
    set rm := algebra_map k[X] (ratfunc k) m with eq_rm,
    set rM := algebra_map k[X] (ratfunc k) M with eq_rM,
    set rn := algebra_map k[X] (ratfunc k) n with eq_rn,
    set rN := algebra_map k[X] (ratfunc k) N with eq_rN,
    rw [←eq_rm, ←eq_rM, ←eq_rn, ←eq_rN],
    calc rn^2 * rM^3 = rn^2 / rN^2 * rN^2 * rM^3 : 
        by rw div_mul_cancel _ (pow_ne_zero 2 nz_rN)
      ... = (rm^3 / rM^3 + 1) * rM^3 * rN^2 :
        by rw eqn; ring_nf
      ... = (rm^3 + rM^3) * rN^2 :
        by rw [add_mul, div_mul_cancel _ (pow_ne_zero 3 nz_rM), one_mul], },
  clear eqn,

  have assoc_M3_N2 : associated (M^3) (N^2),
  { apply associated_of_dvd_dvd,
    { have cp : is_coprime (M^3) (m^3+1*M^3) := 
        cp_mM.symm.pow.add_mul_right_right 1,
      rw one_mul at cp,
      apply cp.dvd_of_dvd_mul_left,
      rw ←flat_eqn, exact dvd_mul_left _ _, },
    { have cp : is_coprime (N^2) (n^2) := cp_nN.symm.pow,
      apply cp.dvd_of_dvd_mul_left,
      rw flat_eqn, exact dvd_mul_left _ _, }, },
    
  -- TODO: x is mk m M and y is mk n N
  -- TODO: is_const x if and only if m M are associated
  -- associated_of_dvd_dvd -> N^2 and M^3 dividing each other gives associated
  -- power -> all exponentials divided by 2 and 3

  -- have coe_rm : rm = ↑m := eq_rm,
  -- have coe_rM : rM = ↑M := eq_rM,
  -- have coe_rn : rn = ↑n := eq_rn,
  -- have coe_rN : rN = ↑N := eq_rN,
  -- rw [coe_rm, coe_rM, coe_rn, coe_rN] at flat_eqn,
  -- simp_rw [←algebra_map.coe_pow,
  --   ←algebra_map.coe_add,
  --   ←algebra_map.coe_mul] at flat_eqn,
  
  sorry,
end
import .flt_catalan
import ..lib.rational_func

noncomputable theory
open_locale classical polynomial

open ratfunc

variables {k: Type*} [field k]


lemma calcstep {n N m M : k[X]}
  (nz_M : M ≠ 0) (nz_N : N ≠ 0)
  (eqn : (algebra_map _ (ratfunc k)) n ^ 2 / (algebra_map _ (ratfunc k)) N ^ 2 =
    (algebra_map _ (ratfunc k)) m ^ 3 / (algebra_map _ (ratfunc k)) M ^ 3 + 1) : 
  n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2 :=
begin
  have nz_rM := ratfunc.algebra_map_ne_zero nz_M,
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
      by rw [eqn, mul_assoc, mul_assoc, mul_comm (rN^2) _]
    ... = (rm^3 + rM^3) * rN^2 :
      by rw [add_mul, div_mul_cancel _ (pow_ne_zero 3 nz_rM), one_mul],
end

lemma calcstep2 
  {m M n N : k[X]} (nz_M : M ≠ 0) (nz_N : N ≠ 0)
  (cp_mM : is_coprime m M)
  (cp_nN : is_coprime n N)
  (nz_m : m ≠ 0)
  (nz_n : n ≠ 0)
  (flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2) : 
  ∃ (w : k[X]) (u v : k[X]ˣ), w ≠ 0 ∧ ↑u * w ^ 2 = M ∧ ↑v * w ^ 3 = N ∧ is_coprime m w ∧ 
    ↑(u ^ 3) * n ^ 2 = ↑(v ^ 2) * m ^ 3 + ↑(v ^ 2 * u ^ 3) * w ^ 6 :=
begin
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
  
  rcases (associated_pow_pow_coprime_iff nz_M nz_N 
  dec_trivial _ assoc_M3_N2 (by norm_num))
    with ⟨w, nz_w, assoc_M_w2, assoc_N_w3⟩,
  swap, dec_trivial,
  rcases assoc_M_w2.symm with ⟨u, eq_Mw⟩, rw mul_comm at eq_Mw,
  rcases assoc_N_w3.symm with ⟨v, eq_Nw⟩, rw mul_comm at eq_Nw,

  refine ⟨w, u, v, nz_w, eq_Mw, eq_Nw, _⟩,

  simp_rw [←eq_Mw, ←eq_Nw, mul_pow, ←pow_mul, ←mul_assoc] at flat_eqn,
  ring_nf at flat_eqn,
  rw mul_left_inj' (pow_ne_zero 6 nz_w) at flat_eqn,
  rw [mul_comm _ (↑v ^ 2), 
    left_distrib (↑v ^ 2) (m^3) _,
    ←mul_assoc] at flat_eqn,
  simp_rw [←units.coe_pow, ←units.coe_mul] at flat_eqn,
  have cp_mw : is_coprime m w,
  { rw [←eq_Mw, is_coprime_mul_unit_left_right u.is_unit,
      is_coprime.pow_right_iff] at cp_mM, 
    exact cp_mM, dec_trivial }, refine ⟨cp_mw, flat_eqn⟩, 
end

theorem no_parametrization_y2_x3_1 (chk : ¬(ring_char k ∣ 6))
  {x y : ratfunc k} (eqn : y^2 = x^3 + 1) : is_const x ∧ is_const y :=
begin
  cases eq_or_ne x 0 with eq_x nz_x,
  { subst x, 
    rw [zero_pow', zero_add] at eqn, swap, dec_trivial,
    refine ⟨⟨0, (map_zero _).symm⟩, is_const_of_root_unity _ eqn⟩,
    dec_trivial },
  cases eq_or_ne y 0 with eq_y nz_y,
  { subst y, rw [eq_comm, zero_pow', ←eq_neg_iff_add_eq_zero] at eqn,
    swap, dec_trivial,
    have tt : (x^3)^2 = 1, rw sq_eq_one_iff, right, exact eqn,
    ring_nf at tt,
    refine ⟨is_const_of_root_unity _ tt, ⟨0, (map_zero _).symm⟩⟩,
    dec_trivial },

  have eq_x := x.num_div_denom.symm,
  have eq_y := y.num_div_denom.symm,
  have nz_m := num_ne_zero nz_x,
  have nz_n := num_ne_zero nz_y,
  have nz_M := x.denom_ne_zero,
  have nz_N := y.denom_ne_zero,
  have cp_mM := is_coprime.num_denom x,
  have cp_nN := is_coprime.num_denom y,

  set m := x.num,
  set M := x.denom,
  set n := y.num,
  set N := y.denom,
  clear_value m M n N,
  rw [eq_x, eq_y] at eqn,
  simp only [div_pow] at eqn,
  subst eq_x, subst eq_y,
 
  have flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2,
  { apply calcstep; assumption },
  clear eqn,

  have eqn2 : 
  ∃ (w : k[X]) (u v : k[X]ˣ), w ≠ 0 ∧ ↑u * w ^ 2 = M ∧ ↑v * w ^ 3 = N ∧ is_coprime m w ∧ 
    ↑(u ^ 3) * n ^ 2 = ↑(v ^ 2) * m ^ 3 + ↑(v ^ 2 * u ^ 3) * w ^ 6,
  { apply calcstep2; assumption },
  clear flat_eqn, 
  rcases eqn2 with ⟨w, u, v, nz_w, eq_M, eq_N, cp_mw, eqn2⟩, 
  have chk2 : ¬ring_char k ∣ 2,
  { intro h, apply chk, apply h.trans, use 3, norm_num, },
  have chk3 : ¬ring_char k ∣ 3,
  { intro h, apply chk, apply h.trans, use 2, norm_num, },

  rw [eq_comm, ←sub_eq_zero, sub_eq_add_neg, ←neg_mul, ←units.coe_neg] at eqn2,
  have deriv_eq_zero := polynomial.flt_catalan 
    _ _ _ _ chk3 chk chk2 nz_m nz_w nz_n cp_mw eqn2,
  rcases deriv_eq_zero with ⟨eq_dm, eq_dw, eq_dn⟩,
  split,
  { rw (polynomial.eq_C_of_nat_degree_eq_zero eq_dm),
    rw ←eq_M, rw (polynomial.eq_C_of_nat_degree_eq_zero eq_dw),
    rcases polynomial.is_unit_iff.mp u.is_unit with ⟨cu, -, eq_cu⟩,
    rw ←eq_cu, rw [←map_pow, ←map_mul, ratfunc.algebra_map_C,
      ratfunc.algebra_map_C, ←map_div₀, is_const], existsi _, refl, },
  { rw (polynomial.eq_C_of_nat_degree_eq_zero eq_dn),
    rw ←eq_N, rw (polynomial.eq_C_of_nat_degree_eq_zero eq_dw),
    rcases polynomial.is_unit_iff.mp v.is_unit with ⟨cv, -, eq_cv⟩,
    rw ←eq_cv, rw [←map_pow, ←map_mul, ratfunc.algebra_map_C,
      ratfunc.algebra_map_C, ←map_div₀, is_const], existsi _, refl, },
  iterate 4 { norm_num }, 
end

import LeanPolyABC.Corollaries.FltCatalan
import LeanPolyABC.Lib.RationalFunc

#align_import corollaries.no_parametrization

noncomputable section

open scoped Classical Polynomial

open RatFunc

variable {k : Type _} [Field k]

theorem calcstep {n N m M : k[X]} (nz_M : M ≠ 0) (nz_N : N ≠ 0)
    (eqn :
      (algebraMap _ (RatFunc k)) n ^ 2 / (algebraMap _ (RatFunc k)) N ^ 2 =
        (algebraMap _ (RatFunc k)) m ^ 3 / (algebraMap _ (RatFunc k)) M ^ 3 + 1) :
    n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2 :=
  by
  have nz_rM := RatFunc.algebraMap_ne_zero nz_M
  have nz_rN := RatFunc.algebraMap_ne_zero nz_N
  rw [← (RatFunc.algebraMap_injective k).eq_iff]
  simp_rw [RingHom.map_mul, RingHom.map_add, RingHom.map_pow]
  set rm := algebraMap k[X] (RatFunc k) m with eq_rm
  set rM := algebraMap k[X] (RatFunc k) M with eq_rM
  set rn := algebraMap k[X] (RatFunc k) n with eq_rn
  set rN := algebraMap k[X] (RatFunc k) N with eq_rN
  rw [← eq_rm, ← eq_rM, ← eq_rn, ← eq_rN]
  calc
    rn ^ 2 * rM ^ 3 = rn ^ 2 / rN ^ 2 * rN ^ 2 * rM ^ 3 := by
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 nz_rN)]
    _ = (rm ^ 3 / rM ^ 3 + 1) * rM ^ 3 * rN ^ 2 := by
      rw [eqn, mul_assoc, mul_assoc, mul_comm (rN ^ 2) _]
    _ = (rm ^ 3 + rM ^ 3) * rN ^ 2 := by
      rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 3 nz_rM), one_mul]

theorem calcstep2 {m M n N : k[X]} (nz_M : M ≠ 0) (nz_N : N ≠ 0) (cp_mM : IsCoprime m M)
    (cp_nN : IsCoprime n N) (nz_m : m ≠ 0) (nz_n : n ≠ 0)
    (flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2) :
    ∃ (w : k[X]) (u v : k[X]ˣ),
      w ≠ 0 ∧
        ↑u * w ^ 2 = M ∧
          ↑v * w ^ 3 = N ∧
            IsCoprime m w ∧ ↑(u ^ 3) * n ^ 2 = ↑(v ^ 2) * m ^ 3 + ↑(v ^ 2 * u ^ 3) * w ^ 6 :=
  by
  have assoc_M3_N2 : Associated (M ^ 3) (N ^ 2) :=
    by
    apply associated_of_dvd_dvd
    · have cp : IsCoprime (M ^ 3) (m ^ 3 + 1 * M ^ 3) := cp_mM.symm.pow.add_mul_right_right 1
      rw [one_mul] at cp
      apply cp.dvd_of_dvd_mul_left
      rw [← flat_eqn]; exact dvd_mul_left _ _
    · have cp : IsCoprime (N ^ 2) (n ^ 2) := cp_nN.symm.pow
      apply cp.dvd_of_dvd_mul_left
      rw [flat_eqn]; exact dvd_mul_left _ _
  rcases associated_pow_pow_coprime_iff nz_M nz_N (by decide) _ assoc_M3_N2 (by norm_num) with
    ⟨w, nz_w, assoc_M_w2, assoc_N_w3⟩
  swap; decide
  rcases assoc_M_w2.symm with ⟨u, eq_Mw⟩; rw [mul_comm] at eq_Mw
  rcases assoc_N_w3.symm with ⟨v, eq_Nw⟩; rw [mul_comm] at eq_Nw
  refine' ⟨w, u, v, nz_w, eq_Mw, eq_Nw, _⟩
  simp_rw [← eq_Mw, ← eq_Nw, mul_pow, ← pow_mul, ← mul_assoc] at flat_eqn
  ring_nf at flat_eqn
  rw [mul_left_inj' (pow_ne_zero 6 nz_w)] at flat_eqn
  rw [mul_comm _ (↑v ^ 2), left_distrib (↑v ^ 2) (m ^ 3) _, ← mul_assoc] at flat_eqn
  simp_rw [← Units.val_pow_eq_pow_val, ← Units.val_mul] at flat_eqn
  have cp_mw : IsCoprime m w :=
    by
    rw [← eq_Mw, isCoprime_mul_unit_left_right u.is_unit, IsCoprime.pow_right_iff] at cp_mM
    exact cp_mM; decide
  refine' ⟨cp_mw, flat_eqn⟩

theorem no_parametrization_y2_x3_1 (chk : ¬ringChar k ∣ 6) {x y : RatFunc k}
    (eqn : y ^ 2 = x ^ 3 + 1) : IsConst x ∧ IsConst y :=
  by
  cases' eq_or_ne x 0 with eq_x nz_x
  · subst x
    rw [zero_pow, zero_add] at eqn; swap; decide
    refine' ⟨⟨0, (map_zero _).symm⟩, isConst_of_root_unity _ eqn⟩
    decide
  cases' eq_or_ne y 0 with eq_y nz_y
  · subst y; rw [eq_comm, zero_pow, ← eq_neg_iff_add_eq_zero] at eqn
    swap; decide
    have tt : (x ^ 3) ^ 2 = 1; rw [sq_eq_one_iff]; right; exact eqn
    ring_nf at tt
    refine' ⟨isConst_of_root_unity _ tt, ⟨0, (map_zero _).symm⟩⟩
    decide
  have eq_x := x.num_div_denom.symm
  have eq_y := y.num_div_denom.symm
  have nz_m := num_ne_zero nz_x
  have nz_n := num_ne_zero nz_y
  have nz_M := x.denom_ne_zero
  have nz_N := y.denom_ne_zero
  have cp_mM := IsCoprime.num_denom x
  have cp_nN := IsCoprime.num_denom y
  set m := x.num
  set M := x.denom
  set n := y.num
  set N := y.denom
  clear_value m M n N
  rw [eq_x, eq_y] at eqn
  simp only [div_pow] at eqn
  subst eq_x; subst eq_y
  have flat_eqn : n ^ 2 * M ^ 3 = (m ^ 3 + M ^ 3) * N ^ 2 := by apply calcstep <;> assumption
  clear eqn
  have eqn2 :
    ∃ (w : k[X]) (u v : k[X]ˣ),
      w ≠ 0 ∧
        ↑u * w ^ 2 = M ∧
          ↑v * w ^ 3 = N ∧
            IsCoprime m w ∧ ↑(u ^ 3) * n ^ 2 = ↑(v ^ 2) * m ^ 3 + ↑(v ^ 2 * u ^ 3) * w ^ 6 :=
    by apply calcstep2 <;> assumption
  clear flat_eqn
  rcases eqn2 with ⟨w, u, v, nz_w, eq_M, eq_N, cp_mw, eqn2⟩
  have chk2 : ¬ringChar k ∣ 2 := by intro h; apply chk; apply h.trans; use 3; norm_num
  have chk3 : ¬ringChar k ∣ 3 := by intro h; apply chk; apply h.trans; use 2; norm_num
  rw [eq_comm, ← sub_eq_zero, sub_eq_add_neg, ← neg_mul, ← Units.val_neg] at eqn2
  have deriv_eq_zero := Polynomial.flt_catalan _ _ _ _ chk3 chk chk2 nz_m nz_w nz_n cp_mw eqn2
  rcases deriv_eq_zero with ⟨eq_dm, eq_dw, eq_dn⟩
  constructor
  · rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dm]
    rw [← eq_M]; rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dw]
    rcases polynomial.is_unit_iff.mp u.is_unit with ⟨cu, -, eq_cu⟩
    rw [← eq_cu];
    rw [← map_pow, ← map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀, IsConst]
    exists _; rfl
  · rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dn]
    rw [← eq_N]; rw [Polynomial.eq_C_of_natDegree_eq_zero eq_dw]
    rcases polynomial.is_unit_iff.mp v.is_unit with ⟨cv, -, eq_cv⟩
    rw [← eq_cv];
    rw [← map_pow, ← map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← map_div₀, IsConst]
    exists _; rfl
  iterate 4 norm_num

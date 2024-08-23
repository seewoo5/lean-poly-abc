import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Logic.Lemmas
import LeanPolyABC.MasonStothers
import Mathlib.RingTheory.Coprime.Basic

noncomputable section

open scoped Polynomial Classical

open Polynomial

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]

-- Multiplying units preserve coprimality
private theorem isCoprime_mul_units_left {a b : k[X]} {u v : k} (hu : u ≠ 0) (hv : v ≠ 0) :
    IsCoprime (C u * a) (C v * b) ↔ IsCoprime a b :=
  Iff.trans
    (isCoprime_mul_unit_left_left hu.isUnit_C _ _)
    (isCoprime_mul_unit_left_right hv.isUnit_C _ _)

private theorem rot_coprime {p q r : ℕ} {a b c : k[X]} {u v w : k}
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) (hab : IsCoprime a b)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) : IsCoprime b c := by
  have uu := hu.isUnit_C
  have uv := hv.isUnit_C
  have uw := hw.isUnit_C

  rw [←IsCoprime.pow_iff hp hq, ←isCoprime_mul_units_left hu hv] at hab
  rw [←IsCoprime.pow_iff hq hr, ←isCoprime_mul_units_left hv hw]

  rw [add_eq_zero_iff_neg_eq] at heq
  rw [←heq, IsCoprime.neg_right_iff]
  convert IsCoprime.add_mul_left_right hab.symm 1 using 2
  rw [mul_one]

private theorem rot3_add {α : Type _} [AddCommMonoid α] {a b c : α} : a + b + c = b + c + a := by
  rw [add_comm (b + c) a]; exact add_assoc _ _ _

private theorem mul3_add {α : Type _} [CommMonoid α] {a b c : α} : a * b * c = b * c * a := by
  rw [mul_comm (b * c) a]; exact mul_assoc _ _ _

lemma weighted_average_le_max₃ {p q r a b c : Nat} :
    p * a + q * b + r * c ≤ (p + q + r) * Nat.max₃ a b c :=
  by
  rw [add_mul, add_mul]
  apply Nat.add_le_add
  apply Nat.add_le_add
  exact Nat.mul_le_mul (Nat.le_refl _) (Nat.le_max₃_left _ _ _)
  exact Nat.mul_le_mul (Nat.le_refl _) (Nat.le_max₃_middle _ _ _)
  exact Nat.mul_le_mul (Nat.le_refl _) (Nat.le_max₃_right _ _ _)

theorem Polynomial.derivative_C_mul {R : Type u}  [Semiring R]  (a : R) (p : R[X]) :
    derivative (C a * p) = C a * derivative p := by
  rw [←smul_eq_C_mul, derivative.map_smul _ _, smul_eq_C_mul]

theorem derivative_pow_eq_zero_iff {n : ℕ} (chn : ¬ringChar k ∣ n) {a : k[X]}  :
    derivative (a ^ n) = 0 ↔ derivative a = 0 :=
  by
  constructor
  · intro apd
    rw [derivative_pow, C_eq_natCast, mul_eq_zero, mul_eq_zero] at apd
    rcases apd with (nz | powz) | goal
    . rw [←C_eq_natCast, C_eq_zero] at nz
      exfalso
      exact chn (ringChar.dvd nz)
    . have az : a = 0 := pow_eq_zero powz
      rw [az, map_zero]
    . exact goal
  · intro hd; rw [derivative_pow, hd, MulZeroClass.mul_zero]

theorem mul_eq_zero_left_iff
    {M₀ : Type*} [MulZeroClass M₀] [NoZeroDivisors M₀]
    {a : M₀} {b : M₀}  (ha : a ≠ 0) : a * b = 0 ↔ b = 0 := by
  rw [mul_eq_zero]
  tauto

theorem Polynomial.flt_catalan_deriv
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
  have hbc : IsCoprime b c := by apply rot_coprime heq <;> assumption
  have hca : IsCoprime c a := by apply rot_coprime (rot3_add.symm.trans heq) <;> assumption
  have hap := mul_ne_zero hu.C_ne_zero (pow_ne_zero p ha)
  have hbp := mul_ne_zero hv.C_ne_zero (pow_ne_zero q hb)
  have hcp := mul_ne_zero hw.C_ne_zero (pow_ne_zero r hc)
  have habp : IsCoprime (C u * a ^ p) (C v * b ^ q) :=
    (isCoprime_mul_units_left hu hv).mpr hab.pow
  have hbcp : IsCoprime (C v * b ^ q) (C w * c ^ r) :=
    (isCoprime_mul_units_left hv hw).mpr hbc.pow
  have hcap : IsCoprime (C w * c ^ r) (C u * a ^ p) :=
    (isCoprime_mul_units_left hw hu).mpr hca.pow
  have habcp := hcap.symm.mul_left hbcp
  cases' Polynomial.abc hap hbp hcp habp heq with dr0 ineq
  case inl dr0 =>
    simp only [derivative_C_mul] at dr0
    rw [mul_eq_zero_left_iff hu.C_ne_zero,
        mul_eq_zero_left_iff hv.C_ne_zero,
        mul_eq_zero_left_iff hw.C_ne_zero,
        derivative_pow_eq_zero_iff chp,
        derivative_pow_eq_zero_iff chq,
        derivative_pow_eq_zero_iff chr] at dr0
    exact dr0
  case inr ineq =>
    rw [Nat.add_one_le_iff] at ineq
    exfalso; apply not_le_of_lt ineq; clear ineq
    -- work on lhs
    rw [radical_hMul habcp, radical_hMul habp]
    rw [radical_mul_unit_left hu.isUnit_C,
        radical_mul_unit_left hv.isUnit_C,
        radical_mul_unit_left hw.isUnit_C]
    rw [radical_pow a hp, radical_pow b hq, radical_pow c hr]
    rw [← radical_hMul hab, ← radical_hMul (hca.symm.mul_left hbc)]
    apply le_trans radical_natDegree_le
    rw [natDegree_mul (mul_ne_zero ha hb) hc]
    rw [natDegree_mul ha hb]
    -- work on rhs
    rw [mul_ne_zero_iff] at hap hbp hcp
    rw [natDegree_mul hap.left hap.right]
    rw [natDegree_mul hbp.left hbp.right]
    rw [natDegree_mul hcp.left hcp.right]
    simp only [natDegree_C, natDegree_pow, zero_add]
    have hpqr : 0 < p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
    apply le_of_mul_le_mul_left _ hpqr
    apply le_trans _ (Nat.mul_le_mul_right _ hineq)
    convert weighted_average_le_max₃ using 1
    ring_nf

private theorem expcont {a : k[X]} (ha : a ≠ 0) (hda : derivative a = 0) (chn0 : ringChar k ≠ 0) :
    ∃ ca, ca ≠ 0 ∧ a = expand k (ringChar k) ca ∧ a.natDegree = ca.natDegree * ringChar k :=
  by
  have heq := (expand_contract (ringChar k) hda chn0).symm
  refine' ⟨_, _, heq, _⟩
  · intro h; rw [h] at heq; simp only [map_zero] at heq; solve_by_elim
  · rw [←natDegree_expand, ←heq]

private theorem expand_dvd {a b : k[X]} {n : ℕ} (hn : n ≠ 0) (h : a ∣ b) :
    expand k n a ∣ expand k n b := by
  rcases h with ⟨t, eqn⟩
  use expand k n t; rw [eqn, map_mul]

private theorem is_coprime_of_expand {a b : k[X]} {n : ℕ} (hn : n ≠ 0) :
    IsCoprime (expand k n a) (expand k n b) → IsCoprime a b :=
  by
  simp_rw [← EuclideanDomain.gcd_isUnit_iff]
  rw [← not_imp_not]; intro h
  cases' EuclideanDomain.gcd_dvd a b with ha hb
  have hh := EuclideanDomain.dvd_gcd (expand_dvd hn ha) (expand_dvd hn hb)
  intro h'; apply h; have tt := isUnit_of_dvd_unit hh h'
  rw [Polynomial.isUnit_iff] at tt ⊢
  rcases tt with ⟨zz, yy⟩; rw [eq_comm, expand_eq_C (zero_lt_iff.mpr hn), eq_comm] at yy
  refine' ⟨zz, yy⟩

theorem Polynomial.flt_catalan_aux
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r)
    (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
    {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
    a.natDegree = 0 :=
  by
  have hbc : IsCoprime b c := by
    apply rot_coprime <;> assumption
  have hbc : IsCoprime c a := by
    apply rot_coprime (rot3_add.symm.trans heq) <;> assumption
  cases' eq_or_ne (ringChar k) 0 with ch0 chn0
  -- Characteristic zero
  · have hderiv : derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
      apply Polynomial.flt_catalan_deriv hp hq hr hineq _ _ _ ha hb hc _ hu hv hw <;> assumption
    rcases hderiv with ⟨da, -, -⟩
    have ii : CharZero k := by
      apply charZero_of_inj_zero; intro n; rw [ringChar.spec]
      rw [ch0]; exact zero_dvd_iff.mp
    have tt := eq_C_of_derivative_eq_zero da
    rw [tt]; exact natDegree_C _
  /- Characteristic ch ≠ 0, where we use infinite descent.
    We use proof by contradiction (`by_contra`) combined with strong induction
    (`Nat.case_strong_induction_on`) to formalize the proof.
    -/
  . set d := a.natDegree with eq_d;
    clear_value d; by_contra hd
    revert a b c eq_d hd
    induction' d using Nat.case_strong_induction_on with d ih_d
    · intros; tauto
    intros a b c ha hb hc hab heq hbc hca eq_d hd
    have hderiv : derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0 := by
      apply Polynomial.flt_catalan_deriv hp hq hr _ _ _ _ ha hb hc _ hu hv hw <;> assumption
    rcases hderiv with ⟨ad, bd, cd⟩
    rcases expcont ha ad chn0 with ⟨ca, ca_nz, eq_a, eq_deg_a⟩
    rcases expcont hb bd chn0 with ⟨cb, cb_nz, eq_b, eq_deg_b⟩
    rcases expcont hc cd chn0 with ⟨cc, cc_nz, eq_c, eq_deg_c⟩
    set ch := ringChar k with eq_ch
    apply @ih_d ca.natDegree _ ca cb cc ca_nz cb_nz cc_nz <;> clear ih_d <;> try rfl
    · apply is_coprime_of_expand chn0; rw [← eq_a, ← eq_b]; exact hab
    · rw [eq_a, eq_b, eq_c, ←expand_C ch u, ←expand_C ch v, ←expand_C ch w] at heq
      simp_rw [← map_pow, ← map_mul, ← map_add] at heq
      rw [Polynomial.expand_eq_zero (zero_lt_iff.mpr chn0)] at heq
      exact heq
    · apply is_coprime_of_expand chn0; rw [← eq_b, ← eq_c]; exact hbc
    · apply is_coprime_of_expand chn0; rw [← eq_c, ← eq_a]; exact hca
    . rw [eq_d, eq_deg_a] at hd; exact (mul_ne_zero_iff.mp hd).1
    . have hch1 : ch ≠ 1 := by rw [eq_ch]; exact CharP.ringChar_ne_one
      clear eq_ch; clear_value ch
      have hch2 : 2 ≤ ch := by omega
      -- Why can't a single omega handle things from here?
      rw [←Nat.succ_le_succ_iff]
      rw [eq_d, eq_deg_a] at hd ⊢
      rw [mul_eq_zero, not_or] at hd
      rcases hd with ⟨ca_nz, _⟩
      rw [Nat.succ_le_iff]
      rewrite (config := {occs := .pos [1]}) [←Nat.mul_one ca.natDegree]
      rw [Nat.mul_lt_mul_left]
      tauto
      omega

  theorem Polynomial.flt_catalan
      {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
      (hineq : q * r + r * p + p * q ≤ p * q * r)
      (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q) (chr : ¬ringChar k ∣ r)
      {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b)
      {u v w : k} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
      (heq : C u * a ^ p + C v * b ^ q + C w * c ^ r = 0) :
      a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
    by
    -- WLOG argument: essentially three times flt_catalan_aux
    have hbc : IsCoprime b c := by apply rot_coprime heq hab <;> assumption
    have hca : IsCoprime c a := by apply rot_coprime (rot3_add.symm.trans heq) hbc <;> assumption
    refine' ⟨_, _, _⟩
    · apply Polynomial.flt_catalan_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq <;> try assumption
    · rw [rot3_add] at heq hineq; rw [mul3_add] at hineq
      apply Polynomial.flt_catalan_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq <;> try assumption
    · rw [← rot3_add] at heq hineq; rw [← mul3_add] at hineq
      apply Polynomial.flt_catalan_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq <;> try assumption

/- FLT is special case of nonsolvability of Fermat-Catalan equation.
Take p = q = r = n and u = v = 1, w = -1.
-/
theorem Polynomial.flt
    {n : ℕ} (hn : 3 ≤ n) (chn : ¬ringChar k ∣ n)
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  by
  have hn' : 0 < n := by linarith
  rw [← sub_eq_zero, ← one_mul (a ^ n), ← one_mul (b ^ n), ← one_mul (c ^ n), sub_eq_add_neg, ←
    neg_mul] at heq
  have hone : (1 : k[X]) = C 1 := by rfl
  have hneg_one : (-1 : k[X]) = C (-1) := by simp only [map_neg, map_one]
  simp_rw [hneg_one, hone] at heq
  apply Polynomial.flt_catalan hn' hn' hn' _
    chn chn chn ha hb hc hab one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq
  have eq_lhs : n * n + n * n + n * n = 3 * n * n := by ring_nf
  rw [eq_lhs]; rw [mul_assoc, mul_assoc]
  apply Nat.mul_le_mul_right (n * n); exact hn

import Algebra.CharP.Defs
import Algebra.EuclideanDomain.Defs
import RingTheory.MvPowerSeries.Basic
import Algebra.Polynomial.Expand
import Logic.Lemmas
import MasonStothers

#align_import corollaries.flt_catalan

noncomputable section

open scoped Polynomial Classical

open Polynomial

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]

-- Units of k[X] are nonzero.
private theorem unit_ne_zero {u : k[X]ˣ} : (↑u : k[X]) ≠ 0 :=
  by
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩
  rw [← er, Ne.def, C_eq_zero, ← Ne.def]
  rw [isUnit_iff_ne_zero] at hr
  exact hr

-- Units of k[X] have degree 0.
private theorem unit_nat_degree_zero {u : k[X]ˣ} : (↑u : k[X]).natDegree = 0 :=
  by
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩
  rw [← er]; exact Polynomial.natDegree_C r

-- For a unit u and a polynomial a, (ua)' = u * a'
private theorem derivative_unit_mul {u : k[X]ˣ} (a : k[X]) :
    (↑u * a).derivative = ↑u * a.derivative :=
  by
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩
  rw [← er]; simp only [derivative_mul, derivative_C, MulZeroClass.zero_mul, zero_add]

-- Multiplying units preserve coprimality
private theorem is_coprime.mul_units_left {a b : k[X]} {u v : k[X]ˣ} (h : IsCoprime a b) :
    IsCoprime (↑u * a) (↑v * b) := by
  rw [isCoprime_mul_unit_left_left u.is_unit, isCoprime_mul_unit_left_right v.is_unit] <;> exact h

private theorem rot_coprime {p q r : ℕ} {a b c : k[X]} {u v w : k[X]ˣ}
    (heq : ↑u * a ^ p + ↑v * b ^ q + ↑w * c ^ r = 0) (hab : IsCoprime a b) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) : IsCoprime b c :=
  by
  rw [add_eq_zero_iff_neg_eq, ← Units.inv_mul_eq_iff_eq_mul, mul_neg, mul_add, ← mul_assoc, ←
    mul_assoc, ← Units.val_mul, ← Units.val_mul] at heq
  rw [← IsCoprime.pow_left_iff hq, ← IsCoprime.pow_right_iff hr, ← HEq, IsCoprime.neg_right_iff]
  refine' IsCoprime.add_mul_right_right _ ↑(w⁻¹ * v)
  rw [isCoprime_mul_unit_left_right (w⁻¹ * u).IsUnit]
  exact hab.symm.pow

private theorem rot3_add {α : Type _} [AddCommMonoid α] {a b c : α} : a + b + c = b + c + a := by
  rw [add_comm (b + c) a]; exact add_assoc _ _ _

private theorem mul3_add {α : Type _} [CommMonoid α] {a b c : α} : a * b * c = b * c * a := by
  rw [mul_comm (b * c) a]; exact mul_assoc _ _ _

theorem Polynomial.flt_catalan_deriv {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r) (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q)
    (chr : ¬ringChar k ∣ r) {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k[X]ˣ} (heq : ↑u * a ^ p + ↑v * b ^ q + ↑w * c ^ r = 0) :
    a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0 :=
  by
  have hbc : IsCoprime b c := by apply rot_coprime HEq hab <;> assumption
  have hca : IsCoprime c a := by apply rot_coprime (rot3_add.symm.trans HEq) hbc <;> assumption
  have hap : a ^ p ≠ 0 := pow_ne_zero _ ha
  have hbp : b ^ q ≠ 0 := pow_ne_zero _ hb
  have hcp : c ^ r ≠ 0 := pow_ne_zero _ hc
  have habp : IsCoprime (↑u * a ^ p) (↑v * b ^ q) := hab.pow.mul_units_left
  have hbcp : IsCoprime (↑v * b ^ q) (↑w * c ^ r) := hbc.pow.mul_units_left
  have hcap : IsCoprime (↑w * c ^ r) (↑u * a ^ p) := hca.pow.mul_units_left
  have habcp := hcap.symm.mul_left hbcp
  cases'
    Polynomial.abc (mul_ne_zero unit_ne_zero hap) (mul_ne_zero unit_ne_zero hbp)
      (mul_ne_zero unit_ne_zero hcp) habp hbcp hcap HEq with
    ineq dr0
  swap
  · simp_rw [derivative_unit_mul, Units.mul_right_eq_zero] at dr0
    rw [pow_derivative_eq_zero chp ha, pow_derivative_eq_zero chq hb,
      pow_derivative_eq_zero chr hc] at dr0
    exact dr0
  rw [Nat.add_one_le_iff] at ineq
  exfalso; apply not_le_of_lt ineq; clear ineq
  -- work on lhs
  rw [radical_mul habcp, radical_mul habp]
  simp_rw [radical_unit_mul]
  rw [radical_pow a hp, radical_pow b hq, radical_pow c hr]
  rw [← radical_mul hab, ← radical_mul (hca.symm.mul_left hbc)]
  apply le_trans radical_nat_degree_le
  rw [nat_degree_mul (mul_ne_zero ha hb) hc]
  rw [nat_degree_mul ha hb]
  -- work on rhs
  rw [nat_degree_mul unit_ne_zero hap]
  rw [nat_degree_mul unit_ne_zero hbp]
  rw [nat_degree_mul unit_ne_zero hcp]
  simp_rw [Polynomial.natDegree_pow, unit_nat_degree_zero, zero_add]
  have hpqr : 0 < p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
  apply le_of_mul_le_mul_left _ hpqr
  apply le_trans _ (Nat.mul_le_mul_right _ hineq)
  convert weighted_average_le_max3
  ring_nf

private theorem expcont {a : k[X]} (ha : a ≠ 0) (hda : a.derivative = 0) (chn0 : ringChar k ≠ 0) :
    ∃ ca, ca ≠ 0 ∧ a = expand k (ringChar k) ca ∧ a.natDegree = ca.natDegree * ringChar k :=
  by
  have heq := (expand_contract (ringChar k) hda chn0).symm
  refine' ⟨_, _, HEq, _⟩
  · intro h; rw [h] at heq; simp only [map_zero] at heq; solve_by_elim
  · convert nat_degree_expand _ _

private theorem expand_dvd {a b : k[X]} {n : ℕ} (hn : n ≠ 0) (h : a ∣ b) :
    expand k n a ∣ expand k n b := by
  rcases h with ⟨t, eqn⟩
  use expand k n t; rw [eqn, map_mul]

private theorem expand_unit (u : k[X]ˣ) {n : ℕ} (hn : n ≠ 0) : expand k n ↑u = ↑u :=
  by
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨c, hc, eqc⟩
  simp_rw [← eqc, Polynomial.expand_C]

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

theorem Polynomial.flt_catalan_aux {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r) (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q)
    (chr : ¬ringChar k ∣ r) {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k[X]ˣ} (heq : ↑u * a ^ p + ↑v * b ^ q + ↑w * c ^ r = 0) :
    a.natDegree = 0 :=
  by
  have hbc : IsCoprime b c := by apply rot_coprime HEq hab <;> assumption
  have hca : IsCoprime c a := by apply rot_coprime (rot3_add.symm.trans HEq) hbc <;> assumption
  cases' eq_or_ne (ringChar k) 0 with ch0 chn0
  -- Characteristic zero
  · have hderiv : a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0 := by
      apply Polynomial.flt_catalan_deriv hp hq hr <;> assumption
    rcases hderiv with ⟨da, -, -⟩
    have ii : CharZero k
    apply charZero_of_inj_zero; intro n; rw [ringChar.spec]
    rw [ch0]; exact zero_dvd_iff.mp
    have tt := eq_C_of_derivative_eq_zero da
    rw [tt]; exact nat_degree_C _
  /- Characteristic ch ≠ 0, where we use infinite descent.
    We use proof by contradiction (`by_contra`) combined with strong induction
    (`nat.case_strong_induction_on`) to formalize the proof.
    -/
  set d := a.nat_degree with eq_d;
  clear_value d; by_contra hd
  revert a b c eq_d hd
  induction' d using Nat.case_strong_induction_on with d ih_d
  · intros; apply hd; rfl
  intro a b c eq_d hd ha hb hc hab heq hbc hca
  have hderiv : a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0 := by
    apply Polynomial.flt_catalan_deriv hp hq hr <;> assumption
  rcases hderiv with ⟨ad, bd, cd⟩
  rcases expcont ha ad chn0 with ⟨ca, ca_nz, eq_a, eq_deg_a⟩
  rcases expcont hb bd chn0 with ⟨cb, cb_nz, eq_b, eq_deg_b⟩
  rcases expcont hc cd chn0 with ⟨cc, cc_nz, eq_c, eq_deg_c⟩
  set ch := ringChar k with eq_ch
  apply @ih_d ca.nat_degree _ ca cb cc rfl <;> clear ih_d <;> try assumption
  · intro h; rw [h, MulZeroClass.zero_mul] at eq_deg_a; apply hd; rw [eq_d]; exact eq_deg_a
  · apply is_coprime_of_expand chn0; rw [← eq_a, ← eq_b]; exact hab
  · rw [eq_a, eq_b, eq_c, ← expand_unit u chn0, ← expand_unit v chn0, ← expand_unit w chn0] at heq
    simp_rw [← map_pow, ← map_mul, ← map_add] at heq
    rw [Polynomial.expand_eq_zero (zero_lt_iff.mpr chn0)] at heq
    exact HEq
  · apply is_coprime_of_expand chn0; rw [← eq_b, ← eq_c]; exact hbc
  · apply is_coprime_of_expand chn0; rw [← eq_c, ← eq_a]; exact hca
  rw [← Nat.lt_succ_iff, eq_d, eq_deg_a]
  rw [eq_d, eq_deg_a] at hd; have tt := (mul_ne_zero_iff.mp hd).1
  conv_lhs => rw [← mul_one ca.nat_degree]
  apply Nat.mul_lt_mul_of_pos_left
  · have hch : ch ≠ 1; rw [eq_ch]; exact CharP.ringChar_ne_one
    clear_value ch; cases ch; tauto; cases ch; tauto; decide
  exact zero_lt_iff.mpr tt

theorem Polynomial.flt_catalan {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hineq : q * r + r * p + p * q ≤ p * q * r) (chp : ¬ringChar k ∣ p) (chq : ¬ringChar k ∣ q)
    (chr : ¬ringChar k ∣ r) {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) {u v w : k[X]ˣ} (heq : ↑u * a ^ p + ↑v * b ^ q + ↑w * c ^ r = 0) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  by
  -- WLOG argument: essentially three times flt_catalan_aux
  have hbc : IsCoprime b c := by apply rot_coprime HEq hab <;> assumption
  have hca : IsCoprime c a := by apply rot_coprime (rot3_add.symm.trans HEq) hbc <;> assumption
  refine' ⟨_, _, _⟩
  · apply Polynomial.flt_catalan_aux hp hq hr _ _ _ _ _ _ _ _ HEq <;> try assumption
  · rw [rot3_add] at heq hineq; rw [mul3_add] at hineq
    apply Polynomial.flt_catalan_aux _ _ _ _ _ _ _ _ _ _ _ HEq <;> try assumption
  · rw [← rot3_add] at heq hineq; rw [← mul3_add] at hineq
    apply Polynomial.flt_catalan_aux _ _ _ _ _ _ _ _ _ _ _ HEq <;> try assumption

/- FLT is special case of nonsolvability of Fermat-Catalan equation.
Take p = q = r = n and u = v = 1, w = -1.
-/
theorem Polynomial.flt {n : ℕ} (hn : 3 ≤ n) (chn : ¬ringChar k ∣ n) {a b c : k[X]} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  by
  have hn' : 0 < n := by linarith
  rw [← sub_eq_zero, ← one_mul (a ^ n), ← one_mul (b ^ n), ← one_mul (c ^ n), sub_eq_add_neg, ←
    neg_mul] at heq
  have h : ↑(1 : k[X]ˣ) = (1 : k[X]) := rfl
  have hh : ↑(-1 : k[X]ˣ) = (-1 : k[X]) := rfl
  simp_rw [← hh, ← h] at heq
  apply Polynomial.flt_catalan hn' hn' hn' _ chn chn chn ha hb hc hab HEq
  have eq_lhs : n * n + n * n + n * n = 3 * n * n := by ring_nf
  rw [eq_lhs]; rw [mul_assoc, mul_assoc]
  apply Nat.mul_le_mul_right (n * n); exact hn

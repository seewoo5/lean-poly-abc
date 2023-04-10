import algebra.char_p.basic
import algebra.euclidean_domain.defs
import ring_theory.power_series.basic
import data.polynomial.expand
import logic.lemmas

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

/- Units of k[X] are nonzero. -/
private lemma unit_ne_zero {u : k[X]ˣ} : (↑u : k[X]) ≠ 0 :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw [←er, ne.def, C_eq_zero, ←ne.def],
  rw is_unit_iff_ne_zero at hr,
  exact hr,
end

/- Units of k[X] have degree 0. -/
private lemma unit_nat_degree_zero {u : k[X]ˣ} : (↑u : k[X]).nat_degree = 0 :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw ←er, exact polynomial.nat_degree_C r,
end

/- For a unit u and a polynomial a, (ua)' = u * a' -/
private lemma derivative_unit_mul {u : k[X]ˣ} (a : k[X]) :
  (↑u * a).derivative = ↑u * a.derivative :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw ←er, simp only [derivative_mul, derivative_C, zero_mul, zero_add],
end

/- Multiplying units preserve coprimality -/
private lemma is_coprime.mul_units_left {a b : k[X]} {u v : k[X]ˣ}
  (h : is_coprime a b) : is_coprime (↑u * a) (↑v * b) :=
by rw [is_coprime_mul_unit_left_left u.is_unit, is_coprime_mul_unit_left_right v.is_unit]; exact h 

private lemma rot_coprime {p q r : ℕ}
  {a b c : k[X]} {u v w : k[X]ˣ} (heq: ↑u*a^p + ↑v*b^q + ↑w*c^r = 0)
  (hab : is_coprime a b) 
  (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : is_coprime b c :=
begin
  rw [add_eq_zero_iff_neg_eq, ←units.inv_mul_eq_iff_eq_mul, mul_neg, mul_add, 
      ←mul_assoc, ←mul_assoc, ←units.coe_mul, ←units.coe_mul] at heq,
  rw [←is_coprime.pow_left_iff hq, ←is_coprime.pow_right_iff hr, ←heq,
    is_coprime.neg_right_iff],
  refine is_coprime.add_mul_right_right _ ↑(w⁻¹ * v),
  rw is_coprime_mul_unit_left_right (w⁻¹ * u).is_unit,
  exact hab.symm.pow,
end

private lemma rot3_add 
  {α : Type*} [add_comm_monoid α] {a b c : α} : a + b + c = b + c + a :=
begin
  rw add_comm (b+c) a, exact add_assoc _ _ _,
end

private lemma mul3_add 
  {α : Type*} [comm_monoid α] {a b c : α} : a * b * c = b * c * a :=
begin
  rw mul_comm (b*c) a, exact mul_assoc _ _ _,
end

theorem polynomial.flt_catalan_deriv
  {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (hineq : q*r + r*p + p*q ≤ p*q*r)
  (chp : ¬(ring_char k ∣ p)) (chq : ¬(ring_char k ∣ q)) (chr : ¬(ring_char k ∣ r))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : is_coprime a b)
  {u v w : k[X]ˣ} (heq: ↑u*a^p + ↑v*b^q + ↑w*c^r = 0) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hbc : is_coprime b c,
  { apply rot_coprime heq hab; assumption },
  have hca : is_coprime c a,
  { apply rot_coprime (rot3_add.symm.trans heq) hbc; assumption },

  have hap : a^p ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^q ≠ 0 := pow_ne_zero _ hb,
  have hcp : c^r ≠ 0 := pow_ne_zero _ hc,

  have habp : is_coprime (↑u*a^p) (↑v*b^q) := hab.pow.mul_units_left,
  have hbcp : is_coprime (↑v*b^q) (↑w*c^r) := hbc.pow.mul_units_left,
  have hcap : is_coprime (↑w*c^r) (↑u*a^p) := hca.pow.mul_units_left,
  have habcp := hcap.symm.mul_left hbcp,

  cases (polynomial.abc 
    (mul_ne_zero unit_ne_zero hap)
    (mul_ne_zero unit_ne_zero hbp)
    (mul_ne_zero unit_ne_zero hcp)
    habp hbcp hcap heq) with ineq dr0, swap,
  { simp_rw [derivative_unit_mul, 
      units.mul_right_eq_zero] at dr0,
    rw [pow_derivative_eq_zero chp ha,
        pow_derivative_eq_zero chq hb,
        pow_derivative_eq_zero chr hc] at dr0,
    exact dr0, },
  
  rw nat.add_one_le_iff at ineq,
  exfalso, apply not_le_of_lt ineq, clear ineq,
  -- work on lhs
  rw [radical_mul habcp, radical_mul habp],
  simp_rw radical_unit_mul,
  rw [radical_pow a hp, radical_pow b hq, radical_pow c hr],
  rw [←radical_mul hab, ←radical_mul (hca.symm.mul_left hbc)],
  apply le_trans radical_nat_degree_le,
  rw nat_degree_mul (mul_ne_zero ha hb) hc,
  rw nat_degree_mul ha hb,
  -- work on rhs
  rw nat_degree_mul unit_ne_zero hap,
  rw nat_degree_mul unit_ne_zero hbp,
  rw nat_degree_mul unit_ne_zero hcp,
  simp_rw [polynomial.nat_degree_pow, unit_nat_degree_zero, zero_add],

  have hpqr : 0 < p*q*r := nat.mul_le_mul
    (nat.mul_le_mul hp hq) hr,
  apply le_of_mul_le_mul_left _ hpqr,
  apply le_trans _ (nat.mul_le_mul_right _ hineq),
  convert weighted_average_le_max3,
  ring_nf,
end

private lemma expcont {a : k[X]} 
  (ha : a ≠ 0) (hda : a.derivative = 0) (chn0 : ring_char k ≠ 0) :
  ∃ ca, ca ≠ 0 ∧ a = expand k (ring_char k) ca ∧ 
    a.nat_degree = ca.nat_degree * (ring_char k) :=
begin
  have heq := (expand_contract (ring_char k) hda chn0).symm,
  refine ⟨_, _, heq, _⟩,
  { intro h, rw h at heq, simp only [map_zero] at heq, solve_by_elim, },
  { convert nat_degree_expand _ _, },
end

private lemma expand_dvd {a b : k[X]} {n : ℕ} (hn : n ≠ 0) (h : a ∣ b) :
  expand k n a ∣ expand k n b :=
begin
  rcases h with ⟨t, eqn⟩,
  use expand k n t, rw [eqn, map_mul],
end

private lemma expand_unit (u : k[X]ˣ) {n : ℕ} (hn : n ≠ 0) :
  expand k n ↑u = ↑u :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨c, hc, eqc⟩,
  simp_rw [←eqc, polynomial.expand_C],
end

private lemma is_coprime_of_expand {a b : k[X]} {n : ℕ} (hn : n ≠ 0) :
  is_coprime (expand k n a) (expand k n b) → is_coprime a b :=
begin
  simp_rw [←euclidean_domain.gcd_is_unit_iff],
  rw ←not_imp_not, intro h,
  cases (euclidean_domain.gcd_dvd a b) with ha hb,
  have hh := euclidean_domain.dvd_gcd (expand_dvd hn ha) (expand_dvd hn hb),
  intro h', apply h, have tt := is_unit_of_dvd_unit hh h',
  rw [polynomial.is_unit_iff] at tt ⊢,
  rcases tt with ⟨zz, yy⟩, rw [eq_comm, expand_eq_C (zero_lt_iff.mpr hn), eq_comm] at yy,
  refine ⟨zz, yy⟩, 
end

theorem polynomial.flt_catalan_aux
  {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (hineq : q*r + r*p + p*q ≤ p*q*r)
  (chp : ¬(ring_char k ∣ p)) (chq : ¬(ring_char k ∣ q)) (chr : ¬(ring_char k ∣ r))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : is_coprime a b)
  {u v w : k[X]ˣ} (heq: ↑u*a^p + ↑v*b^q + ↑w*c^r = 0) : 
  a.nat_degree = 0 :=
begin
  have hbc : is_coprime b c,
  { apply rot_coprime heq hab; assumption },
  have hca : is_coprime c a,
  { apply rot_coprime (rot3_add.symm.trans heq) hbc; assumption },

  cases (eq_or_ne (ring_char k) 0) with ch0 chn0,
  /- Characteristic zero -/
  { have hderiv : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0),
    { apply polynomial.flt_catalan_deriv hp hq hr; assumption, },
    rcases hderiv with ⟨da, -, -⟩,
    haveI ii : char_zero k,
    apply char_zero_of_inj_zero, intro n, rw ring_char.spec,
    rw ch0, exact zero_dvd_iff.mp,
    have tt := eq_C_of_derivative_eq_zero da,
    rw tt, exact nat_degree_C _, },

  /- Characteristic ch ≠ 0, where we use infinite descent.
  We use proof by contradiction (`by_contra`) combined with strong induction
  (`nat.case_strong_induction_on`) to formalize the proof.
  -/
  set d := a.nat_degree with eq_d, clear_value d, by_contra hd,
  revert a b c eq_d hd,
  induction d using nat.case_strong_induction_on with d ih_d,
  { intros, apply hd, refl },
  intros a b c eq_d hd ha hb hc hab heq hbc hca,
  have hderiv : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0),
  { apply polynomial.flt_catalan_deriv hp hq hr; assumption, },
  rcases hderiv with ⟨ad, bd, cd⟩,
  rcases expcont ha ad chn0 with ⟨ca, ca_nz, eq_a, eq_deg_a⟩,
  rcases expcont hb bd chn0 with ⟨cb, cb_nz, eq_b, eq_deg_b⟩,
  rcases expcont hc cd chn0 with ⟨cc, cc_nz, eq_c, eq_deg_c⟩,
  set ch := ring_char k with eq_ch,
  apply @ih_d ca.nat_degree _ ca cb cc rfl; clear ih_d; try {assumption},
  { intro h, rw [h, zero_mul] at eq_deg_a, apply hd, rw eq_d, exact eq_deg_a, },
  { apply is_coprime_of_expand chn0, rw [←eq_a, ←eq_b], exact hab },
  { rw [eq_a, eq_b, eq_c, 
      ←expand_unit u chn0, ←expand_unit v chn0, ←expand_unit w chn0] at heq,
    simp_rw [←map_pow, ←map_mul, ←map_add] at heq,
    rw (polynomial.expand_eq_zero (zero_lt_iff.mpr chn0)) at heq,
    exact heq, },
  { apply is_coprime_of_expand chn0, rw [←eq_b, ←eq_c], exact hbc },
  { apply is_coprime_of_expand chn0, rw [←eq_c, ←eq_a], exact hca },
  rw [←nat.lt_succ_iff, eq_d, eq_deg_a],
  rw [eq_d, eq_deg_a] at hd, have tt := (mul_ne_zero_iff.mp hd).1,
  conv_lhs {rw ←mul_one ca.nat_degree},
  apply nat.mul_lt_mul_of_pos_left,
  { have hch : ch ≠ 1, rw eq_ch, exact char_p.ring_char_ne_one,
    clear_value ch, cases ch, tauto, cases ch, tauto, dec_trivial, },
  exact zero_lt_iff.mpr tt,
end

theorem polynomial.flt_catalan
  {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (hineq : q*r + r*p + p*q ≤ p*q*r)
  (chp : ¬(ring_char k ∣ p)) (chq : ¬(ring_char k ∣ q)) (chr : ¬(ring_char k ∣ r))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : is_coprime a b)
  {u v w : k[X]ˣ} (heq: ↑u*a^p + ↑v*b^q + ↑w*c^r = 0) : 
  a.nat_degree = 0 ∧ b.nat_degree = 0 ∧ c.nat_degree = 0 :=
begin
  /- WLOG argument: essentially three times flt_catalan_aux -/
  have hbc : is_coprime b c,
  { apply rot_coprime heq hab; assumption },
  have hca : is_coprime c a,
  { apply rot_coprime (rot3_add.symm.trans heq) hbc; assumption },
  refine ⟨_, _, _⟩,
  { apply polynomial.flt_catalan_aux hp hq hr
      _ _ _ _ _ _ _ _ heq; try {assumption}, },
  { rw rot3_add at heq hineq, rw mul3_add at hineq,
    apply polynomial.flt_catalan_aux _ _ _
      _ _ _ _ _ _ _ _ heq; try {assumption}, },
  { rw ←rot3_add at heq hineq, rw ←mul3_add at hineq,
    apply polynomial.flt_catalan_aux _ _ _
      _ _ _ _ _ _ _ _ heq; try {assumption}, },
end 

/- FLT is special case of nonsolvability of Fermat-Catalan equation.
Take p = q = r = n and u = v = 1, w = -1.
-/
theorem polynomial.flt
  {n : ℕ} (hn : 3 ≤ n) (chn : ¬(ring_char k ∣ n))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (heq: a^n + b^n = c^n) : 
  a.nat_degree = 0 ∧ b.nat_degree = 0 ∧ c.nat_degree = 0 :=
begin
  have hn' : 0 < n := by linarith,
  rw [←sub_eq_zero, ←one_mul (a^n), ←one_mul (b^n), ←one_mul (c^n),
    sub_eq_add_neg, ←neg_mul] at heq,
  have h : ↑(1: k[X]ˣ) = (1: k[X]) := rfl,
  have hh : ↑(-1: k[X]ˣ) = (-1: k[X]) := rfl,
  simp_rw [←hh, ←h] at heq,
  apply polynomial.flt_catalan hn' hn' hn' _
    chn chn chn ha hb hc hab heq,
  have eq_lhs : n*n + n*n + n*n = 3*n*n := by ring_nf,
  rw eq_lhs, rw [mul_assoc, mul_assoc],
  apply nat.mul_le_mul_right (n*n), exact hn,
end

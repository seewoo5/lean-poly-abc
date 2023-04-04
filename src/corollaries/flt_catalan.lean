import algebra.char_p.basic
import algebra.euclidean_domain.defs
import ring_theory.power_series.basic
import logic.lemmas

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

private lemma unit_ne_zero {u : k[X]ˣ} : (↑u : k[X]) ≠ 0 :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw [←er, ne.def, C_eq_zero, ←ne.def],
  rw is_unit_iff_ne_zero at hr,
  exact hr,
end

private lemma unit_nat_degree_zero {u : k[X]ˣ} : (↑u : k[X]).nat_degree = 0 :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw ←er, exact polynomial.nat_degree_C r,
end

private lemma derivative_unit_mul {u : k[X]ˣ} (a : k[X]) :
  (↑u * a).derivative = ↑u * a.derivative :=
begin
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨r, hr, er⟩,
  rw ←er, simp only [derivative_mul, derivative_C, zero_mul, zero_add],
end

private lemma is_coprime.mul_units_left {a b : k[X]} {u v : k[X]ˣ}
  (h : is_coprime a b) : is_coprime (↑u * a) (↑v * b) :=
by rw [is_coprime_mul_unit_left_left u.is_unit, is_coprime_mul_unit_left_right v.is_unit]; exact h 

theorem polynomial.flt_catalan'
  {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (hineq : q*r + r*p + p*q ≤ p*q*r)
  (chp : ¬(ring_char k ∣ p)) (chq : ¬(ring_char k ∣ q)) (chr : ¬(ring_char k ∣ r))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : is_coprime a b)
  {u v w : k[X]ˣ} (heq: ↑u*a^p + ↑v*b^q = ↑w*c^r) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hbc : is_coprime b c,
  { rw [←units.inv_mul_eq_iff_eq_mul, mul_add, 
      ←mul_assoc, ←mul_assoc, ←units.coe_mul, ←units.coe_mul] at heq,
    rw [←is_coprime.pow_left_iff hq, ←is_coprime.pow_right_iff hr, ←heq],
    refine is_coprime.add_mul_right_right _ ↑(w⁻¹ * v),
    rw is_coprime_mul_unit_left_right (w⁻¹ * u).is_unit,
    exact hab.symm.pow },
  have hca : is_coprime c a,
  { rw [←units.inv_mul_eq_iff_eq_mul, mul_add, 
      ←mul_assoc, ←mul_assoc, ←units.coe_mul, ←units.coe_mul] at heq,
    rw [←is_coprime.pow_left_iff hr, ←is_coprime.pow_right_iff hp, ←heq],
    refine is_coprime.mul_add_right_left _ ↑(w⁻¹ * u),
    rw is_coprime_mul_unit_left_left (w⁻¹ * v).is_unit,
    exact hab.symm.pow, },

  have hap : a^p ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^q ≠ 0 := pow_ne_zero _ hb,
  have hcp : -c^r ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hc),

  rw [←add_neg_eq_zero, ←mul_neg] at heq,

  have habp : is_coprime (↑u*a^p) (↑v*b^q) := hab.pow.mul_units_left,
  have hbcp : is_coprime (↑v*b^q) (↑w*-c^r) := hbc.pow.neg_right.mul_units_left,
  have hcap : is_coprime (↑w*-c^r) (↑u*a^p) := hca.pow.neg_left.mul_units_left,
  have habcp := hcap.symm.mul_left hbcp,

  cases (polynomial.abc 
    (mul_ne_zero unit_ne_zero hap)
    (mul_ne_zero unit_ne_zero hbp)
    (mul_ne_zero unit_ne_zero hcp)
    habp hbcp hcap heq) with ineq dr0, swap,
  { simp_rw [derivative_unit_mul, 
      units.mul_right_eq_zero,
      derivative_neg, neg_eq_zero] at dr0,
    rw [pow_derivative_eq_zero chp ha,
        pow_derivative_eq_zero chq hb,
        pow_derivative_eq_zero chr hc] at dr0,
    exact dr0, },
  
  exfalso, apply not_le_of_lt ineq, clear ineq,
  -- work on lhs
  rw [radical_mul habcp, radical_mul habp],
  simp_rw radical_unit_mul,
  rw [radical_neg,
    radical_pow a hp, radical_pow b hq, radical_pow c hr],
  rw [←radical_mul hab, ←radical_mul (hca.symm.mul_left hbc)],
  apply le_trans radical_nat_degree_le,
  rw nat_degree_mul (mul_ne_zero ha hb) hc,
  rw nat_degree_mul ha hb,
  -- work on rhs
  rw nat_degree_mul unit_ne_zero hap,
  rw nat_degree_mul unit_ne_zero hbp,
  rw nat_degree_mul unit_ne_zero hcp,
  simp_rw [
    polynomial.nat_degree_neg,
    polynomial.nat_degree_pow,
    unit_nat_degree_zero, zero_add],

  have hpqr : 0 < p*q*r := nat.mul_le_mul
    (nat.mul_le_mul hp hq) hr,
  apply le_of_mul_le_mul_left _ hpqr,
  apply le_trans _ (nat.mul_le_mul_right _ hineq),
  convert weighted_average_le_max3,
  ring_nf,
end

theorem polynomial.flt_coprime
  {n : ℕ} (hn : 3 ≤ n) (chn : ¬(ring_char k ∣ n))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (heq: a^n + b^n = c^n) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hn' : 0 < n := by linarith,
  rw [←one_mul (a^n), ←one_mul (b^n), ←one_mul (c^n)] at heq,
  have h : ↑(1: k[X]ˣ) = (1: k[X]) := rfl,
  simp_rw ←h at heq,
  apply polynomial.flt_catalan' hn' hn' hn' _
    chn chn chn ha hb hc hab heq,
  have eq_lhs : n*n + n*n + n*n = 3*n*n := by ring_nf,
  rw eq_lhs, rw [mul_assoc, mul_assoc],
  apply nat.mul_le_mul_right (n*n), exact hn,
end

namespace euclidean_domain 

universe u
variables {R : Type u} [euclidean_domain R] {a b : R}

-- TODO: get rid of this once mathlib is updated
protected lemma mul_div_cancel' (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a :=
  by rw [←mul_div_assoc _ hab, mul_div_cancel_left _ hb]

lemma pow_n_dvd_pow_n_iff {a b : k[X]} {n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hn : 0 < n) :
  a^n ∣ b^n ↔ a ∣ b :=
begin
  rw dvd_iff_normalized_factors_le_normalized_factors ha hb,
  rw dvd_iff_normalized_factors_le_normalized_factors
    (pow_ne_zero _ ha) (pow_ne_zero _ hb),
  simp_rw [normalized_factors_pow, multiset.le_iff_count, multiset.count_nsmul],
  simp_rw mul_le_mul_left hn,
end

end euclidean_domain

theorem polynomial.flt
  [char_zero k] {n : ℕ} (hn : 3 ≤ n)
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (heq: a^n + b^n = c^n) : 
  ∃ (d: k[X]) (sa sb sc : k), a = ↑sa * d ∧ b = ↑sb * d ∧ c = ↑sc * d :=
begin
  have hd : euclidean_domain.gcd a b ≠ 0,
  { intro h, rw euclidean_domain.gcd_eq_zero_iff at h, exact ha h.1, },
  have eq_a := euclidean_domain.mul_div_cancel' hd
    (euclidean_domain.gcd_dvd_left a b),
  have eq_b := euclidean_domain.mul_div_cancel' hd
    (euclidean_domain.gcd_dvd_right a b),
  set d := euclidean_domain.gcd a b with def_d,
  rw [←eq_a, ←eq_b] at heq,
  simp_rw [mul_pow, ←mul_add] at heq,
  have dvd_dc := dvd_of_mul_right_eq _ heq,
  have hn' : 0 < n := by linarith,
  rw euclidean_domain.pow_n_dvd_pow_n_iff hd hc hn' at dvd_dc,
  have eq_c := euclidean_domain.mul_div_cancel' hd dvd_dc,
  rw [←eq_c, mul_pow, mul_right_inj' (pow_ne_zero _ hd)] at heq,
  have hab : is_coprime (a / d) (b / d),
  { have gcd_eq := euclidean_domain.gcd_eq_gcd_ab a b,
    rw [←def_d, ←eq_a, ←eq_b, mul_assoc, mul_assoc, ←mul_add] at gcd_eq,
    conv_lhs at gcd_eq {rw ←mul_one d},
    rw [mul_right_inj' hd, mul_comm (a / d), mul_comm (b / d)] at gcd_eq,
    existsi _, existsi _, exact gcd_eq.symm, },
  have flt := polynomial.flt_coprime hn
    (by rw [ring_char.eq_zero, zero_dvd_iff]; linarith) 
    (right_ne_zero_of_mul (eq_a.trans_ne ha))
    (right_ne_zero_of_mul (eq_b.trans_ne hb))
    (right_ne_zero_of_mul (eq_c.trans_ne hc))
    hab heq,
  rcases flt with ⟨hda, hdb, hdc⟩,
  rw [polynomial.eq_C_of_derivative_eq_zero hda, mul_comm, eq_comm] at eq_a,
  rw [polynomial.eq_C_of_derivative_eq_zero hdb, mul_comm, eq_comm] at eq_b,
  rw [polynomial.eq_C_of_derivative_eq_zero hdc, mul_comm, eq_comm] at eq_c,
  refine ⟨_, _, _, _, eq_a, eq_b, eq_c⟩,
end

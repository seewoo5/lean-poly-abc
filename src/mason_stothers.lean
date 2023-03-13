import algebra.char_p.basic

import wronskian
import div_radical
import max3

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]


@[simp]
lemma dvd_derivative_iff {a : k[X]} : 
  a ∣ a.derivative ↔ a.derivative = 0 :=
begin
  split,
  intro h,
  by_cases a_nz : a = 0,
  { rw a_nz, simp only [derivative_zero], },
  by_contra deriv_nz,
  have deriv_lt := degree_derivative_lt a_nz,
  have le_deriv := polynomial.degree_le_of_dvd h deriv_nz,
  have lt_self := le_deriv.trans_lt deriv_lt,
  simp only [lt_self_iff_false] at lt_self, exact lt_self,

  intro h, rw h, simp,
end

lemma is_coprime.wronskian_eq_zero_iff
  {a b : k[X]} (hc: is_coprime a b) : 
  wronskian a b = 0 ↔ (a.derivative = 0 ∧ b.derivative = 0) :=
begin
  split,

  intro hw,
  rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw,
  split,
  { rw ←dvd_derivative_iff,
    apply hc.dvd_of_dvd_mul_right,
    rw ←hw, exact dvd_mul_right _ _, },
  { rw ←dvd_derivative_iff,
    apply hc.symm.dvd_of_dvd_mul_left,
    rw hw, exact dvd_mul_left _ _, },

  intro hdab,
  cases hdab with hda hdb,
  rw wronskian,
  rw [hda, hdb], simp only [mul_zero, zero_mul, sub_self],
end

/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0 and deg(a) ≥ deg(rad(abc)), we have a' = b' = c' = 0.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf, which is essentially based on Noah Snyder's proof ("An Alternative Proof of Mason's Theorem"), but slightly different.

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. (a / rad(a)) | W, and same for b and c. `poly_mod_rad_div_diff`
3. a / rad(a), b / rad(b), c / rad(c) are all coprime, so their product abc / rad(abc) also divides W. `poly_coprime_div_mul_div`
4. Using the assumption on degrees, deduce that deg (abc / rad(abc)) > deg W.
5. By `polynomial.degree_le_of_dvd`, W = 0.
6. Since W(a, b) = ab' - a'b = 0 and a and b are coprime, a' = 0. Similarly we have b' = c' = 0. `coprime_wronskian_eq_zero_const`
-/

protected lemma is_coprime.div_radical {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : is_coprime a b) : is_coprime a.div_radical b.div_radical :=
begin
  rw ←polynomial.mul_radical_div_radical ha at h,
  rw ←polynomial.mul_radical_div_radical hb at h,
  exact h.of_mul_left_right.of_mul_right_right,
end

theorem polynomial.abc {a b c : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a)
  (hsum: a + b + c = 0) (hdeg : (a * b * c).radical.degree ≤ a.degree) : 
    (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  -- Utility assertions
  have hab_c := hca.symm.mul_left hbc,
  have hab_nz : a * b ≠ 0 := mul_ne_zero ha hb,
  have habc_nz : a * b * c ≠ 0 := mul_ne_zero hab_nz hc,

  have ndeg_eq_a := polynomial.degree_eq_nat_degree ha,
  have ndeg_eq_b := polynomial.degree_eq_nat_degree hb,
  have ndeg_eq_c := polynomial.degree_eq_nat_degree hc,

  have abc_dr_nz := polynomial.div_radical_ne_zero habc_nz,
  have ndeg_eq_abc_dr := polynomial.degree_eq_nat_degree abc_dr_nz,

  -- conversion to .nat_degree
  have hndeg : (a * b * c).radical.nat_degree ≤ a.nat_degree := begin
    have h := (a * b * c).radical_ne_zero,
    have heq := polynomial.degree_eq_nat_degree h,
    rw [heq, ndeg_eq_a] at hdeg,
    simp only [with_bot.coe_le_coe] at hdeg, exact hdeg,
  end,

  -- Step 1 & 2
  have wbc := wronskian_eq_of_sum_zero hsum,
  have ara_dvd_w := a.div_radical_dvd_wronskian_left b,
  have brb_dvd_w := a.div_radical_dvd_wronskian_right b,
  have crc_dvd_w := b.div_radical_dvd_wronskian_right c,
  set w := wronskian a b with wab,
  rw ←wbc at crc_dvd_w,
  
  -- Step 3
  have abc_dvd_w : (a*b*c).div_radical ∣ w := begin
    have abc_eq : (a*b*c).div_radical = 
      a.div_radical * b.div_radical * c.div_radical := begin
      rw ←polynomial.div_radical_mul ha hb hab,
      rw ←polynomial.div_radical_mul hab_nz hc _,
      exact hca.symm.mul_left hbc,
    end,
    rw abc_eq,
    have hab_dr := hab.div_radical ha hb,
    have hbc_dr := hbc.div_radical hb hc,
    have hca_dr := hca.div_radical hc ha,
    have h_coprime := hca_dr.symm.mul_left hbc_dr,
    apply h_coprime.mul_dvd _ crc_dvd_w,
    exact hab_dr.mul_dvd ara_dvd_w brb_dvd_w,
  end,

  -- Step 4
  -- We use polynomial.nat_degree : ℕ in place of polynomial.degree : with_bot ℕ for 
  -- ease of computation and avoiding lack of lemmas
  have deg_comp_1 : a.nat_degree + b.nat_degree + c.nat_degree ≤ 
    a.nat_degree + (a*b*c).div_radical.nat_degree := by
    calc a.nat_degree + b.nat_degree + c.nat_degree = (a*b*c).nat_degree : 
      by rw [nat_degree_mul hab_nz hc, nat_degree_mul ha hb]
    ... = ((a*b*c).radical * (a*b*c).div_radical).nat_degree : 
      by rw polynomial.mul_radical_div_radical habc_nz
    ... = (a*b*c).radical.nat_degree + (a*b*c).div_radical.nat_degree : 
      nat_degree_mul (a*b*c).radical_ne_zero abc_dr_nz
    ... ≤ a.nat_degree + (a*b*c).div_radical.nat_degree : add_le_add_right hndeg _,
  have deg_comp_2 : b.nat_degree + c.nat_degree ≤ (a*b*c).div_radical.nat_degree := begin
    apply @nat.le_of_add_le_add_left a.nat_degree,
    rw ←add_assoc, exact deg_comp_1,
  end,
  -- revert to .degree - this is false in .nat_degree
  have deg_comp_3 : w.degree < (a*b*c).div_radical.degree :=
  begin
    have ineq := wronskian.degree_lt_add hb hc,
    rw ←wbc at ineq,
    apply ineq.trans_le,
    rw [ndeg_eq_b, ndeg_eq_c, ndeg_eq_abc_dr],
    rw [←with_bot.coe_add, with_bot.coe_le_coe],
    exact deg_comp_2,
  end,
  have w_z : w = 0 := begin
    by_contra w_nz,
    have t := degree_le_of_dvd abc_dvd_w w_nz,
    have wf : w.degree < w.degree := begin
      calc w.degree < (a*b*c).div_radical.degree : deg_comp_3
      ... ≤ w.degree : t
    end,
    simp only [lt_self_iff_false] at wf,
    exact wf,
  end,
  cases (hab.wronskian_eq_zero_iff.mp w_z) with daz dbz,
  refine ⟨daz, dbz, _⟩,
  rw wbc at w_z,
  cases (hbc.wronskian_eq_zero_iff.mp w_z) with _ dcz,
  exact dcz,
end

theorem polynomial.abc_contra {a b c : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a)
  (hsum: a + b + c = 0)
  (hnderiv : ¬(a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0)) : 
  a.degree < (a * b * c).radical.degree :=
begin
  cases lt_or_le a.degree (a * b * c).radical.degree with h h,
  { exact h, },
  { exfalso, apply hnderiv, apply polynomial.abc; assumption },
end

theorem polynomial.abc_contra_nat {a b c : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a)
  (hsum: a + b + c = 0)
  (hnderiv : ¬(a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0)) : 
  a.nat_degree < (a * b * c).radical.nat_degree :=
begin
  rw ←with_bot.coe_lt_coe,
  rw [←polynomial.degree_eq_nat_degree ha,
      ←polynomial.degree_eq_nat_degree _],
  apply polynomial.abc_contra; assumption,
  exact (a * b * c).radical_ne_zero,
end

private lemma rot3_add {a b c : k[X]} : a + b + c = b + c + a := by ring_nf
private lemma rot3_mul {a b c : k[X]} : a * b * c = b * c * a := by ring_nf

/- Alternative version with maximum of degrees.
Corollary 2.1.5 of Franz's note.
Here we need an assumption that their derivatives are not all zero - otherwise the statement itself is false as stated.
-/
theorem polynomial.abc_max3 (chn : ring_char k = 0) 
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) 
  (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a) 
  (hsum : a + b + c = 0) 
  (hnderiv : ¬(a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0)) : 
  max3 a.nat_degree b.nat_degree c.nat_degree < (a*b*c).radical.nat_degree :=
begin
  have hadeg : a.nat_degree < (a*b*c).radical.nat_degree :=
    by apply polynomial.abc_contra_nat; assumption,
  have hbdeg : b.nat_degree < (a*b*c).radical.nat_degree :=
    by rw rot3_add at hsum; rw rot3_mul; 
       apply polynomial.abc_contra_nat; try {assumption}; tauto,
  have hcdeg : c.nat_degree < (a*b*c).radical.nat_degree :=
    by rw [rot3_add, rot3_add] at hsum; rw [rot3_mul, rot3_mul]; 
       apply polynomial.abc_contra_nat; try {assumption}; tauto,
  rw max3_lt_iff, refine ⟨hadeg, hbdeg, hcdeg⟩, 
end

/- FLT for polynomials
For coprime polynomials a, b, c satisfying a^n + b^n + c^n = 0, n ≥ 3 then a, b, c are all constant (i.e. all of their derivatives are zero).
(We assume that the characteristic of the field is zero. In fact, the theorem is true when the characteristic does not divide n.)

Proof)
1. Assume that at least one of a, b, and c has nonzero derivative.
2. For the corresponding polynomial (let's say, a), characteristic zero assumption implies that the derivative of its power (let's say, a^n) is also nonzero.
3. Apply ABC for polynomials `poly_abc_max_ver` with triple (a^n, b^n, c^n) to get an inequality max(deg a^n, deg b^n, deg c^n) < deg rad(a^n*b^n*c^n).
4. Use properties of degree `degree_pow`, `rad_pow`, and the assumption `3 ≤ n` to deduce a contradiction.

-> n * max (deg a, deg b, deg c) = max (deg a^n, deg b^n, deg c^n)
< deg (rad (a^n * b^n * c^n)) 
≤ deg (rad (a * b * c))
≤ deg (abc)
≤ deg a + deg b + deg c
≤ 3 * max (deg a, deg b, deg c)
≤ n * max (deg a, deg b, deg c)
-/

-- (a^n)' = 0 → a' = 0 when char(k) ∤ n.
lemma char_ndvd_pow_deriv {a : k[X]} (n : ℕ) (ha : a ≠ 0) 
  (hn : n > 0) (chn : ¬(ring_char k ∣ n))
  (apd : (a^n).derivative = 0) : a.derivative = 0 :=
begin
  rw derivative_pow at apd,
  have pnz : a^(n-1) ≠ 0 := pow_ne_zero (n-1) ha,
  have cn_neq_zero : (polynomial.C (↑n : k)) ≠ 0 :=
  begin
    simp only [polynomial.C_eq_zero, ne.def],
    intro cn_eq_zero,
    have cdvd := ring_char.dvd cn_eq_zero,
    tauto,
  end,
  simp at apd,
  tauto,
end

theorem polynomial.flt (chz : ring_char k = 0) 
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a)
  {n : ℕ} (hn: 3 ≤ n) (hsum: a^n + b^n + c^n = 0)  : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hap : a^n ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^n ≠ 0 := pow_ne_zero _ hb,
  have hcp : c^n ≠ 0 := pow_ne_zero _ hc,

  have habp : is_coprime (a^n) (b^n) := is_coprime.pow hab,
  have hbcp : is_coprime (b^n) (c^n) := is_coprime.pow hbc,
  have hcap : is_coprime (c^n) (a^n) := is_coprime.pow hca,

  have np : 1 ≤ n := le_trans (by dec_trivial) hn,

  by_contra ngoal,

  have hdeg_2 : 
    n * max3 a.nat_degree b.nat_degree c.nat_degree < 
    n * max3 a.nat_degree b.nat_degree c.nat_degree :=
  begin
    calc n * max3 a.nat_degree b.nat_degree c.nat_degree = 
      max3 (n*a.nat_degree) (n*b.nat_degree) (n*c.nat_degree) : 
      by rw max3_mul_left _ _ _ _
    ... = max3 (a^n).nat_degree (b^n).nat_degree (c^n).nat_degree : 
      by simp only [polynomial.nat_degree_pow]
    ... < (a^n * b^n * c^n).radical.nat_degree : begin
      apply polynomial.abc_max3; try {assumption},
      -- derivatives of a^n, b^n and c^n are not zero: uses char k = 0
      intro h, rcases h with ⟨ia, ib, ic⟩,
      apply ngoal,
      have hndvd : ¬(ring_char k ∣ n) := by rw chz; simp; linarith,
      refine ⟨_, _, _⟩; apply char_ndvd_pow_deriv n; assumption,
    end
    ... = ((a*b*c)^n).radical.nat_degree : by rw [mul_pow, mul_pow]
    ... = (a*b*c).radical.nat_degree : by rw (a*b*c).radical_pow np
    ... ≤ (a*b*c).nat_degree : 
      polynomial.radical_nat_degree_le (by repeat {apply mul_ne_zero}; assumption)
    ... = a.nat_degree + b.nat_degree + c.nat_degree : begin
      rw polynomial.nat_degree_mul _ hc,
      rw polynomial.nat_degree_mul ha hb,
      exact mul_ne_zero ha hb,
    end
    ... ≤ 3 * max3 a.nat_degree b.nat_degree c.nat_degree : 
      add3_le_three_mul_max3 _ _ _
    ... ≤ n * max3 a.nat_degree b.nat_degree c.nat_degree :
      nat.mul_le_mul_right _ hn
  end,
  exfalso, exact (eq.not_lt (eq.refl _)) hdeg_2,
end

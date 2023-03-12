/- Proof of polynomial ABC (Mason-Stothers theorem) and polynomial FLT as a corollary.
-/

import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.char_p.basic
import algebra.divisibility.basic
import algebra.divisibility.units
import algebra.group.basic
import algebra.group_power.basic
import algebra.order.smul
import data.finset.basic
import data.multiset.basic
import data.polynomial.basic
import data.polynomial.derivative
import order.with_bot
import ring_theory.euclidean_domain
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain

import .radical
import .wronskian

noncomputable theory

open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]


/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0 and deg(a) ≥ deg(rad(abc)), we have a' = b' = c' = 0.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf, which is essentially based on Noah Snyder's proof ("An Alternative Proof of Mason's Theorem"), but slightly deriverent.

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. (a / rad(a)) | W, and same for b and c. `div_rad_dvd_wronskian_left` and `div_rad_dvd_wronskian_right`
3. a / rad(a), b / rad(b), c / rad(c) are all coprime, so their product abc / rad(abc) also divides W. `coprime_div_mul_div`
4. Using the assumption on degrees, deduce that deg (abc / rad(abc)) > deg W.
5. By `polynomial.degree_le_of_dvd`, W = 0.
6. Since W(a, b) = ab' - a'b = 0 and a and b are coprime, a' = 0. Similarly we have b' = c' = 0. `coprime_wronskian_eq_zero_const`
-/


-- Lemma to ignore degree = ⊥ case when a polynomial is nonzero.
lemma poly_ne_zero_deg_nbot (a : k[X]) (ha : a ≠ 0) : a.degree ≠ ⊥ :=
begin
  by intro h; rw polynomial.degree_eq_bot at h; exact ha h,
end

-- Lemma for Step 1. Follows from basic properties of Wronskian (proved before).
lemma wronskian_eq_of_sum_zero {a b c : k[X]}
  (h : a + b + c = 0) : wronskian a b = wronskian b c :=
begin
  rw ← neg_eq_iff_add_eq_zero at h,
  rw ← h,
  rw wronskian_neg_right,
  rw wronskian_add_right,
  rw wronskian_self,
  rw add_zero,
  rw ← wronskian_anticomm,
end

-- Lemmata for Step 2. Mostly follows from `div_rad_dvd_self` and `div_rad_dvd_deriv_always`.
theorem div_rad_dvd_wronskian_left (a b : k[X]) : div_rad a ∣ wronskian a b :=
begin
  by_cases a_nz : a = 0,
  { subst a_nz, rw wronskian_zero_left b, exact dvd_zero _, },
  rw wronskian,
  apply dvd_sub,
  { apply dvd_mul_of_dvd_left, 
    apply (div_rad_dvd_self _ a_nz), },
  { apply dvd_mul_of_dvd_left,
    apply (div_rad_dvd_deriv_always a_nz), },
end

theorem div_rad_dvd_wronskian_right (a b : k[X]) : div_rad b ∣ wronskian a b :=
begin
  rw [wronskian_anticomm, dvd_neg],
  exact div_rad_dvd_wronskian_left _ _,
end

-- Lemma for Step 6. `coprime_wronskian_eq_zero_const`
lemma dvd_deriv_iff_deriv_eq_zero
  {a : k[X]} (a_dvd_a_deriv : a ∣ a.derivative) : a.derivative = 0 :=
begin
  by_cases a_nz : a = 0,
  { rw a_nz, simp only [derivative_zero], },
  by_contra deriv_nz,
  have deriv_lt := degree_derivative_lt a_nz,
  have le_deriv := polynomial.degree_le_of_dvd a_dvd_a_deriv deriv_nz,
  have lt_self := le_deriv.trans_lt deriv_lt,
  simp only [lt_self_iff_false] at lt_self, exact lt_self,
end

lemma coprime_wronskian_eq_zero_const 
  {a b : k[X]} (hw: wronskian a b = 0) 
  (hc: is_coprime a b) : (a.derivative = 0 ∧ b.derivative = 0) :=
begin
  rw [wronskian, sub_eq_iff_eq_add, zero_add] at hw,
  split,
  { apply dvd_deriv_iff_deriv_eq_zero,
    apply hc.dvd_of_dvd_mul_right,
    rw ←hw, exact dvd_mul_right _ _, },
  { apply dvd_deriv_iff_deriv_eq_zero,
    apply hc.symm.dvd_of_dvd_mul_left,
    rw hw, exact dvd_mul_left _ _, },
end

-- Proof of the main theorem (polynomial ABC).
theorem poly_abc (a b c : k[X]) (hsum: a + b + c = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a) (hdeg : (rad (a * b * c)).degree ≤ a.degree) : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  -- 1, 2.
  have wbc := wronskian_eq_of_sum_zero hsum,
  have ara_dvd_w := div_rad_dvd_wronskian_left a b,
  have brb_dvd_w := div_rad_dvd_wronskian_right a b,
  have crc_dvd_w := div_rad_dvd_wronskian_right b c,
  set w := wronskian a b with wab,
  rw ←wbc at crc_dvd_w,

  -- 3.
  have hab_c := hca.symm.mul_left hbc,
  have hab_nz : a * b ≠ 0 := 
    by simp only [ne.def, mul_eq_zero]; tauto,
  have habc_nz : a * b * c ≠ 0 := 
    by simp only [ne.def, mul_eq_zero]; tauto,
  
  have abc_dvd_w : div_rad (a*b*c) ∣ w := begin
    have abc_eq : div_rad (a*b*c) = 
      (div_rad a)*(div_rad b)*(div_rad c),
      {
        calc div_rad (a*b*c) = div_rad (a*b) * (div_rad c) : div_rad_coprime_mul hab_nz hc hab_c
        ... = (div_rad a) * (div_rad b) * (div_rad c) : by rw div_rad_coprime_mul ha hb hab,
      },
    rw abc_eq,
    apply is_coprime.mul_dvd _ _ crc_dvd_w,
    {
      rw ← div_rad_coprime_mul ha hb hab,
      exact hab_c.div_rad hab_nz hc,
    },
    {
      have h_ara_brb_c := hab.div_rad ha hb,
      exact h_ara_brb_c.mul_dvd ara_dvd_w brb_dvd_w,
    },
  end,

  -- 4.
  have deg_comp_1 : a.degree + b.degree + c.degree ≤ a.degree + (div_rad (a*b*c)).degree :=
  begin
    calc a.degree + b.degree + c.degree = (a*b*c).degree : by simp only [degree_mul]
    ... = (div_rad (a*b*c) * rad (a*b*c)).degree : by rw (mul_div_rad_rad habc_nz)
    ... = (div_rad (a*b*c)).degree + (rad (a*b*c)).degree : by simp only [degree_mul]
    ... ≤ (div_rad (a*b*c)).degree + a.degree : add_le_add_left hdeg _
    ... = a.degree + (div_rad (a*b*c)).degree : add_comm _ _
  end,
  have deg_comp_2 : b.degree + c.degree ≤ (div_rad (a*b*c)).degree := begin
    have a_deg_nbot := poly_ne_zero_deg_nbot a ha,
    rw ←with_bot.add_le_add_iff_left a_deg_nbot,
    rw ←add_assoc _ _ _, exact deg_comp_1,
  end,
  have deg_comp_3 : w.degree < (div_rad (a*b*c)).degree :=
  begin
    have ineq := wronskian.deg_lt_add_deg_deg hb hc,
    rw ←wbc at ineq,
    exact ineq.trans_le deg_comp_2, 
  end,

  -- 5.
  have w_z : w = 0 :=
  begin
    by_contra w_nz,
    have t := degree_le_of_dvd abc_dvd_w w_nz,
    have wf : w.degree < w.degree := begin
      calc w.degree < (div_rad (a*b*c)).degree : deg_comp_3
      ... ≤ w.degree : t
    end,
    simp only [lt_self_iff_false] at wf,
    exact wf,
  end,

  -- 6.
  cases (coprime_wronskian_eq_zero_const w_z hab) with daz dbz,
  rw wbc at w_z,
  cases (coprime_wronskian_eq_zero_const w_z hbc) with _ dcz,
  refine ⟨daz, dbz, dcz⟩, 
end


/- Alternative version with maximum of degrees.
Corollary 2.1.5 of Franz's note.
Here we need an assumption that their derivatives are not all zero - otherwise the statement itself is false as stated.
-/
theorem poly_abc_max_ver (a b c : k[X]) (chn : ring_char k = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hsum : a + b + c = 0) (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a) (hnderiv : ¬(a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0)): max (max a.degree b.degree) c.degree < (rad (a*b*c)).degree :=
begin
  have hadeg : a.degree < (rad (a*b*c)).degree :=
  begin
    have abc_a := poly_abc a b c hsum ha hb hc hab hbc hca,
    cases lt_or_le a.degree ((rad (a * b * c)).degree) with h h,
    exact h, exfalso, apply hnderiv, apply abc_a, exact h,
  end,
  have hbdeg : b.degree < (rad (a*b*c)).degree :=
  begin
    have hsum' : b + c + a = 0,
    {
      calc b + c + a = a + b + c : by ring
      ... = 0 : hsum
    },
    have abc_b := poly_abc b c a hsum' hb hc ha hbc hca hab,
    have hnderiv' : ¬(b.derivative = 0 ∧ c.derivative = 0 ∧ a.derivative = 0) := by tauto,
    have t : b*c*a = a*b*c := by ring,
    cases lt_or_le b.degree ((rad (a*b*c)).degree) with h h,
    exact h,
    exfalso, apply hnderiv', apply abc_b, rw t, exact h,
  end,
  have hcdeg : c.degree < (rad (a*b*c)).degree := 
  begin
    have hsum' : c + a + b = 0,
    {
      calc c + a + b = a + b + c : by ring
      ... = 0 : hsum
    },
    have abc_c := poly_abc c a b hsum' hc ha hb hca hab hbc,
    have hnderiv' : ¬(c.derivative = 0 ∧ a.derivative = 0 ∧ b.derivative = 0) := by tauto,
    have t : c*a*b = a*b*c := by ring,
    cases lt_or_le c.degree ((rad (a*b*c)).degree) with h h,
    exact h,
    exfalso, apply hnderiv', apply abc_c, rw t, exact h,
  end,
  exact max_lt (max_lt hadeg hbdeg) hcdeg,
end


/- FLT for polynomials

For coprime polynomials a, b, c satisfying a^n + b^n + c^n = 0, n ≥ 3 then a, b, c are all constant (i.e. all of their derivatives are zero).
(We assume that the characteristic of the field is zero. In fact, the theorem is true when the characteristic does not divide n.)

Proof)
1. Assume that at least one of a, b, and c has nonzero derivative.
2. For the corresponding polynomial (let's say, a), characteristic zero assumption implies that the derivative of its power (let's say, a^n) is also nonzero.
3. Apply ABC for polynomials `poly_abc_max_ver` with triple (a^n, b^n, c^n) to get an inequality max(deg a^n, deg b^n, deg c^n) < deg rad(a^n*b^n*c^n).
4. Use properties of degree `degree_pow`, `rad_pow`, and the assumption `3 ≤ n` to deduce a contradiction. Here we need some arithmetic with `nat.with_bot`.

-> n * max (deg a, deg b, deg c) = max (deg a^n, deg b^n, deg c^n)
< deg (rad (a^n * b^n * c^n)) 
≤ deg (rad (a * b * c))
≤ deg (abc)
≤ deg a + deg b + deg c
≤ 3 * max (deg a, deg b, deg c)
≤ n * max (deg a, deg b, deg c)
-/

-- (a^n)' = 0 → a' = 0 when char(k) ∤ n.
lemma char_ndvd_pow_deriv {a : k[X]} {n : ℕ} (ha : a ≠ 0) (hn : n > 0) (chn : ¬(ring_char k ∣ n)) : (a^n).derivative = 0 → a.derivative = 0 :=
begin
  intro apd,
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


/- Lemmata related to arithmetics and inequalities `with_bot ℕ`.
Need this since the type of `polynomial.degree` is not exactly `ℕ`, but `with_bot ℕ` since the degree of zero polynomial is defined as `⊥`.
-/
protected lemma nat.with_bot.add_le_add 
  {a b c d : with_bot ℕ}
  (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
begin
  by_cases hb : b = ⊥,
  { subst hb, simp at h1, subst h1, simp },
  by_cases hc : c = ⊥,
  { subst hc, simp only [with_bot.add_bot, bot_le], }, 
  calc a + c ≤ b + c : by rw with_bot.add_le_add_iff_right hc; exact h1
  ... ≤ b + d : by rw with_bot.add_le_add_iff_left hb; exact h2
end

protected lemma nat.with_bot.smul_le_smul 
  {n : ℕ} {a b : with_bot ℕ}
  (h : a ≤ b) : n • a ≤ n • b :=
begin
  induction n with n ih,
  simp, rw [succ_nsmul, succ_nsmul],
  apply nat.with_bot.add_le_add h ih,
end

protected lemma nat.with_bot.smul_max 
  {n : ℕ} {a b : with_bot ℕ} : n • max a b = max (n • a) (n • b) :=
begin
  apply eq.symm,
  rw max_eq_iff,
  rcases max_cases a b with ⟨eqn, ba⟩ | ⟨eqn, ab⟩,
  left, rw eqn, refine ⟨rfl, _⟩, exact nat.with_bot.smul_le_smul ba,
  right, rw eqn, refine ⟨rfl, _⟩, exact nat.with_bot.smul_le_smul (le_of_lt ab),
end


-- FLT for polynomials (when characteristic is zero).
theorem poly_flt_char_zero (a b c : k[X]) (n : ℕ) (chz : ring_char k = 0) (hn: 3 ≤ n) (hsum: a^n + b^n + c^n = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a) : (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hap : a^n ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^n ≠ 0 := pow_ne_zero _ hb,
  have hcp : c^n ≠ 0 := pow_ne_zero _ hc,

  have habp : is_coprime (a^n) (b^n) := is_coprime.pow hab,
  have hbcp : is_coprime (b^n) (c^n) := is_coprime.pow hbc,
  have hcap : is_coprime (c^n) (a^n) := is_coprime.pow hca,

  have np : n > 0 := by linarith,

  by_contra ngoal,

  have hdeg_2 : n • (max (max a.degree b.degree) c.degree) < n • (max (max a.degree b.degree) c.degree) :=
  begin
    calc n • (max (max a.degree b.degree) c.degree) = max (n • (max a.degree b.degree)) (n • c.degree) : by rw nat.with_bot.smul_max
    ... = max (max (n • a.degree) (n • b.degree)) (n • c.degree) : by rw nat.with_bot.smul_max
    ... = max (max (a^n).degree (b^n).degree) (c^n).degree : by simp only [polynomial.degree_pow]
    ... < (rad (a^n * b^n * c^n)).degree : _
    ... = (rad ((a*b*c)^n)).degree : by rw [mul_pow, mul_pow]
    ... = (rad (a*b*c)).degree : by rw rad_pow (a*b*c) np
    ... ≤ (a*b*c).degree : rad_deg_le_deg (by simp only [ne.def, mul_eq_zero]; tauto)
    ... = a.degree + b.degree + c.degree : by simp only [degree_mul]
    ... ≤ 3 • (max (max a.degree b.degree) c.degree) : _
    ... ≤ n • (max (max a.degree b.degree) c.degree) : _,
    { have hdeg_1 := poly_abc_max_ver (a^n) (b^n) (c^n) 
        chz hap hbp hcp hsum habp hbcp hcap,
      apply hdeg_1, intro h, apply ngoal,
      refine ⟨_, _, _⟩;
      { apply char_ndvd_pow_deriv _ np; try {assumption},
        rw chz, simp, linarith, tauto, }, },
    { set m := max (max a.degree b.degree) c.degree with def_m,
      have eq_3m : 3 • m = m + m + m := begin
        rw (show 3 = 2 + 1, by refl),
        rw [add_smul, two_smul, one_smul],
      end,
      rw eq_3m,
      apply nat.with_bot.add_le_add,
      apply nat.with_bot.add_le_add,
      { rw def_m, apply le_max_of_le_left _,
        exact le_max_left _ _ }, 
      { rw def_m, apply le_max_of_le_left _,
        exact le_max_right _ _ },
      { exact le_max_right _ _ }, },
    { set m := max (max a.degree b.degree) c.degree with def_m,
      cases le_or_lt 0 m with h h,
      exact nsmul_le_nsmul h hn,
      rw nat.with_bot.lt_zero_iff _ at h, rw h,
      rw (show 3 = 2 + 1, by refl),
      rw [add_smul, two_smul, one_smul], simp, },
  end,
  exfalso, exact (eq.not_lt (eq.refl _)) hdeg_2,
end

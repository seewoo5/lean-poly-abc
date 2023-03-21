import algebra.char_p.basic
import algebra.euclidean_domain.defs

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

protected lemma is_coprime.div_radical {a b : k[X]}
  (h : is_coprime a b) : is_coprime a.div_radical b.div_radical :=
begin
  rw ←polynomial.mul_radical_div_radical a at h,
  rw ←polynomial.mul_radical_div_radical b at h,
  exact h.of_mul_left_right.of_mul_right_right,
end

private lemma abc_subcall {a b c w : k[X]}
  {hw : w ≠ 0} (wab : w = wronskian a b)
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a)
  (abc_dr_dvd_w : (a*b*c).div_radical ∣ w) : 
    c.nat_degree < (a*b*c).radical.nat_degree :=
begin
  have hab := mul_ne_zero ha hb,
  have habc := mul_ne_zero hab hc,

  set abc_dr_nd := (a*b*c).div_radical.nat_degree with def_abc_dr_nd,
  set abc_r_nd := (a*b*c).radical.nat_degree with def_abc_r_nd,
  have t11 : abc_dr_nd < a.nat_degree + b.nat_degree := by calc
    abc_dr_nd ≤ w.nat_degree : 
        polynomial.nat_degree_le_of_dvd abc_dr_dvd_w hw
    ... < a.nat_degree + b.nat_degree :
        by rw wab at hw ⊢; exact wronskian.nat_degree_lt_add hw,
  have t4 : abc_dr_nd + abc_r_nd < a.nat_degree + b.nat_degree + abc_r_nd :=
    nat.add_lt_add_right t11 abc_r_nd,
  have t3 : abc_dr_nd + abc_r_nd = a.nat_degree + b.nat_degree + c.nat_degree := by calc
    abc_dr_nd + abc_r_nd = ((a*b*c).div_radical * (a*b*c).radical).nat_degree : 
      by rw ←polynomial.nat_degree_mul
        (polynomial.div_radical_ne_zero habc)
        (a*b*c).radical_ne_zero
    ... = (a*b*c).nat_degree :
      by rw mul_comm _ (polynomial.radical _);
         rw (a * b * c).mul_radical_div_radical
    ... = a.nat_degree + b.nat_degree + c.nat_degree :
      by rw [polynomial.nat_degree_mul hab hc, polynomial.nat_degree_mul ha hb],
  rw t3 at t4,
  exact nat.lt_of_add_lt_add_left t4,
end

private lemma rot3_add {a b c : k[X]} : a + b + c = b + c + a := by ring_nf
private lemma rot3_mul {a b c : k[X]} : a * b * c = b * c * a := by ring_nf

theorem polynomial.abc {a b c : k[X]}
  (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab: is_coprime a b) (hbc: is_coprime b c) (hca: is_coprime c a) (hsum: a + b + c = 0) : 
    (max3 a.nat_degree b.nat_degree c.nat_degree < (a*b*c).radical.nat_degree) ∨
    (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  -- Utility assertions
  have wbc := wronskian_eq_of_sum_zero hsum,
  set w := wronskian a b with wab,
  have wca : w = wronskian c a := begin
    rw rot3_add at hsum,
    have h := wronskian_eq_of_sum_zero hsum,
    rw ←wbc at h, exact h,
  end,
  have abc_dr_dvd_w : (a*b*c).div_radical ∣ w := begin
    have adr_dvd_w := a.div_radical_dvd_wronskian_left b,
    have bdr_dvd_w := a.div_radical_dvd_wronskian_right b,
    have cdr_dvd_w := b.div_radical_dvd_wronskian_right c,
    rw ←wab at adr_dvd_w bdr_dvd_w, 
    rw ←wbc at cdr_dvd_w,

    have cop_ab_dr := hab.div_radical,
    have cop_bc_dr := hbc.div_radical,
    have cop_ca_dr := hca.div_radical,
    have cop_abc_dr := cop_ca_dr.symm.mul_left cop_bc_dr,
    have abdr_dvd_w := cop_ab_dr.mul_dvd adr_dvd_w bdr_dvd_w,
    have abcdr_dvd_w := cop_abc_dr.mul_dvd abdr_dvd_w cdr_dvd_w,

    convert abcdr_dvd_w,

    rw ←polynomial.div_radical_mul hab,
    rw ←polynomial.div_radical_mul _,
    exact hca.symm.mul_left hbc,
  end,

  by_cases hw : w = 0,
  { right,
    rw hw at wab wbc,
    cases hab.wronskian_eq_zero_iff.mp wab.symm with ga gb,
    cases hbc.wronskian_eq_zero_iff.mp wbc.symm with _ gc,
    refine ⟨ga, gb, gc⟩, },
  { left, rw max3_lt_iff,
    refine ⟨_, _, _⟩,
    { rw rot3_mul at ⊢ abc_dr_dvd_w,
      apply abc_subcall wbc; assumption, },
    { rw [rot3_mul, rot3_mul] at ⊢ abc_dr_dvd_w,
      apply abc_subcall wca; assumption, },
    { apply abc_subcall wab; assumption, }, },
end

lemma pow_derivative_eq_zero 
  {n : ℕ} (chn : ¬(ring_char k ∣ n))
  {a : k[X]} (ha : a ≠ 0) :
  (a^n).derivative = 0 ↔ a.derivative = 0 :=
begin
  split,
  { intro apd,
    rw derivative_pow at apd,
    simp only [C_eq_nat_cast, mul_eq_zero] at apd,
    have pnz : a^(n-1) ≠ 0 := pow_ne_zero (n-1) ha,
    have cn_neq_zero : (↑(↑n : k) : k[X]) ≠ 0 := begin
      simp only [polynomial.C_eq_zero, ne.def,
        algebra_map.lift_map_eq_zero_iff],
      intro cn_eq_zero,
      exact chn (ring_char.dvd cn_eq_zero),
    end,
    tauto, },
  { intro hd, rw derivative_pow, rw hd, 
    simp only [mul_zero], },
end

theorem polynomial.flt
  {n : ℕ} (hn : 3 ≤ n) (chn : ¬(ring_char k ∣ n))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (hbc : is_coprime b c) (hca : is_coprime c a)
  (heq: a^n + b^n = c^n) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hap : a^n ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^n ≠ 0 := pow_ne_zero _ hb,
  have hcp : -c^n ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hc),

  have habp : is_coprime (a^n) (b^n) := is_coprime.pow hab,
  have hbcp : is_coprime (b^n) (-c^n) := (is_coprime.pow hbc).neg_right,
  have hcap : is_coprime (-c^n) (a^n) := (is_coprime.pow hca).neg_left,

  rw ←add_neg_eq_zero at heq,

  cases (polynomial.abc hap hbp hcp habp hbcp hcap heq) with ineq dr0,
  { exfalso,
    simp only [polynomial.nat_degree_neg,
      polynomial.nat_degree_pow] at ineq,
    have simp1 : a^n * b^n * -c^n = -(a*b*c)^n :=
      by rw [mul_pow, mul_pow, mul_neg],
    rw [simp1, max3_mul_left _ _ _ _] at ineq, clear simp1,
    rw polynomial.radical_neg at ineq,
    have np : 1 ≤ n := le_trans (by dec_trivial) hn,
    rw (a*b*c).radical_pow np at ineq, clear np,
    have ineq2 : (a * b * c).radical.nat_degree ≤ 
      n * max3 a.nat_degree b.nat_degree c.nat_degree := 
      by calc (a * b * c).radical.nat_degree ≤ (a*b*c).nat_degree : 
        polynomial.radical_nat_degree_le
      ... = a.nat_degree + b.nat_degree + c.nat_degree : 
        by rw polynomial.nat_degree_mul (mul_ne_zero ha hb) hc;
           rw polynomial.nat_degree_mul ha hb
      ... ≤ 3 * max3 a.nat_degree b.nat_degree c.nat_degree :
        add3_le_three_mul_max3 _ _ _
      ... ≤ n * max3 a.nat_degree b.nat_degree c.nat_degree :
        nat.mul_le_mul_right _ hn,
    apply eq.not_lt (eq.refl (n * max3 a.nat_degree b.nat_degree c.nat_degree)),
    exact ineq.trans_le ineq2, },
  { rw [polynomial.derivative_neg, neg_eq_zero] at dr0,
    rw [pow_derivative_eq_zero chn ha,
        pow_derivative_eq_zero chn hb,
        pow_derivative_eq_zero chn hc] at dr0,
    exact dr0 },
end

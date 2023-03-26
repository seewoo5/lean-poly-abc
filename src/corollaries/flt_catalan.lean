import algebra.char_p.basic
import algebra.euclidean_domain.defs

import mason_stothers

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

theorem polynomial.flt_catalan
  {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
  (hineq : q*r + r*p + p*q ≤ p*q*r)
  (chp : ¬(ring_char k ∣ p)) (chq : ¬(ring_char k ∣ q)) (chr : ¬(ring_char k ∣ r))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (heq: a^p + b^q = c^r) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have hbc : is_coprime b c,
  { rw [←is_coprime.pow_left_iff hq, ←is_coprime.pow_right_iff hr, ←heq],
    convert is_coprime.add_mul_right_right hab.symm.pow (1: k[X]),
    exact (one_mul _).symm, },
  have hca : is_coprime c a,
  { rw [←is_coprime.pow_left_iff hr, ←is_coprime.pow_right_iff hp, ←heq],
    convert is_coprime.mul_add_right_left hab.symm.pow (1: k[X]),
    exact (one_mul _).symm, },

  have hap : a^p ≠ 0 := pow_ne_zero _ ha,
  have hbp : b^q ≠ 0 := pow_ne_zero _ hb,
  have hcp : -c^r ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ hc),

  have habp : is_coprime (a^p) (b^q) := is_coprime.pow hab,
  have hbcp : is_coprime (b^q) (-c^r) := (is_coprime.pow hbc).neg_right,
  have hcap : is_coprime (-c^r) (a^p) := (is_coprime.pow hca).neg_left,
  have habcp : is_coprime ((a^p)*(b^q)) (-c^r) := hcap.symm.mul_left hbcp,

  rw ←add_neg_eq_zero at heq,

  cases (polynomial.abc hap hbp hcp habp hbcp hcap heq) with ineq dr0, swap,
  { rw [polynomial.derivative_neg, neg_eq_zero] at dr0,
    rw [pow_derivative_eq_zero chp ha,
        pow_derivative_eq_zero chq hb,
        pow_derivative_eq_zero chr hc] at dr0,
    exact dr0 },
  
  exfalso, apply not_le_of_lt ineq, clear ineq,
  rw [radical_mul habcp, radical_mul habp],
  rw [radical_pow a hp, radical_pow b hq, 
    radical_neg, radical_pow c hr],
  rw [←radical_mul hab, ←radical_mul (hca.symm.mul_left hbc)],
  apply le_trans radical_nat_degree_le,
  rw nat_degree_neg, simp_rw nat_degree_pow,
  have hpqr : 0 < p*q*r := nat.mul_le_mul
    (nat.mul_le_mul hp hq) hr,
  apply le_of_mul_le_mul_left _ hpqr,
  apply le_trans _ (nat.mul_le_mul_right _ hineq),
  convert weighted_average_le_max3,
  rw nat_degree_mul (mul_ne_zero ha hb) hc,
  rw nat_degree_mul ha hb,
  ring_nf,
end

theorem polynomial.flt_coprime
  {n : ℕ} (hn : 3 ≤ n) (chn : ¬(ring_char k ∣ n))
  {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : is_coprime a b) (heq: a^n + b^n = c^n) : 
  (a.derivative = 0 ∧ b.derivative = 0 ∧ c.derivative = 0) :=
begin
  have h1n : 1 ≤ n := le_trans (by dec_trivial) hn,
  apply polynomial.flt_catalan h1n h1n h1n _
    chn chn chn ha hb hc hab heq,
  have eq_lhs : n*n + n*n + n*n = 3*n*n := by ring_nf,
  rw eq_lhs, rw [mul_assoc, mul_assoc],
  apply nat.mul_le_mul_right (n*n), exact hn,
end
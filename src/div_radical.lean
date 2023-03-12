import data.polynomial.basic
import data.finset.basic
import data.multiset.basic
-- import order.disjoint
import data.polynomial.derivative
import ring_theory.polynomial.content
import ring_theory.unique_factorization_domain
import ring_theory.euclidean_domain
-- import ring_theory.principal_ideal_domain
import algebra.divisibility.units
import algebra.divisibility.basic
import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.group.basic
import algebra.group_power.basic
import algebra.char_p.basic
import init.data.nat.lemmas
import order.with_bot
import algebra.order.smul

import radical
import wronskian

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

-- This is the key to our implementation
def polynomial.div_radical (a : k[X]) : k[X] := a / a.radical

lemma polynomial.mul_radical_div_radical {a : k[X]} (ha : a ≠ 0) : 
  a.radical * a.div_radical = a :=
begin
  rw polynomial.div_radical, 
  rw ←(euclidean_domain.mul_div_assoc),
  refine euclidean_domain.mul_div_cancel_left _ _,
  exact a.radical_ne_zero,
  exact polynomial.radical_dvd_self ha,
end

lemma polynomial.div_radical_ne_zero {a : k[X]} (ha : a ≠ 0) : a.div_radical ≠ 0 :=
begin
  have h := ha, rw ←polynomial.mul_radical_div_radical ha at h,
  intro eqn, rw eqn at h, 
  simp only [mul_zero, ne.def, eq_self_iff_true, not_true] at h,
  exact h,
end

lemma polynomial.div_radical_is_unit {u : k[X]} (hu : is_unit u) : 
  is_unit u.div_radical :=
begin
  have u_neq_0 : u ≠ 0 := by
    intro h; subst h; revert hu; exact not_is_unit_zero,
  rw is_unit_iff_exists_inv at ⊢ hu,
  rcases hu with ⟨inv_u, eq_u⟩,
  use u.radical * inv_u,
  have eqn := polynomial.mul_radical_div_radical u_neq_0,
  rw mul_comm at eqn,
  rw [←mul_assoc, eqn],
  exact eq_u,
end

lemma eq_div_radical {a x : k[X]} (ha : a ≠ 0) (h : a.radical * x = a) : 
  x = a.div_radical :=
begin
  rw polynomial.div_radical,
  apply euclidean_domain.eq_div_of_mul_eq_left a.radical_ne_zero,
  rw mul_comm, exact h,
end

lemma polynomial.div_radical_mul {a b : k[X]} 
  (ha : a ≠ 0) (hb : b ≠ 0) (hc: is_coprime a b) : 
  (a * b).div_radical = a.div_radical * b.div_radical :=
begin
  symmetry, apply eq_div_radical,
  { exact mul_ne_zero ha hb },  
  rw polynomial.radical_mul ha hb hc,
  set c := a * b with eq_c,
  rw [←polynomial.mul_radical_div_radical ha, 
      ←polynomial.mul_radical_div_radical hb] at eq_c,
  rw eq_c, ring_nf,
end

lemma polynomial.div_radical_dvd_self {a : k[X]} (ha: a ≠ 0) : 
  a.div_radical ∣ a :=
begin
  rw polynomial.div_radical,
  apply euclidean_domain.div_dvd_of_dvd,
  exact polynomial.radical_dvd_self ha,
end

private def div_goal (a: k[X]) : Prop := a.div_radical ∣ a.derivative

private lemma div_goal_const (u: k) : div_goal (polynomial.C u) := 
begin
  rw [div_goal, derivative_C],
  exact dvd_zero _,
end

private lemma div_goal_one : div_goal (1 : k[X]) := div_goal_const 1

private lemma div_goal_unit {u : k[X]} (hu : is_unit u) : div_goal u :=
  (polynomial.div_radical_is_unit hu).dvd

private lemma normalize_dvd_pow {a : k[X]} (ha : a ≠ 0) (n : ℕ) : 
  (normalize a) ∣ a^(n + 1) :=
begin
  have na := associated_normalize a,
  have na2 := associated.symm na,
  rw associated at na2,
  rcases na2 with ⟨u, eq⟩,
  have eq2 : a^(n+1) = (normalize a) * (u * a^n),
  {
    calc a^(n+1) = a^n * a^1 : pow_add a n 1
    ... = a^1 * a^n : mul_comm _ _
    ... = a * a^n : by simp
    ... = (normalize a * u) * a^n : by rw eq
    ... = (normalize a) * (u * a^n) : mul_assoc (normalize a) u (a^n)
  },
  exact dvd.intro (u * a^n) (eq2.symm),
end

lemma div_radical_prime_pow_associated {a : k[X]} (pa : prime a) (n : ℕ) : 
  associated (a^(n+1)).div_radical (a^n) :=
begin
  rw polynomial.div_radical,
  rw (polynomial.radical_prime_pow pa 
    (show 0 < n+1, by dec_trivial)),
  have na := normalize_associated a,
  have ha := pa.ne_zero,
  have hna : normalize a ≠ 0 :=
  begin
    intro h,
    rw normalize_eq_zero at h,
    exact pa.ne_zero h,
  end,
  have h2 := associated.refl (a^(n+1)),
  have h3 : (a^(n+1) / (normalize a)) * (normalize a) = a^(n+1) :=
    begin
      have w := euclidean_domain.mul_div_assoc (normalize a) (normalize_dvd_pow ha n),
      have w2 := euclidean_domain.mul_div_cancel_left (a^(n+1)) hna,
      rw mul_comm (normalize a) (a^(n+1) / normalize a) at w,
      exact eq.trans (w.symm) w2,
    end,
    apply associated.of_mul_right _ (normalize_associated a) hna,
    rw h3,
  have pow_eq : a^(n+1) = a^n * a,
  {
    calc a^(n+1) = a^n * a^1 : pow_add a n 1
    ... = a^n * a : by simp,
  },
  rw pow_eq,
end

lemma div_goal_prime_pow {a: k[X]} (pa: prime a) (n: ℕ) : 
  div_goal (a^(n+1)) :=
begin
  have ha := pa.ne_zero,
  rw [div_goal, derivative_pow a (n+1)],
  have a_pow_assoc := div_radical_prime_pow_associated pa n,
  rw associated.dvd_iff_dvd_left a_pow_assoc,
  simp only [nat.cast_add, algebra_map.coe_one, map_add, C_eq_nat_cast, map_one, nat.add_succ_sub_one, add_zero],
  rw [mul_comm, ←mul_assoc],
  simp,
end

lemma div_goal_is_coprime {a b: k[X]} (ha: a ≠ 0) (hb : b ≠ 0) 
  (hc: is_coprime a b) : div_goal a -> div_goal b -> div_goal (a*b) :=
begin
  intros xa xb,
  rw div_goal at ⊢ xa xb,
  rw derivative_mul,
  have a_dvd := polynomial.div_radical_dvd_self ha,
  have b_dvd := polynomial.div_radical_dvd_self hb,
  have a_b_diff_dvd := mul_dvd_mul a_dvd xb,
  have a_diff_b_dvd := mul_dvd_mul xa b_dvd,
  rw ← (polynomial.div_radical_mul ha hb hc) at a_b_diff_dvd a_diff_b_dvd,
  exact dvd_add a_diff_b_dvd a_b_diff_dvd,
end

theorem polynomial.div_radical_dvd_derivative {a : k[X]} (ha : a ≠ 0) : 
  a.div_radical ∣ a.derivative :=
begin
  rw ←div_goal, 
  revert ha,
  apply induction_on_coprime a,
  { simp only [ne.def, eq_self_iff_true, not_true, is_empty.forall_iff], },
  { intros _ ux _, exact div_goal_unit ux, },
  { intros p i hp _,
    cases i with i,
    { rw pow_zero, exact div_goal_one, },
    { rw (show i.succ = i + 1, by refl),
      refine div_goal_prime_pow hp i, }, },

  intros x y hpxy hx hy xy_nz,
  have hc : is_coprime x y,
  {
    apply euclidean_domain.is_coprime_of_dvd _ _,

    simp at xy_nz,
    tauto,
    intros p hp p_nz p_div_x p_div_y,
    have pu := hpxy p p_div_x p_div_y,
    simp at hp,
    exact hp pu,
  },

  rw mul_ne_zero_iff at xy_nz,
  cases xy_nz with nzx nzy,
  exact div_goal_is_coprime nzx nzy hc (hx nzx) (hy nzy),
end

theorem polynomial.div_radical_dvd_wronskian_left (a b : k[X]) : 
  a.div_radical ∣ wronskian a b :=
begin
  by_cases a_nz : a = 0,
  { subst a_nz, rw wronskian_zero_left b, exact dvd_zero _, },
  rw wronskian,
  apply dvd_sub,
  { apply dvd_mul_of_dvd_left, 
    exact polynomial.div_radical_dvd_self a_nz, },
  { apply dvd_mul_of_dvd_left,
    exact polynomial.div_radical_dvd_derivative a_nz, },
end

theorem polynomial.div_radical_dvd_wronskian_right (a b : k[X]) : 
  b.div_radical ∣ wronskian a b :=
begin
  rw [wronskian_anticomm, dvd_neg],
  exact b.div_radical_dvd_wronskian_left _,
end
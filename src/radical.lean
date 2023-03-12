/- Radical of a polynomial.
Definition and properties.
This file also contains the proof of "main lemma" for polynomial ABC: a / rad(a) divides a'.
-/

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

noncomputable theory

open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]


-- Definitions

/- Radical of polynomial: rad(a) = product of monic (normalized) factors.
Note that there's a notion of `normalization_monoid` that somehow generalizes the concept of polynomial ring, leading coefficient, and monic polynomial.
-/

def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

def rad (a: k[X]) : k[X] := 
  (prime_factors a).prod id

/- Polynomial divided by its radical: div_rad(a) = a / rad(a).
We will eventually prove that div_rad(a) divides a'.
-/

-- define div_rad(a) as a / rad(a)
def div_rad (a : k[X]) : k[X] := a / (rad a)

def div_rad_dvd_deriv (a: k[X]) : Prop := (div_rad a) ∣ a.derivative


-- Properties of radicals

-- rad(a) ∣ a. 
lemma rad_dvd_self (a : k[X]) (ha : a ≠ 0): rad a ∣ a :=
begin
  rw rad,
  have x := (prime_factors a).val,
  have y := normalized_factors_prod ha,
  rw ← associated.dvd_iff_dvd_right y,
  rw ← finset.prod_val,
  apply multiset.prod_dvd_prod_of_le,
  rw prime_factors,
  simp,
  exact multiset.dedup_le _,
end

-- radical(nonzero) = nonzero.
lemma rad_ne_zero {a: k[X]} (ha: a ≠ 0) : rad a ≠ 0 :=
begin
  rw [rad, ← finset.prod_val],
  apply multiset.prod_ne_zero,
  rw prime_factors,
  simp only [multiset.to_finset_val, multiset.mem_dedup], 
  exact zero_not_mem_normalized_factors _,
end


/- `rad_coprime_mul`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof)
1. Prime factors of a*b equal to the disjoint union of those of a and b. `coprime_mul_prime_factors_disj_union`
2. By definition of radical, we're done.
-/

-- Coprime polynomials have disjoint prime factors (as multisets)
lemma coprime_disjoint_factors {a b : k[X]} (hc: is_coprime a b) : (normalized_factors a).disjoint (normalized_factors b):=
begin
  intros x hxa hxb,
  have x_dvd_a := dvd_of_mem_normalized_factors hxa,
  have x_dvd_b := dvd_of_mem_normalized_factors hxb,
  have xp := prime_of_normalized_factor x hxa,
  have x_dvd_gcd := euclidean_domain.dvd_gcd x_dvd_a x_dvd_b,
  rw ←euclidean_domain.gcd_is_unit_iff at hc,
  have x_unit := is_unit_of_dvd_unit x_dvd_gcd hc,
  exact xp.not_unit x_unit,
end

-- Coprime polynomials have disjoint prime factors (as finsets)
lemma coprime_disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply coprime_disjoint_factors hc x_in_fa x_in_fb,
end

-- Prime factors of (a*b) is a disjoint union of those of a and b, when they are coprime.
lemma coprime_mul_prime_factors_disj_union {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = (prime_factors a).disj_union (prime_factors b) (coprime_disjoint_prime_factors hc) :=
begin
  rw [finset.disj_union_eq_union],
  simp_rw prime_factors, 
  apply finset.ext,
  intro x,
  simp,
  rw normalized_factors_mul ha hb, simp,
end

-- Main statement
lemma rad_coprime_mul {a b : k[X]} (ha: a ≠ 0) (hb: b ≠ 0) (hc: is_coprime a b) : 
  rad (a * b) = rad a * rad b :=
begin
  simp_rw rad,
  rw coprime_mul_prime_factors_disj_union ha hb hc,
  rw finset.prod_disj_union (coprime_disjoint_prime_factors hc),
end


/- `rad_pow`

For any polynomial a and n ∈ ℕ with n > 0, rad(a^n) = rad(a)

Proof) Show that the prime factors of a and a^n are the same (below `prime_factors_eq_pow`), and the result follows.
-/

-- Polynomial factors are invariant under power.
lemma prime_factors_eq_pow (a: k[X]) (n: ℕ) (hn: n > 0) : 
  prime_factors (a^n) = prime_factors a :=
begin
  simp_rw prime_factors,
  simp only [normalized_factors_pow],
  apply finset.ext,
  intro x,
  simp only [multiset.mem_to_finset],
  rw multiset.mem_nsmul _,
  exact ne_of_gt hn,
end

-- Main statement.
lemma rad_pow (a: k[X]) {n: nat} (hn: n > 0) : rad (a^n) = rad(a) :=
begin
  simp_rw [rad, prime_factors_eq_pow a n hn],
end


/- Main lemma: a / (rad a) divides a'.

The below proof is based on induction.
To be precise, we use `unique_factorization_monoid.induction_on_coprime` and to reduce to the cases when
1. a is a unit
2. a is a power of prime
3. if the statement is true for coprime a and b, then it is also true for a*b. (induction step)
-/


lemma div_rad_dvd_deriv_const (u : k) : div_rad_dvd_deriv (polynomial.C u) :=
begin
  rw div_rad_dvd_deriv,
  rw derivative_C,
  exact dvd_zero _,
end

lemma div_rad_dvd_deriv_one : div_rad_dvd_deriv (1 : k[X]) := div_rad_dvd_deriv_const 1

lemma div_rad_eq {x a : k[X]} (ha : a ≠ 0) : x = div_rad a ↔ x * (rad a) = a :=
begin
  have rad_nz := rad_ne_zero ha,
  split,
  { intro eq, subst eq, rw div_rad,
    rw mul_comm, 
    rw ←(euclidean_domain.mul_div_assoc),
    exact euclidean_domain.mul_div_cancel_left _ rad_nz,
    exact rad_dvd_self _ ha, },
  { intro eq, rw div_rad, 
    apply euclidean_domain.eq_div_of_mul_eq_left _ eq,
    exact rad_nz, },
end

lemma mul_div_rad_rad {a : k[X]} (ha : a ≠ 0) : (div_rad a) * (rad a) = a :=
begin
  rw ← div_rad_eq ha,
end

lemma rad_deg_le_deg {a: k[X]} (ha : a ≠ 0) : (rad a).degree ≤ a.degree :=
begin
  set rhs := a.degree with eq_rhs,
  rw ←mul_div_rad_rad ha at eq_rhs,
  rw [←zero_add (rad a).degree, eq_rhs, degree_mul],
  rw with_bot.add_le_add_iff_right,
  { cases le_or_lt 0 (div_rad a).degree with h h,
    exact h, 
    exfalso, 
    simp only [polynomial.degree_eq_bot, nat.with_bot.lt_zero_iff] at h,
    have eqn := mul_div_rad_rad ha,
    rw h at eqn, simp at eqn, rw eqn at ha, simp at ha, exact ha, },
  { intro h, rw polynomial.degree_eq_bot at h,
    have eqn := mul_div_rad_rad ha,
    rw h at eqn, simp at eqn, rw eqn at ha, simp at ha, exact ha, },
end

lemma div_rad_unit {u : k[X]} (hu : is_unit u) : is_unit (div_rad u) :=
begin
  have u_neq_0 : u ≠ 0 := by
    intro h; subst h; revert hu; exact not_is_unit_zero,
  rw is_unit_iff_exists_inv at ⊢ hu,
  rcases hu with ⟨inv_u, eq_u⟩,
  use rad u * inv_u,
  rw [←mul_assoc, mul_div_rad_rad u_neq_0],
  exact eq_u,
end 

lemma div_rad_dvd_deriv_unit {u : k[X]} (hu : is_unit u) : div_rad_dvd_deriv u :=
begin
  rw div_rad_dvd_deriv,
  exact (div_rad_unit hu).dvd,
end

lemma rad_prime_eq (a : k[X]) (ha: prime a) : rad a = normalize a :=
begin
  rw rad,
  rw prime_factors,
  have ia := ha.irreducible,
  have na := normalized_factors_irreducible ia,
  rw na,
  simp only [multiset.to_finset_singleton, id.def, finset.prod_singleton],
end

lemma rad_prime_pow (a : k[X]) (ha: prime a) (n : ℕ) (hn : n > 0): rad (a^n) = normalize a :=
begin
  rw (rad_pow a hn),
  exact (rad_prime_eq a ha),
end

lemma dvd_normalize_pow (a : k[X]) (n : ℕ) (ha : a ≠ 0) : (normalize a) ∣ a^(n + 1) :=
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

lemma dvd_rad_prime_pow (a : k[X]) (n : ℕ) (pa : prime a) (ha : a ≠ 0) : associated (div_rad (a^(n+1))) (a^n) :=
begin
  rw div_rad,
  rw (rad_prime_pow a pa (n + 1) (by dec_trivial)),
  have na := associated_normalize a,
  rw associated.comm at na,
  have hna : normalize a ≠ 0 :=
  begin
    intro h,
    rw normalize_eq_zero at h,
    exact ha h,
  end,
  have h2 := associated.refl (a^(n+1)),
  have h3 : (a^(n+1) / (normalize a)) * (normalize a) = a^(n+1) :=
    begin
      have w := euclidean_domain.mul_div_assoc (normalize a) (dvd_normalize_pow a n ha),
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

/- Main statement of Step 2. For prime powers.
Note that the exponent is `n+1` instead of `n`.
-/
lemma div_rad_dvd_deriv_prime_power (a: k[X]) (ha : a ≠ 0) (pa: prime a) (n: ℕ) : div_rad_dvd_deriv (a^(n+1)) :=
begin
  rw div_rad_dvd_deriv,
  rw derivative_pow a (n+1),
  have a_pow_assoc := dvd_rad_prime_pow a n pa ha,
  rw associated.dvd_iff_dvd_left a_pow_assoc,
  simp only [nat.cast_add, algebra_map.coe_one, map_add, C_eq_nat_cast, map_one, nat.add_succ_sub_one, add_zero],
  rw [mul_comm, ←mul_assoc],
  simp,
end


-- Step 3.

-- `div_rad` is multiplicative for coprime pairs.
lemma div_rad_coprime_mul {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc: is_coprime a b) : div_rad (a * b) = (div_rad a) * (div_rad b) :=
begin
  symmetry, rw div_rad_eq _,
  rw rad_coprime_mul ha hb hc,
  set c := a * b with eq_c,
  rw [←mul_div_rad_rad ha, ←mul_div_rad_rad hb] at eq_c,
  rw eq_c, ring_nf, simp, tauto,
end


-- div_rad(a) divides a.
lemma div_rad_dvd_self (a : k[X]) (ha: a ≠ 0) : div_rad a ∣ a :=
begin
  rw div_rad,
  exact euclidean_domain.div_dvd_of_dvd (rad_dvd_self a ha),
end

/- Main statement of Step 3. Induction step.
If the lemma is true for coprime a and b, then it is also true for (a*b).
Proof uses Leibniz rule `derivative_mul`, `div_rad_dvd_self`, and the fact that div_rad is multiplicative for coprime pairs `div_rad_coprime_mul`.
-/
lemma div_rad_dvd_deriv_induction (a b: k[X]) (ha: a ≠ 0) (hb : b ≠ 0) (hc: is_coprime a b) : div_rad_dvd_deriv a -> div_rad_dvd_deriv b -> div_rad_dvd_deriv (a*b) :=
begin
  intros xa xb,
  rw div_rad_dvd_deriv,
  rw div_rad_dvd_deriv at xa xb,
  rw derivative_mul,
  have a_dvd := div_rad_dvd_self a ha,
  have b_dvd := div_rad_dvd_self b hb,
  have a_b_deriv_dvd := mul_dvd_mul a_dvd xb,
  have a_deriv_b_dvd := mul_dvd_mul xa b_dvd,
  rw ← (div_rad_coprime_mul ha hb hc) at a_b_deriv_dvd a_deriv_b_dvd,
  exact dvd_add a_deriv_b_dvd a_b_deriv_dvd,
end


-- The final proof of the main lemma based on the above intermediate steps.
theorem div_rad_dvd_deriv_always {a : k[X]} (ha : a ≠ 0) : div_rad_dvd_deriv a :=
begin
  revert ha,
  apply induction_on_coprime a,

  simp only [ne.def, eq_self_iff_true, not_true, is_empty.forall_iff],
  intros _ ux _,
  exact div_rad_dvd_deriv_unit ux,

  { intros p i hp _,
    cases i with i,
    { rw pow_zero, exact div_rad_dvd_deriv_one, },
    { rw (show i.succ = i + 1, by refl),
      refine div_rad_dvd_deriv_prime_power p _ hp i,
      simp only [ne.def, pow_eq_zero_iff, nat.succ_pos'] at ha,
      exact ha, }, },

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
  exact div_rad_dvd_deriv_induction _ _ nzx nzy hc (hx nzx) (hy nzy),
end

protected lemma is_coprime.div_rad {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : is_coprime a b) : is_coprime (div_rad a) (div_rad b) :=
begin
  rw ←mul_div_rad_rad ha at h,
  rw ←mul_div_rad_rad hb at h,
  exact h.of_mul_left_left.of_mul_right_left,
end

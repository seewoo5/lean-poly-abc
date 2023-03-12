import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.char_p.basic
import algebra.divisibility.basic
import algebra.divisibility.units
import algebra.group.basic
import algebra.group_power.basic
import algebra.order.smul
import data.polynomial.basic
import data.finset.basic
import data.multiset.basic
import data.polynomial.derivative
import init.data.nat.lemmas
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

-- Wronskian: W(a, b) = ab' - a'b
def wronskian (a b : k[X]) : k[X] :=
  a * b.derivative - a.derivative * b

/- Radical of polynomial: rad(a) = product of monic (normalized) factors.
Note that there's a notion of `normalization_monoid` that somehow generalizes the concept of polynomial ring, leading coefficient, and monic polynomial.
-/
def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

def rad (a: k[X]) : k[X] := 
  (prime_factors a).prod id


-- Basic properties of Wronskian

@[simp]
lemma wronskian_zero_left (a : k[X]) : wronskian 0 a = 0 :=
by simp_rw wronskian; simp only [zero_mul, derivative_zero, sub_self]

@[simp]
lemma wronskian_zero_right (a : k[X]) : wronskian a 0 = 0 :=
by simp_rw wronskian; simp only [derivative_zero, mul_zero, sub_self]

lemma wronskian_neg_left (a b : k[X]) : wronskian (-a) b = - (wronskian a b) :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_neg_right (a b : k[X]) : wronskian a (-b) = - wronskian a b :=
by simp_rw [wronskian, derivative_neg]; ring

lemma wronskian_add_right (a b c : k[X]) :
  wronskian a (b + c) = wronskian a b + wronskian a c :=
by simp_rw [wronskian, derivative_add]; ring

lemma wronskian_self (a : k[X]) : wronskian a a = 0 :=
by rw [wronskian, mul_comm, sub_self]

lemma wronskian_anticomm (a b : k[X]) : wronskian a b = - wronskian b a :=
by rw [wronskian, wronskian]; ring

lemma polynomial.degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ :=
  by intro h; rw polynomial.degree_eq_bot at h; exact ha h

lemma wronskian.deg_lt_add_deg_deg {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) : 
  (wronskian a b).degree < a.degree + b.degree :=
begin
  calc (wronskian a b).degree ≤ max (a * b.derivative).degree (a.derivative * b).degree : polynomial.degree_sub_le _ _
  ... < a.degree + b.degree : _,
  rw max_lt_iff, split; rw degree_mul,
  { rw with_bot.add_lt_add_iff_left (polynomial.degree_ne_bot ha),
    exact polynomial.degree_derivative_lt hb, },
  { rw with_bot.add_lt_add_iff_right (polynomial.degree_ne_bot hb),
    exact polynomial.degree_derivative_lt ha, },
end 



-- Properties of radicals

/- `rad_coprime_mul`

For any coprime polynomial a and b, rad(a*b) = rad(a) * rad(b)

Proof)
1. Prime factors of a*b equal to the disjoint union of those of a and b. `poly_coprime_mul_prime_factors_disj_union`
3. By definition of radical, we're done.
-/

-- Coprime polynomials have disjoint prime factors (as multisets)
lemma poly_coprime_disjoint_factors {a b : k[X]} (hc: is_coprime a b) : (normalized_factors a).disjoint (normalized_factors b):=
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
lemma poly_coprime_disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply poly_coprime_disjoint_factors hc x_in_fa x_in_fb,
end

-- Prime factors of (a*b) is a disjoint union of those of a and b, when they are coprime.
lemma poly_coprime_mul_prime_factors_disj_union {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : 
  prime_factors (a * b) = (prime_factors a).disj_union (prime_factors b) (poly_coprime_disjoint_prime_factors hc) :=
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
  rw poly_coprime_mul_prime_factors_disj_union ha hb hc,
  rw finset.prod_disj_union (poly_coprime_disjoint_prime_factors hc),
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

/- `rad_deg_le_deg` deg(rad(a)) ≤ deg(a)

Proof)
a = Product of all (factors a)

Fact 1.
deg (Product of a_1, a_2, ..., a_n) = Sum (deg a_1), deg a_2, ....

> polynomial.degree_prod

Fact 2. A : multiset is a subset (le) of B : multiset
-> sum A <= sum B

Fact 2-1. B = A ⊔ (B ∖ A)
Fact 2-2. sum B = sum (A ⊔ (B \ A)) = sum A + sum (B \ A)
Fact 2-3. sum (B \ A) : ℕ 
Fact 2-4. a = b + c in ℕ -> a ≥ b

> multiset.le

Fact 3. 
  (rad a).deg = (Product of all (factors a).to_finset).deg
    = Sum (factors a).to_finset  <- Fact 1
  
  a.deg = (Product of all (factors a)).deg
    = Sum (factors a)  <- Fact 1

  Goal : Sum (factors a).to_finset <= Sum (factors a)
    (factors a).to_finset is a subset of (factors a)
  
-/

lemma div_rad_dvd (a : k[X]) (ha : a ≠ 0): rad a ∣ a :=
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

lemma rad_ne_zero {a: k[X]} (ha: a ≠ 0) : rad a ≠ 0 :=
begin
  rw [rad, ← finset.prod_val],
  apply multiset.prod_ne_zero,
  rw prime_factors,
  simp only [multiset.to_finset_val, multiset.mem_dedup], 
  exact zero_not_mem_normalized_factors _,
end 


/- Main lemma: a / (rad a) divides a'.

The below proof is based on induction.
To be precise, we use `unique_factorization_monoid.induction_on_coprime` and to reduce to the cases when
1. a is a unit
2. a is a power of prime
3. if the statement is true for coprime a and b, then it is also true for a*b. (induction step)
-/

-- define div_rad(a) as a / rad(a)
def div_rad (a : k[X]) : k[X] := a / (rad a)

def div_rad_dvd_deriv (a: k[X]) : Prop := (div_rad a) ∣ a.derivative


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
    exact div_rad_dvd _ ha, },
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


-- lemma div_rad_coprime_mul (a b : k[X]) (ha : a ≠ 0) (hb : b ≠ 0) (hc : is_coprime a b) : div_rad(a * b) = (div_rad a) * (div_rad b) :=
-- begin
--   simp_rw div_rad,
--   rw rad_coprime_mul ha hb hc,
--   symmetry,
--   exact div_mul_div_comm a (rad a) b (rad b),
-- end

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

lemma div_rad_coprime_mul {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc: is_coprime a b) : div_rad (a * b) = (div_rad a) * (div_rad b) :=
begin
  symmetry, rw div_rad_eq _,
  rw rad_coprime_mul ha hb hc,
  set c := a * b with eq_c,
  rw [←mul_div_rad_rad ha, ←mul_div_rad_rad hb] at eq_c,
  rw eq_c, ring_nf, simp, tauto,
end

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

-- div_rad(a) divides a.
lemma div_rad_dvd_self (a : k[X]) (ha: a ≠ 0) : div_rad a ∣ a :=
begin
  rw div_rad,
  exact euclidean_domain.div_dvd_of_dvd (div_rad_dvd a ha),
end

/- Induction step of the main lemma.
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


-- The final proof of the main lemma based on the above lemmata.
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

protected lemma is_coprime.div_rad {a b : k[X]} (ha : a ≠ 0) (hb : b ≠ 0)
  (h : is_coprime a b) : is_coprime (div_rad a) (div_rad b) :=
begin
  rw ←mul_div_rad_rad ha at h,
  rw ←mul_div_rad_rad hb at h,
  exact h.of_mul_left_left.of_mul_right_left,
end

/- ABC for polynomials (Mason-Stothers theorem)

For coprime polynomials a, b, c satisfying a + b + c = 0 and deg(a) ≥ deg(rad(abc)), we have a' = b' = c' = 0.

Proof is based on this online note by Franz Lemmermeyer http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf, which is essentially based on Noah Snyder's proof ("An Alternative Proof of Mason's Theorem"), but slightly deriverent.

1. Show that W(a, b) = W(b, c) = W(c, a) =: W. `wronskian_eq_of_sum_zero`
2. (a / rad(a)) | W, and same for b and c. `div_rad_dvd_wronskian_left` and `div_rad_dvd_wronskian_right`
3. a / rad(a), b / rad(b), c / rad(c) are all coprime, so their product abc / rad(abc) also divides W. `poly_coprime_div_mul_div`
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

-- Lemma for Step 6.
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
1. By contradiction. Assume that
2. Apply ABC for polynomials with triple (a^n, b^n, c^n):

-> max (deg a^n, deg b^n, deg c^n) = n * max (deg a, deg b, deg c) + 1
≤ deg (rad (a^n * b^n * c^n)) 
≤ deg (rad (a * b * c))
≤ deg (abc)
≤ deg a + deg b + deg c
≤ 3 * max (deg a, deg b, deg c)

and from n ≥ 3, we should have max (deg a, deg b, deg c) = ⟂, i.e. at least one of a, b, c is zero.

-/

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


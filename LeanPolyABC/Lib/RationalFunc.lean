import Mathlib.Tactic.Core
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.FieldTheory.RatFunc.Defs

#align_import lib.rational_func

-- for no_zero_divisors instance
-- for no_zero_divisors instance
noncomputable section

open scoped Classical Polynomial

open RatFunc

variable {k : Type _} [Field k]

private theorem aux_is_unit {a : k[X]} (ha : a ≠ 0) : IsUnit (Polynomial.C a.leadingCoeff⁻¹) :=
  by
  rw [Polynomial.isUnit_C]
  apply IsUnit.inv
  rw [← Polynomial.leadingCoeff_ne_zero] at ha
  exact Ne.isUnit ha

private theorem div_mul_eq {a b : k[X]} (h : a ∣ b) : b / a * a = b :=
  by
  rw [← EuclideanDomain.mod_eq_zero] at h
  have t := EuclideanDomain.div_add_mod b a
  rw [h, add_zero, mul_comm] at t; exact t

theorem IsCoprime.num_denom (x : RatFunc k) : IsCoprime x.num x.den :=
  by
  apply RatFunc.induction_on x
  intro p q q_nz
  rw [RatFunc.num_div, RatFunc.denom_div _ q_nz]
  have hnz : q / gcd p q ≠ 0 := by
    intro h; apply q_nz
    rw [← div_mul_eq (gcd_dvd_right p q)]
    rw [h, MulZeroClass.zero_mul]
  rw [isCoprime_mul_unit_left_left (aux_is_unit hnz) (p / gcd p q) _]
  rw [isCoprime_mul_unit_left_right (aux_is_unit hnz) (p / gcd p q) _]
  clear hnz
  rw [← gcd_isUnit_iff]
  have hnz : gcd p q ≠ 0 := gcd_ne_zero_of_right q_nz
  refine' isUnit_of_associated_mul _ hnz
  apply Associated.trans (gcd_mul_left' _ _ _).symm
  rw [mul_comm (gcd p q), mul_comm (gcd p q)]
  rw [div_mul_eq (gcd_dvd_left p q), div_mul_eq (gcd_dvd_right p q)]

def IsConst (x : RatFunc k) :=
  ∃ c : k, x = RatFunc.C c

theorem associates_pow_eq_pow_iff {A B : Associates k[X]} {n : ℕ} (hn : 0 < n) :
    A ^ n = B ^ n ↔ A = B := by
  by_cases hA : A = 0
  · subst hA
    rw [zero_pow hn, eq_comm, pow_eq_zero_iff hn, eq_comm]
    exact Associates.noZeroDivisors
  by_cases hB : B = 0
  · subst hB
    rw [zero_pow hn, pow_eq_zero_iff hn]
    exact Associates.noZeroDivisors
  constructor; swap
  · intro h; subst h
  intro h
  apply Associates.eq_of_eq_counts hA hB
  intro p hp
  apply Nat.eq_of_mul_eq_mul_left hn
  rw [← Associates.count_pow hA hp n, ← Associates.count_pow hB hp n, h]

example (p q : ℕ) (f : ℕ → ℕ) (h : p = q) : f p = f q :=
  congr_arg f h

theorem isConst_of_associated {f : RatFunc k} (h : Associated f.num f.den) : IsConst f :=
  by
  rcases h.symm with ⟨u, heq⟩
  rcases polynomial.is_unit_iff.mp u.is_unit with ⟨c, uc, eq_c⟩
  rw [← eq_c] at heq
  have tt := congr_arg (algebraMap (Polynomial k) (RatFunc k)) HEq.symm
  rw [map_mul, mul_comm] at tt
  have uu := div_eq_of_eq_mul (algebra_map_ne_zero f.denom_ne_zero) tt
  rw [f.num_div_denom, RatFunc.algebraMap_C] at uu
  use c; exact uu

theorem isConst_of_root_unity {n : ℕ} (hn : 0 < n) {f : RatFunc k} (h : f ^ n = 1) : IsConst f :=
  by
  rw [← f.num_div_denom, div_pow, ← map_pow, ← map_pow] at h
  have nz : algebraMap k[X] (RatFunc k) (f.denom ^ n) ≠ 0
  apply algebra_map_ne_zero; apply pow_ne_zero; exact f.denom_ne_zero
  rw [← mul_left_inj' nz, div_mul_cancel₀ (algebraMap k[X] (RatFunc k) (f.num ^ n)) nz, one_mul] at
    h
  have hh := congr_arg Associates.mk (algebraMap_injective k h)
  rw [Associates.mk_pow, Associates.mk_pow, associates_pow_eq_pow_iff hn,
    Associates.mk_eq_mk_iff_associated] at hh
  exact isConst_of_associated hh

theorem associated_pow_pow_coprime_iff {a b : k[X]} {m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hm : 0 < m)
    (hn : 0 < n) (h : Associated (a ^ m) (b ^ n)) (hcp : m.Coprime n) :
    ∃ c : k[X], c ≠ 0 ∧ Associated a (c ^ n) ∧ Associated b (c ^ m) :=
  by
  -- change to associates
  simp_rw [← Associates.mk_eq_mk_iff_associated, Associates.mk_pow] at h ⊢
  rw [← Associates.mk_ne_zero] at ha hb
  set A := Associates.mk a with eq_A
  set B := Associates.mk b with eq_B
  rw [← eq_A] at ha; rw [← eq_B] at hb
  rename' ha => hA; rename' hb => hB
  clear_value A B; clear eq_A eq_B a b
  suffices goal : ∃ C, A = C ^ n ∧ B = C ^ m
  rcases goal with ⟨C, hC⟩
  use C.out; simp only [Associates.mk_out]
  refine' ⟨_, hC⟩
  rw [← Associates.mk_ne_zero, Associates.mk_out, ← pow_ne_zero_iff hn, ← hC.1]
  exact hA; exact Associates.noZeroDivisors
  have subgoal : ∃ C, A = C ^ n :=
    by
    apply Associates.is_pow_of_dvd_count hA
    intro p hp
    apply hcp.symm.dvd_of_dvd_mul_left
    rw [← Associates.count_pow hA hp, h, Associates.count_pow hB hp]
    exact Nat.dvd_mul_right _ _
  rcases subgoal with ⟨C, eq_ACn⟩
  refine' ⟨C, eq_ACn, _⟩
  rw [eq_ACn, pow_right_comm, associates_pow_eq_pow_iff hn] at h
  exact h.symm

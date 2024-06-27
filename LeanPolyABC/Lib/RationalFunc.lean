import Mathlib.Tactic.Core
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Associated
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial

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

def IsConst (x : RatFunc k) :=
  ∃ c : k, x = RatFunc.C c

theorem associates_pow_eq_pow_iff {A B : Associates k[X]} {n : ℕ} (hn : n ≠ 0) :
    A ^ n = B ^ n ↔ A = B := by
  by_cases hA : A = 0
  · subst hA
    rw [zero_pow hn, eq_comm, pow_eq_zero_iff hn, eq_comm]
  by_cases hB : B = 0
  · subst hB
    rw [zero_pow hn, pow_eq_zero_iff hn]
  · constructor; swap
    . intro h; subst h; rfl
    . intro h
      apply Associates.eq_of_eq_counts hA hB
      intro p hp
      apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hn)
      rw [← Associates.count_pow hA hp n, ← Associates.count_pow hB hp n, h]

theorem isConst_of_associated {f : RatFunc k} (h : Associated f.num f.denom) : IsConst f :=
  by
  rcases h.symm with ⟨u, heq⟩
  rcases Polynomial.isUnit_iff.mp u.isUnit with ⟨c, uc, eq_c⟩
  rw [← eq_c] at heq
  have tt := congr_arg (algebraMap (Polynomial k) (RatFunc k)) heq.symm
  rw [map_mul, mul_comm] at tt
  have uu := div_eq_of_eq_mul (algebraMap_ne_zero f.denom_ne_zero) tt
  rw [f.num_div_denom, RatFunc.algebraMap_C] at uu
  use c

theorem isConst_of_root_unity {n : ℕ} (hn : n ≠ 0) {f : RatFunc k} (h : f ^ n = 1) : IsConst f :=
  by
  rw [← f.num_div_denom, div_pow, ← map_pow, ← map_pow] at h
  have nz : algebraMap k[X] (RatFunc k) (f.denom ^ n) ≠ 0 := by
    apply algebraMap_ne_zero; apply pow_ne_zero; exact f.denom_ne_zero
  rw [← mul_left_inj' nz, div_mul_cancel₀ (algebraMap k[X] (RatFunc k) (f.num ^ n)) nz, one_mul] at h
  have hh := congr_arg Associates.mk (algebraMap_injective k h)
  rw [Associates.mk_pow, Associates.mk_pow, associates_pow_eq_pow_iff hn,
    Associates.mk_eq_mk_iff_associated] at hh
  exact isConst_of_associated hh

theorem associated_pow_pow_coprime_iff {a b : k[X]} {m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0)
    (hn : n ≠ 0) (h : Associated (a ^ m) (b ^ n)) (hcp : m.Coprime n) :
    ∃ c : k[X], c ≠ 0 ∧ Associated a (c ^ n) ∧ Associated b (c ^ m) :=
  by
  -- change to associates
  simp_rw [← Associates.mk_eq_mk_iff_associated, Associates.mk_pow] at h ⊢
  rw [← Associates.mk_ne_zero] at ha hb
  set A := Associates.mk a with eq_A
  set B := Associates.mk b with eq_B
  rename' ha => hA; rename' hb => hB
  clear_value A B; clear eq_A eq_B
  suffices goal : ∃ C, A = C ^ n ∧ B = C ^ m by
    rcases goal with ⟨C, hC⟩
    use C.out; simp only [Associates.mk_out]
    refine' ⟨_, hC⟩
    rw [← Associates.mk_ne_zero, Associates.mk_out, ← pow_ne_zero_iff hn, ← hC.1]
    exact hA
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

import .radical
import .wronskian

/-
On `div_radical(a) = a / radical(a)`. The purpose of this file is to prove our "main lemma" that `div_radical(a)` divides `a'` for any nonzero polynomial `a`.
The proof is based on induction (`unique_factorization_domain.induction_on_coprime`).
-/


noncomputable theory
open_locale polynomial classical

namespace polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

/-- For a given polynomial `a`, `div_radical(a)` is `a` divided by its radical `rad(a)`. This is the key to our implementation. -/
def div_radical (a : k[X]) : k[X] := a / a.radical

lemma mul_radical_div_radical (a : k[X]) : 
  a.radical * a.div_radical = a :=
begin
  rw div_radical, 
  rw ←(euclidean_domain.mul_div_assoc),
  refine euclidean_domain.mul_div_cancel_left _ _,
  exact a.radical_ne_zero,
  exact radical_dvd_self a,
end

lemma div_radical_ne_zero {a : k[X]} (ha : a ≠ 0) : a.div_radical ≠ 0 :=
begin
  rw ← mul_radical_div_radical a at ha,
  exact right_ne_zero_of_mul ha,
end

lemma div_radical_is_unit {u : k[X]} (hu : is_unit u) : 
  is_unit u.div_radical :=
begin
  rwa [div_radical, radical_is_unit hu, euclidean_domain.div_one],
end

lemma eq_div_radical {a x : k[X]} (h : a.radical * x = a) :
  x = a.div_radical :=
begin
  apply euclidean_domain.eq_div_of_mul_eq_left a.radical_ne_zero,
  rwa mul_comm,
end

lemma div_radical_mul {a b : k[X]} (hc: is_coprime a b) : 
  (a * b).div_radical = a.div_radical * b.div_radical :=
begin
  by_cases ha : a = 0,
  { rw [ha, zero_mul, div_radical, euclidean_domain.zero_div, zero_mul] },
  by_cases hb : b = 0,
  { rw [hb, mul_zero, div_radical, euclidean_domain.zero_div, mul_zero] },
  symmetry, apply eq_div_radical,
  rw radical_mul hc,
  rw [mul_mul_mul_comm, mul_radical_div_radical, mul_radical_div_radical],
end

lemma div_radical_dvd_self (a : k[X]) : 
  a.div_radical ∣ a :=
begin
  rw div_radical,
  apply euclidean_domain.div_dvd_of_dvd,
  exact radical_dvd_self a,
end

/- Main lemma: a / rad(a) ∣ a'.
Proof uses `induction_on_coprime` of `unique_factorization_domain`.
-/
theorem div_radical_dvd_derivative (a : k[X]) : 
  a.div_radical ∣ a.derivative :=
begin
  apply induction_on_coprime a,
  { /- when a is zero -/
    rw derivative_zero,
    apply dvd_zero,
  },
  { /- when a is unit -/
    exact λ a ha, (div_radical_is_unit ha).dvd,
  },
  { /- when a = p^i for some prime p -/
    rintros p (_ | i) hp,
    { rw [pow_zero, derivative_one],
      apply dvd_zero },
    rw [←mul_dvd_mul_iff_left (radical_ne_zero (p ^ i.succ)), mul_radical_div_radical,
        radical_prime_pow hp i.succ_pos, derivative_pow_succ, ← mul_assoc],
    apply dvd_mul_of_dvd_left,
    rw [mul_comm, mul_assoc],
    apply dvd_mul_of_dvd_right,
    rw [pow_succ', mul_dvd_mul_iff_left (pow_ne_zero i hp.ne_zero), dvd_normalize_iff],
  },
  { /- if it holds for coprime pair a and b, then it also holds for a * b. -/
    intros x y hpxy hx hy,
    have hc : is_coprime x y := euclidean_domain.is_coprime_of_dvd
      (λ ⟨hx, hy⟩, not_is_unit_zero (hpxy 0 (zero_dvd_iff.mpr hx) (zero_dvd_iff.mpr hy)))
      (λ p hp _ hpx hpy, hp (hpxy p hpx hpy)),
    rw [div_radical_mul hc, derivative_mul],
    exact dvd_add (mul_dvd_mul hx y.div_radical_dvd_self)
      (mul_dvd_mul x.div_radical_dvd_self hy),
  },
end

theorem div_radical_dvd_wronskian_left (a b : k[X]) : 
  a.div_radical ∣ wronskian a b :=
begin
  rw wronskian,
  apply dvd_sub,
  { apply dvd_mul_of_dvd_left, 
    exact div_radical_dvd_self a },
  { apply dvd_mul_of_dvd_left,
    exact div_radical_dvd_derivative a },
end

theorem div_radical_dvd_wronskian_right (a b : k[X]) : 
  b.div_radical ∣ wronskian a b :=
begin
  rw [wronskian_anticomm, dvd_neg],
  exact b.div_radical_dvd_wronskian_left _,
end

end polynomial
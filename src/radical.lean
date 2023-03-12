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

noncomputable theory
open_locale polynomial classical

open polynomial
open unique_factorization_monoid

variables {k: Type*} [field k]

lemma polynomial.degree_ne_bot {a : k[X]} (ha : a ≠ 0) : a.degree ≠ ⊥ :=
  by intro h; rw polynomial.degree_eq_bot at h; exact ha h

-- Radical of polynomial = product of monic (normalized) factors
def prime_factors (a: k[X]) : finset (k[X]) := 
  (normalized_factors a).to_finset

protected def polynomial.radical (a: k[X]) : k[X] := 
  (prime_factors a).prod id

-- coprime polynomials have disjoint prime factors (as multisets)
lemma is_coprime.disjoint_normalized_factors {a b : k[X]} (hc: is_coprime a b) : 
  (normalized_factors a).disjoint (normalized_factors b):=
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

-- coprime polynomials have disjoint prime factors (as finsets)
lemma is_coprime.disjoint_prime_factors {a b : k[X]} (hc: is_coprime a b) : 
  disjoint (prime_factors a) (prime_factors b):=
begin
  simp_rw prime_factors,
  rw finset.disjoint_left,
  intros x x_in_fa,
  intro x_in_fb,
  simp only [multiset.mem_to_finset] at x_in_fa x_in_fb,
  apply poly_coprime_disjoint_factors hc x_in_fa x_in_fb,
end


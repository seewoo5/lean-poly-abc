import algebra.associated
import algebra.big_operators.multiset.basic
import algebra.divisibility.basic
import algebra.divisibility.units
import algebra.group.basic
import algebra.group_power.basic
import algebra.order.smul
import data.finset.basic
import data.multiset.basic
import data.polynomial.basic
import data.polynomial.derivative
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

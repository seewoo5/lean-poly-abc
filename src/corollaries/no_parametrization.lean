import ring_theory.euclidean_domain
import ring_theory.polynomial.content
import field_theory.ratfunc

import .flt_catalan

noncomputable theory
open_locale classical polynomial

open ratfunc

variables {k: Type*} [field k]

def is_const (x : ratfunc k) := ∃ c : k, x = ratfunc.C c

theorem no_parametrization_y2_x3_1 
  {x y : ratfunc k} (eqn : y^2 = x^3 + 1) : is_const x ∧ is_const y := sorry
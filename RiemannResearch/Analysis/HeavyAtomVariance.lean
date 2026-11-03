/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp variance bound for a distinguished atom of mass at least one half

Source: elementary conditional-variance derivation in
PrimeTensorCRTResults20261102.md, section 3. This module verifies the
complete scalar gap. In a normalized [0,1]-valued distribution, x is the
distinguished value and m,v are the mean and second moment of its complement.
The Q gcd-cell application and its summation are proved on paper separately.
-/
namespace RiemannResearch.Analysis.HeavyAtomVariance

theorem gap_identity (t x m v : ℝ) :
    t*(1-t) - (t*x^2+(1-t)*v-(t*x+(1-t)*m)^2) =
      (1-x)*(1-t)*(1-m)*(t-(1-t)*m) +
      x*(1-t)*m*(t-(1-t)*(1-m)) +
      t*(1-t)*x*(1-x) + (1-t)*(m-v) := by
  ring

theorem variance_le (t x m v : ℝ) (ht : 1 / 2 ≤ t) (ht1 : t ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hv : v ≤ m) :
    t*x^2+(1-t)*v-(t*x+(1-t)*m)^2 ≤ t*(1-t) := by
  have ht0 : 0 ≤ t := by linarith
  have h1t : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have h1x : 0 ≤ 1-x := sub_nonneg.mpr hx1
  have h1m : 0 ≤ 1-m := sub_nonneg.mpr hm1
  have hmv : 0 ≤ m-v := sub_nonneg.mpr hv
  have ha : 0 ≤ t-(1-t)*m := by nlinarith [mul_nonneg h1t h1m]
  have hb : 0 ≤ t-(1-t)*(1-m) := by nlinarith [mul_nonneg h1t hm0]
  have hg : 0 ≤ t*(1-t) - (t*x^2+(1-t)*v-(t*x+(1-t)*m)^2) := by
    rw [gap_identity]
    positivity
  linarith

end RiemannResearch.Analysis.HeavyAtomVariance

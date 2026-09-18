import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# The logarithmic derivative at a zero of finite order

An analytic complex function with a zero of finite positive multiplicity has
a logarithmic derivative of meromorphic order -1. The derivative lowers the
analytic order by one, and the quotient subtracts the two orders.

This is the standard local order calculation; the proof is assembled from
Mathlib's analyticOrderAt_deriv_of_pos and meromorphicOrderAt_div.
The RH consumer is RH/ChebyshevMellinRH.
-/

set_option autoImplicit false

theorem AnalyticAt.meromorphicOrderAt_logDeriv_of_zero {f : ℂ → ℂ} {s : ℂ}
    (ha : AnalyticAt ℂ f s) (hfinite : analyticOrderAt f s ≠ ⊤) (hz : f s = 0) :
    meromorphicOrderAt (logDeriv f) s = -1 := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hn0 : n ≠ 0 := by
    intro h
    have hne := ha.analyticOrderAt_ne_zero.mpr hz
    rw [← hn, h] at hne
    exact hne rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hd : analyticOrderAt (deriv f) s = (m : ℕ∞) := by
    apply analyticOrderAt_deriv_of_pos ha
    simpa only [Nat.cast_succ] using hn.symm
  change meromorphicOrderAt (deriv f / f) s = -1
  rw [meromorphicOrderAt_div ha.deriv.meromorphicAt ha.meromorphicAt,
    ha.deriv.meromorphicOrderAt_eq, ha.meromorphicOrderAt_eq, hd, ← hn]
  simp only [ENat.map_natCast]
  change ((m : ℤ) : WithTop ℤ) - ((m.succ : ℤ) : WithTop ℤ) =
    ((-1 : ℤ) : WithTop ℤ)
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
  congr 1
  omega

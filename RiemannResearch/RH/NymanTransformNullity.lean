import RiemannResearch.RH.ArithmeticReturnMellin
import RiemannResearch.RH.NymanReturnRapidDecay
import RiemannResearch.RH.NymanConductorContinuation
import RiemannResearch.RH.PoleCancellationTransform
import RiemannResearch.RH.ArithmeticInverseCompact
import RiemannResearch.Analysis.SuperexponentialLaplace
import Mathlib.Topology.Order.Compact

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual full-return transforms and their zeta/polar nullity

Source: user-provided argument, Theorems 4.1, 5.1, and 9.1 of the Nyman--Weil
note. All transforms here are the actual bilateral Bochner integrals. The
arithmetic factorization is first derived by absolutely convergent Fubini on
Re(s)>1, then continued using proved Poisson decay and holomorphy. Applying
D²−1/4 uses proved real integration by parts, including its boundary control.

These are transform-nullity theorems. Identification with the arithmetic full
Weil form is a separate explicit-formula theorem.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis
open scoped Topology

namespace RiemannResearch.RH

open ZetaConductorRegularization

private theorem compactSupport_of_two_bounds {u : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) : HasCompactSupport u := by
  have hs : tsupport u ⊆ Set.Icc a b := by
    apply closure_minimal _ isClosed_Icc
    intro y hy
    constructor
    · by_contra h
      exact hy (ha y (lt_of_not_ge h))
    · by_contra h
      exact hy (hb y (lt_of_not_ge h))
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hs

/-- The actual full-return transform has the entire regularized zeta factor
at every complex point, including the removable point s=1. -/
theorem centeredTransform_nymanFullReturn (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (s : ℂ) :
    centeredTransform (nymanFullReturn n u) s =
      conductorZeta n s * centeredTransform u s := by
  have hc : HasCompactSupport u := compactSupport_of_two_bounds ha hb
  have hm : HasExponentialMoments u :=
    hasExponentialMoments_of_compactSupport hu.continuous hc
  have hret : ContDiff ℝ (↑(⊤ : ℕ∞)) (nymanFullReturn n u) :=
    arithmeticReturn_contDiff _ hu ha
  have hdec := superexponentialDecay_nymanFullReturn hu ha hb n
  have heq : centeredTransform (nymanFullReturn n u) =
      (fun z => conductorZeta n z * centeredTransform u z) := by
    apply hdec.centeredTransform_eq_of_rightHalfPlane hret.continuous
    · exact (differentiable_conductorZeta n (NeZero.pos n)).mul
        (differentiable_centeredTransform hm)
    · intro z hz
      rw [← nymanConductorLFunction_eq_conductorZeta n]
      exact centeredTransform_nymanFullReturn_of_compactSupport n hu.continuous hc hz
  exact congrFun heq s

/-- The completed full-return channel has exactly the transform claimed in
equation (4.3), with every analytic input supplied by the preceding providers. -/
theorem centeredTransform_poleCancellation_nymanFullReturn (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) (s : ℂ) :
    centeredTransform (poleCancellationOperator (nymanFullReturn n u)) s =
      s * (s - 1) * conductorZeta n s * centeredTransform u s := by
  let R := nymanFullReturn n u
  have hR : ContDiff ℝ (↑(⊤ : ℕ∞)) R := arithmeticReturn_contDiff _ hu ha
  have hR' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv R) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 1 hR
  have hR'' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv R)) := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      ContDiff.iterate_deriv 2 hR
  have hdec : SuperexponentialDecay R := superexponentialDecay_nymanFullReturn hu ha hb n
  have hdec' : SuperexponentialDecay (deriv R) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      superexponentialDecay_iteratedDeriv_nymanFullReturn hu ha hb n 1
  have hdec'' : SuperexponentialDecay (deriv (deriv R)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      superexponentialDecay_iteratedDeriv_nymanFullReturn hu ha hb n 2
  have hL := hdec.centeredTransform_poleCancellationOperator hdec' hdec''
    (hR.differentiable (by simp)) (hR'.differentiable (by simp)) hR''.continuous s
  change centeredTransform (poleCancellationOperator R) s = _
  rw [hL, centeredTransform_nymanFullReturn n hu ha hb s]
  ring

/-- Actual zeta-zero annihilation; no transform identity or nullity is a hypothesis. -/
theorem centeredTransform_poleCancellation_nymanFullReturn_zero (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0)
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s = 0) :
    centeredTransform (poleCancellationOperator (nymanFullReturn n u)) s = 0 := by
  rw [centeredTransform_poleCancellation_nymanFullReturn n hu ha hb s,
    conductorZeta_eq_zero_of_zeta_zero n hs hz, mul_zero, zero_mul]

/-- Both polar moments of the actual full-return channel vanish. -/
theorem centeredTransform_poleCancellation_nymanFullReturn_polar (n : ℕ) [NeZero n]
    {u : ℝ → ℂ} {a b : ℝ}
    (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (ha : ∀ x < a, u x = 0) (hb : ∀ x > b, u x = 0) :
    centeredTransform (poleCancellationOperator (nymanFullReturn n u)) 0 = 0 ∧
      centeredTransform (poleCancellationOperator (nymanFullReturn n u)) 1 = 0 := by
  constructor <;>
    simp [centeredTransform_poleCancellation_nymanFullReturn n hu ha hb]

/-- The exact arithmetic completion from §9 has the genuine entire zeta factor. -/
theorem centeredTransform_nymanCompletedTest (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) (s : ℂ) :
    centeredTransform (nymanCompletedTest n M hn v) s =
      s * (s - 1) * conductorZeta n s *
        centeredTransform (nymanInversePotential n M hn v) s := by
  letI : NeZero n := ⟨by omega⟩
  exact centeredTransform_poleCancellation_nymanFullReturn n
    (nymanInversePotential_contDiff n M hn hv)
    (fun y hy => nymanInversePotential_zero_below n M hn ha hy)
    (fun y hy => nymanInversePotential_zero_above n M hn hb hy) s

/-- The actual completed test, not an assumed spectral model, annihilates every
zeta zero away from the pole. -/
theorem centeredTransform_nymanCompletedTest_zero (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s = 0) :
    centeredTransform (nymanCompletedTest n M hn v) s = 0 := by
  rw [centeredTransform_nymanCompletedTest n M hn hv ha hb s,
    conductorZeta_eq_zero_of_zeta_zero n hs hz, mul_zero, zero_mul]

theorem centeredTransform_nymanCompletedTest_polar (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    centeredTransform (nymanCompletedTest n M hn v) 0 = 0 ∧
      centeredTransform (nymanCompletedTest n M hn v) 1 = 0 := by
  constructor <;> simp [centeredTransform_nymanCompletedTest n M hn hv ha hb]

end RiemannResearch.RH

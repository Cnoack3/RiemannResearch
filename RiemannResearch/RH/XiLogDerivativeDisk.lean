/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.RationalZeroFreeDisks
import RiemannResearch.RH.ChebyshevMellinRH
import RiemannResearch.RH.WeilExplicitFormula.XiPrime.ExplicitFormula.ZeroFree

/-!
# Analytic disks for the actual completed logarithmic derivative

The real-valued defining inequality is the squared Euclidean distance to
1+iq. The completed logarithmic derivative has an order-minus-one pole at
each xi zero regardless of multiplicity. Thus its disk of holomorphy is
exactly the disk test for nontrivial zeta zeros.
-/

noncomputable section
open Set Zeta23 Zeta23.XiPrime
namespace RiemannResearch.RH.RationalZeroFreeDisks

theorem xi_logDerivative_analyticAt_iff (z : ℂ) :
    AnalyticAt ℂ (logDeriv xi) z ↔ ¬ IsNontrivialZero z := by
  have han := xi_analyticAt z
  have htop : analyticOrderAt xi z ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    have hall : EqOn xi 0 univ :=
      (show AnalyticOnNhd ℂ xi univ from fun w _ => xi_analyticAt w).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ z) h
    have hzero := hall (mem_univ (1:ℂ))
    rw [xi_one] at hzero
    norm_num at hzero
  constructor
  · intro h hz
    have horder := han.meromorphicOrderAt_logDeriv_of_zero htop ((ZeroFree.xi_eq_zero_iff z).mpr hz)
    have hh := h.meromorphicOrderAt_nonneg
    rw [horder] at hh
    exact (show ¬(0 : WithTop ℤ) ≤ -1 by decide) hh
  · intro h
    have hn : xi z ≠ 0 := fun he => h ((ZeroFree.xi_eq_zero_iff z).mp he)
    exact han.deriv.div han hn

def rationalOpenDisk (q : ℚ) (r : ℝ) : Set ℂ :=
  {z | (1-z.re)^2 + ((q:ℝ)-z.im)^2 < r^2}

/-- Diskwise analyticity of ξ′/ξ agrees with the countable geometric
condition at every radius, including the radius zero. -/
theorem xi_logDerivative_disks_iff (r : ℝ) :
    (∀ q : ℚ, AnalyticOnNhd ℂ (logDeriv xi) (rationalOpenDisk q r)) ↔ RationalDiskBound r := by
  constructor
  · intro h q z hz
    by_contra! hlt
    exact ((xi_logDerivative_analyticAt_iff z).mp (h q z hlt)) hz
  · intro h q z hz
    apply (xi_logDerivative_analyticAt_iff z).mpr
    intro hzero
    exact (not_lt_of_ge (h q z hzero)) hz

theorem riemannHypothesis_iff_xi_logDerivative_disks :
    RiemannHypothesis ↔
      ∀ q : ℚ, AnalyticOnNhd ℂ (logDeriv xi) (rationalOpenDisk q (1/2)) :=
  riemannHypothesis_iff_half_disks.trans (xi_logDerivative_disks_iff _).symm

end RiemannResearch.RH.RationalZeroFreeDisks

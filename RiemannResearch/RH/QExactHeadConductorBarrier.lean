/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QExactHeadEpsilonBounds
import RiemannResearch.RH.BurnolParetoTransfer
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Conductor cost of the exact-head dyadic energy budget

Source: research with the user, 29 October 2026. The lower-bound input is
J.-F. Burnol, "A lower bound in an approximation problem involving the
zeros of the Riemann zeta function", Theorem 1.3,
https://arxiv.org/pdf/math/0103058.

The exact complete-energy transfer is unconditional. The conductor barrier
explicitly assumes ContinuousCutoffLowerBound; the published analytic
theorem supplying that hypothesis is not formalized here. No all-stage
witness provider or RH conclusion is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QExactHeadConductorBarrier
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QExactHeadEpsilonBounds
open Pareto.BaezDuarte Pareto.BurnolTransfer

theorem finite_error_transfer_identity (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    ‖Pareto.hilbertOne - finiteResidueSum s a‖ ^ 2 =
      zetaTwo * ‖qOne - ∑ d ∈ s, a d • qResidue d‖ ^ 2 -
      zetaTwo * normCorrection (qOne - ∑ d ∈ s, a d • qResidue d) := by
  have he : toPareto (qOne - ∑ d ∈ s, a d • qResidue d) =
      Pareto.hilbertOne - finiteResidueSum s a := by
    change toParetoLinear (qOne - ∑ d ∈ s, a d • qResidue d) = _
    rw [map_sub]
    change toPareto qOne - toPareto (∑ d ∈ s, a d • qResidue d) = _
    rw [toPareto_qOne, toPareto_finiteResidueSum s a hs]
  simpa only [he] using toPareto_norm_sq_exact (qOne - ∑ d ∈ s, a d • qResidue d)

theorem finite_error_lower_transfer (N : ℕ) (hN : 1 ≤ N) (L : ℝ)
    (h : ContinuousCutoffLowerBound N L) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N) :
    L ≤ zetaTwo * ‖qOne - ∑ d ∈ s, a d • qResidue d‖ ^ 2 := by
  have hl := finite_error_lower_of_continuous N hN L h s a hs
  have he : toPareto (qOne - ∑ d ∈ s, a d • qResidue d) =
      Pareto.hilbertOne - finiteResidueSum s a := by
    change toParetoLinear (qOne - ∑ d ∈ s, a d • qResidue d) = _
    rw [map_sub]
    change toPareto qOne - toPareto (∑ d ∈ s, a d • qResidue d) = _
    rw [toPareto_qOne, toPareto_finiteResidueSum s a (fun d hd => (hs d hd).1)]
  have hu := toPareto_norm_sq_le (qOne - ∑ d ∈ s, a d • qResidue d)
  rw [he] at hu
  exact hl.trans hu

/-- Complete error estimate, with no bound on individual coefficients. -/
theorem scaled_error_le_of_head_energy (H : ℕ) (hH : 0 < H) (f : QHilbert)
    (hh : ∀ k, 0 < k → k ≤ H → qSequence f k = 1)
    (he : ‖f‖ ^ 2 ≤ 1 + 5 / (8 * (H : ℝ))) :
    zetaTwo * ‖qOne - f‖ ^ 2 ≤ ((5 / 4 : ℝ) * zetaTwo + 4) / (H : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have ht : zetaTwo * targetTail H ≤ 1 / (H : ℝ) := by
    calc
      _ ≤ zetaTwo * (1 / (zetaTwo * (H : ℝ))) :=
        mul_le_mul_of_nonneg_left (targetTail_le H hH) zetaTwo_pos.le
      _ = _ := by field_simp [ne_of_gt zetaTwo_pos]
  have hb := mul_le_mul_of_nonneg_left
    (error_sq_le_head_energy H f hh) zetaTwo_pos.le
  have henergy := mul_le_mul_of_nonneg_left he zetaTwo_pos.le
  have halg : zetaTwo * (2 * (5 / (8 * (H : ℝ)))) + 4 / (H : ℝ) =
      ((5 / 4 : ℝ) * zetaTwo + 4) / (H : ℝ) := by ring
  rw [← halg]
  norm_num [div_eq_mul_inv, mul_inv_rev] at ht hb henergy ⊢
  nlinarith only [hb, henergy, ht]

/-- Conditional on the analytic cutoff bound, the logarithm of the largest
allowed conductor must pay a cost proportional to the exact head. -/
theorem log_conductor_lower (H N : ℕ) (hH : 0 < H) (hN : 2 ≤ N)
    (c : ℝ) (hburnol : ContinuousCutoffLowerBound N (c / Real.log N))
    (s : Finset ℕ) (a : ℕ → ℝ) (hs : ∀ d ∈ s, 0 < d ∧ d ≤ N)
    (hh : ∀ k, 0 < k → k ≤ H →
      qSequence (∑ d ∈ s, a d • qResidue d) k = 1)
    (he : ‖∑ d ∈ s, a d • qResidue d‖ ^ 2 ≤ 1 + 5 / (8 * (H : ℝ))) :
    c * (H : ℝ) ≤ ((5 / 4 : ℝ) * zetaTwo + 4) * Real.log N := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hl := finite_error_lower_transfer N (by omega) _ hburnol s a hs
  have hu := scaled_error_le_of_head_energy H hH (∑ d ∈ s, a d • qResidue d) hh he
  exact (div_le_div_iff₀ (Real.log_pos hNR) hHR).mp (hl.trans hu)


/-- The logarithmic lower envelope rules out subexponential conductor growth.
The external analytic envelope is an explicit hypothesis, not an axiom. -/
theorem no_subexponential_family
    (c : ℝ) (hc : 0 < c) (K : ℕ)
    (hburnol : ∀ N : ℕ, K ≤ N → 2 ≤ N →
      ContinuousCutoffLowerBound N (c / Real.log N))
    (H N : ℕ → ℕ) (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (hH : ∀ j, 0 < H j) (hN : ∀ j, 2 ≤ N j)
    (hlarge : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hs : ∀ j d, d ∈ s j → 0 < d ∧ d ≤ N j)
    (hh : ∀ j k, 0 < k → k ≤ H j →
      qSequence (∑ d ∈ s j, a j d • qResidue d) k = 1)
    (he : ∀ j, ‖∑ d ∈ s j, a j d • qResidue d‖ ^ 2 ≤
      1 + 5 / (8 * (H j : ℝ)))
    (hsmall : Filter.Tendsto (fun j => Real.log (N j) / (H j : ℝ))
      Filter.atTop (nhds 0)) : False := by
  have hthreshold : ∀ᶠ j in Filter.atTop, K ≤ N j :=
    hlarge.eventually (Filter.eventually_ge_atTop K)
  have hb : ∀ᶠ j in Filter.atTop, c ≤
      ((5 / 4 : ℝ) * zetaTwo + 4) * (Real.log (N j) / (H j : ℝ)) := by
    filter_upwards [hthreshold] with j hj
    have hHR : (0 : ℝ) < H j := by exact_mod_cast hH j
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hHR).mpr
      (log_conductor_lower (H j) (N j) (hH j) (hN j) c
        (hburnol (N j) hj (hN j)) (s j) (a j) (hs j) (hh j) (he j))
  have ht : Filter.Tendsto
      (fun j => ((5 / 4 : ℝ) * zetaTwo + 4) * (Real.log (N j) / (H j : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hsmall.const_mul ((5 / 4 : ℝ) * zetaTwo + 4)
  exact (not_le_of_gt hc) (ge_of_tendsto ht hb)

end RiemannResearch.RH.QExactHeadConductorBarrier

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete Q-energy obstruction for growing exact heads

Source: user-provided `Squarefree_Infinite_CRT_Continuation_2026-10-16`,
Sections 7--8, for the statements and zero-witness strategy. The analytic
Mellin witness is the existing `legal_exact_head_residual_power_lower`.
The full Q/P comparison preserves every physical coordinate and full tail.

The subpolynomial energy provider remains Open. This module proves a
conditional research reduction to the actual RiemannHypothesis proposition;
it does not assume or formalize the external RH-to-squarefree-density theorem.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QExactHeadSubpolynomial
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open Pareto Pareto.CoefficientStabilization
open RiemannResearch.Analysis.SubpolynomialWindow

/-- Every finite squarefree Q trial maps into the actual Pareto legal closure. -/
theorem toPareto_mem_legalClosure {f : QHilbert}
    (hf : f ∈ qSquarefreeCRTSpan) :
    toPareto f ∈ hilbertLegalClosure {n : ℕ | 0 < n} := by
  have hm : qSquarefreeCRTSpan ≤ closedSpace.comap toParetoCLM.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    change toPareto (qResidue d.val) ∈ closedSpace
    rw [toPareto_qResidue d.val (by have := d.property.1; omega)]
    apply (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨d.val - 2, ?_⟩
    have he : d.val - 2 + 2 = d.val := Nat.sub_add_cancel d.property.1
    simp [residueAtom, BaezDuarte.residueVector, he,
      show 0 < d.val by have := d.property.1; omega]
  exact closedSpace_le_legalClosure (hm hf)

/-- Complete residual norm transfer; no finite physical truncation occurs. -/
theorem residual_toPareto_norm_sq_le (f : QHilbert) :
    ‖hilbertOne - toPareto f‖ ^ 2 ≤ zetaTwo * ‖qOne - f‖ ^ 2 := by
  have he : toPareto (qOne - f) = hilbertOne - toPareto f := by
    change toParetoLinear (qOne - f) = _
    rw [map_sub]
    exact congrArg (· - toPareto f) toPareto_qOne
  simpa only [he] using toPareto_norm_sq_le (qOne - f)

/-- The complete infinite physical error before applying a power estimate. -/
theorem residual_energy_exact (f : QHilbert) :
    ‖qOne - f‖ ^ 2 = ∑' k,
      positiveQWeight k * (qOneSequence k - qSequence f k) ^ 2 := by
  rw [qNorm_weighted_sq]
  congr 1
  funext k
  change positiveQWeight k * (qSequenceLinear (qOne - f) k) ^ 2 = _
  rw [map_sub]
  change positiveQWeight k * (qSequence qOne k - qSequence f k) ^ 2 = _
  rw [qSequence_qOne]

/-- A hypothetical right-half-plane zero forces a positive power of the head
in the complete Q error. Here the exact head consists of 1 ≤ k < n. -/
theorem exact_head_residual_power_lower
    {f : QHilbert} (hf : f ∈ qSquarefreeCRTSpan)
    (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n → qSequence f k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2)) *
      (n : ℝ) ^ (2 * s.re - 1) ≤ ‖qOne - f‖ ^ 2 := by
  have hp := legal_exact_head_residual_power_lower {n : ℕ | 0 < n}
    (fun _ h => h) (toPareto_mem_legalClosure hf) n hn
    (by intro k hk hkn; simpa only [toPareto_sequence] using hhead k hk hkn)
    s hs hs1 hz
  have h := hp.trans (residual_toPareto_norm_sq_le f)
  have hd := (div_le_iff₀ zetaTwo_pos).mpr (by simpa only [mul_comm zetaTwo] using h)
  calc
    _ = ((2 * s.re - 1) / ‖s‖ ^ 2 * (n : ℝ) ^ (2 * s.re - 1)) / zetaTwo := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := hd

/-- Conditional research reduction: cofinal exact squarefree legal heads and
subpolynomial complete Q energy imply RH. The energy estimate is an input. -/
theorem riemannHypothesis_of_cofinal_exact_head_subpolynomial
    (F : ℕ → QHilbert) (n : ℕ → ℕ) (E : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hlegal : ∀ i, F i ∈ qSquarefreeCRTSpan)
    (hhead : ∀ i k, 0 < k → k < n i → qSequence (F i) k = 1)
    (hE : ∀ i, 0 ≤ E i)
    (hbound : ∀ i, ‖qOne - F i‖ ^ 2 ≤ E i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + E i) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < (2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2) :=
    div_pos (by linarith) (mul_pos zetaTwo_pos (pow_pos (norm_pos_iff.mpr hs0) 2))
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hfloor : ∀ᶠ i : ℕ in atTop,
      ((2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2)) *
        (n i : ℝ) ^ (2 * s.re - 1) ≤ E i + 1 := by
    filter_upwards [hn1] with i hi
    exact (exact_head_residual_power_lower (hlegal i) (n i)
      (by exact_mod_cast hi) (hhead i) s hs hs1 hz).trans (hbound i)
  exact no_positive_power_floor (fun i => (n i : ℝ)) E 1
    ((2 * s.re - 1) / (zetaTwo * ‖s‖ ^ 2)) (2 * s.re - 1)
    hn hE (by norm_num) hc ha hsub hfloor

/-- The continuation's energy provider specialized to the existing exhaustive
affine optimizer. All signed Gram terms are retained in minimumError.
Subpolynomial growth of these actual minima is the remaining Open premise. -/
theorem riemannHypothesis_of_subpolynomial_affine_minima
    (L r : ℕ → ℕ) (hL : ∀ N, 0 < L N) (hsf : ∀ N, Squarefree (L N))
    (hr : ∀ N, r N ∈ QSquarefreeAffineHead.conductors (L N))
    (hrH : ∀ N, N + 1 < r N)
    (hsmall : ∀ N d, 1 < d → d ≤ N + 1 → Squarefree d → d ∣ L N)
    (hsub : Tendsto (fun N => Real.log
      (1 + QSquarefreeAffineHead.minimumError (N + 1) (L N) (r N) (hr N)) /
        Real.log ((N + 2 : ℕ) : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  let F : ℕ → QHilbert := fun N =>
    QSquarefreeAffineHead.optimizer (N + 1) (L N) (r N) (hr N)
  let E : ℕ → ℝ := fun N =>
    QSquarefreeAffineHead.minimumError (N + 1) (L N) (r N) (hr N)
  have hf (N : ℕ) := QSquarefreeAffineHead.optimizer_feasible
    (N + 1) (L N) (r N) (Nat.succ_pos N) (hL N) (hr N) (hrH N) (hsmall N)
  have hl (N : ℕ) : F N ∈ qSquarefreeCRTSpan :=
    QSquarefreeLatticePackets.divisorStage_le_squarefreeSpan
      (L N) (hL N) (hsf N) (hf N).1
  apply riemannHypothesis_of_cofinal_exact_head_subpolynomial F (fun N => N + 2) E
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)) hl
  · intro N k hk hkN
    exact (hf N).2 k hk (by omega)
  · intro N
    exact sq_nonneg _
  · intro N
    change E N ≤ E N + 1
    linarith
  · exact hsub

end RiemannResearch.RH.QExactHeadSubpolynomial

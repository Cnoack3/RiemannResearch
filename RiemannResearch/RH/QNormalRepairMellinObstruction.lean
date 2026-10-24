/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeHeadRepair
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.Analysis.FiniteHilbertGramProjection

/-!
# The actual Mellin obstruction to target normal repair cost

Source: constructive-approximants continuation agenda, 24 October 2026.
The normal equations may have dependent observation rows. The signed target
cost is kept intact, and the exact positive Q/P metric correction is retained.
The analytic obstruction is the already proved physical Mellin transform of
actual positive-conductor residues; it is not an assumed detector provider.

These are obstruction theorems conditional on an off-critical-line zeta zero.
No such zero, uniform arithmetic upper bound, or proof of RH is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QNormalRepairMellinObstruction

open Analysis.FiniteHilbertGram Analysis.FiniteConstrainedProjection
open Analysis.FiniteFeasibleGramRepair
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QCovarianceInverse QMellinTransfer QSquarefreeHeadRepair

/-- The sharp physical head cutoff survives the exact Q/P metric transfer. -/
theorem exact_head_error_power_lower_with_correction
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (hD : ∀ i, 0 < D i) (c : ι → ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n → qSequence (qSynthesis D c) k = 1)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) * (n : ℝ) ^ (2 * s.re - 1) +
        metricCorrection (qOne - qSynthesis D c) ≤
      zetaTwo * ‖qOne - qSynthesis D c‖ ^ 2 := by
  have hehead : ∀ k, 0 < k → k < n →
      hilbertSequence (toPareto (qOne - qSynthesis D c)) k = 0 := by
    intro k hk hkn
    rw [toPareto_sequence]
    change qSequenceLinear (qOne - qSynthesis D c) k = 0
    rw [map_sub]
    change qSequence qOne k - qSequence (qSynthesis D c) k = 0
    rw [qSequence_qOne, hhead k hk hkn]
    simp [qOneSequence, Nat.ne_of_gt hk]
  have h := mellin_zero_head_lower (toPareto (qOne - qSynthesis D c)) n hn
    hehead s hs
  change (2 * s.re - 1) * ‖qMellin (qOne - qSynthesis D c) s‖ ^ 2 *
    (n : ℝ) ^ (2 * s.re - 1) ≤ ‖toPareto (qOne - qSynthesis D c)‖ ^ 2 at h
  rw [qMellin_error_at_zero D hD c s hs hs1 hz,
    norm_div, norm_one, div_pow, one_pow] at h
  have hp : ((2 * s.re - 1) / ‖s‖ ^ 2) * (n : ℝ) ^ (2 * s.re - 1) ≤
      ‖toPareto (qOne - qSynthesis D c)‖ ^ 2 := by
    convert h using 1; ring
  have hm := norm_identity (qOne - qSynthesis D c)
  linarith only [hp, hm]

def repair {ι : Type*} [Fintype ι] (D : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (d : Fin M → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (fun i => qResidue (D i)) (inverseCoeff hv qOne) +
    Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d

def normalCost {ι : Type*} [Fintype ι] (D : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (d : Fin M → ℝ) : ℝ :=
  ∑ i, d i * headMismatch hv (headObservation M) qOne i

theorem repair_eq_synthesis {ι : Type*} [Fintype ι] (D : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (d : Fin M → ℝ) :
    ∃ c : ι → ℝ, qSynthesis D c = repair D hv M d := by
  have hm : repair D hv M d ∈ synthesisSpan (fun i => qResidue (D i)) := by
    apply Submodule.add_mem
    · exact synthesis_mem _ _
    · rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (synthesis_mem _ _)
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, by simpa only [qSynthesis, Fintype.linearCombination_apply] using hc⟩

/-- The exact signed target normal cost, including the full metric correction,
has a power obstruction at every zero with real part strictly above one half. -/
theorem normal_repair_power_lower_with_correction
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (hD : ∀ i, 0 < D i)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (d : Fin M → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv (headObservation M) i)
      (Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d) =
        headMismatch hv (headObservation M) qOne i)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) * ((M + 1 : ℕ) : ℝ) ^ (2 * s.re - 1) +
        metricCorrection (qOne - repair D hv M d) ≤
      zetaTwo * (‖projectionResidual hv qOne‖ ^ 2 + normalCost D hv M d) := by
  obtain ⟨c, hc⟩ := repair_eq_synthesis D hv M d
  have hhead : ∀ k, 0 < k → k < M + 1 → qSequence (qSynthesis D c) k = 1 := by
    intro k hk hkm
    let i : Fin M := ⟨k - 1, by omega⟩
    have he := repaired_observation hv (headObservation M) qOne d hn i
    change inner ℝ (headObservation M i) (repair D hv M d) = _ at he
    rw [headObservation_inner, headObservation_inner] at he
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [hi, qSequence_qOne] at he
    rw [hc]
    simpa [qOneSequence, Nat.ne_of_gt hk] using he
  have hp := exact_head_error_power_lower_with_correction D hD c (M + 1)
    (by omega) hhead s hs hs1 hz
  rw [hc] at hp
  have he := repaired_error_identity hv (headObservation M) qOne d hn
  change ‖qOne - repair D hv M d‖ ^ 2 =
    ‖projectionResidual hv qOne‖ ^ 2 + normalCost D hv M d at he
  rwa [he] at hp

/-- In particular, an off-line zero forces the target normal repair cost to
grow at least at this explicit positive power of the physical head length. -/
theorem normal_repair_cost_power_lower
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (hD : ∀ i, 0 < D i)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (d : Fin M → ℝ)
    (hn : ∀ i, inner ℝ (projectedRow hv (headObservation M) i)
      (Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d) =
        headMismatch hv (headObservation M) qOne i)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (((2 * s.re - 1) / ‖s‖ ^ 2) * ((M + 1 : ℕ) : ℝ) ^ (2 * s.re - 1)) /
        zetaTwo - 1 ≤ normalCost D hv M d := by
  have hp := normal_repair_power_lower_with_correction D hD hv M d hn s hs hs1 hz
  have hc := metricCorrection_nonneg (qOne - repair D hv M d)
  have hd := projection_residual_sq_le_one hv
  have hfloor : ((2 * s.re - 1) / ‖s‖ ^ 2) *
      ((M + 1 : ℕ) : ℝ) ^ (2 * s.re - 1) ≤
      zetaTwo * (1 + normalCost D hv M d) := by
    nlinarith only [hp, hc, hd, zetaTwo_pos]
  have hh := (div_le_iff₀ zetaTwo_pos).mpr
    (hfloor.trans_eq (mul_comm zetaTwo (1 + normalCost D hv M d)))
  linarith only [hh]

/-- Any bound in the agenda's rank-free target directional inequality must
pay the same power cost. Its feasibility is supplied by duality itself. -/
theorem directional_budget_power_lower
    {ι : Type*} [Fintype ι] (D : ι → ℕ) (hD : ∀ i, 0 < D i)
    (hv : LinearIndependent ℝ (fun i => qResidue (D i)))
    (M : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdual : ∀ c : Fin M → ℝ,
      (∑ i, c i * headMismatch hv (headObservation M) qOne i) ^ 2 ≤
        B * ‖Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) c‖ ^ 2)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (((2 * s.re - 1) / ‖s‖ ^ 2) * ((M + 1 : ℕ) : ℝ) ^ (2 * s.re - 1)) /
        zetaTwo - 1 ≤ B := by
  obtain ⟨d, hn, hd⟩ :=
    (bounded_normal_iff_directional (projectedRow hv (headObservation M))
      (headMismatch hv (headObservation M) qOne) B hB).mpr hdual
  have hp := normal_repair_cost_power_lower D hD hv M d hn s hs hs1 hz
  have he := normal_energy (projectedRow hv (headObservation M))
    (headMismatch hv (headObservation M) qOne) d hn
  change ‖Fintype.linearCombination ℝ (projectedRow hv (headObservation M)) d‖ ^ 2 =
    normalCost D hv M d at he
  exact hp.trans (by rwa [← he])

end RiemannResearch.RH.QNormalRepairMellinObstruction

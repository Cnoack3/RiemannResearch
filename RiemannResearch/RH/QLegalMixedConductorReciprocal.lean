/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorAsymptotics
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual reciprocal-energy convergence and a positive correction coefficient

Source: LegalSubspaceProjectionObstruction.md. All sequences here are the
actual Hilbert-space vectors of the mixed-conductor family with its actual
residual forcing. No coefficient inequality is assumed as a provider.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal

def lowPart (d : ℕ) : QHilbert :=
  qResidue 3 - parityCoefficient d • parityAtom

theorem orthogonalVector_eq_low_add_high (d : ℕ) :
    orthogonalVector d = lowPart d + highPart d := by
  unfold orthogonalVector mixedVector lowPart
  abel

/-- Exact quadratic expansion, retaining both mixed contributions. -/
theorem reciprocalMoment_expansion (d : ℕ) :
    reciprocalMoment d = inner ℝ (lowPart d) (B (lowPart d)) +
      2 * inner ℝ (lowPart d) (B (highPart d)) +
      inner ℝ (highPart d) (B (highPart d)) := by
  have hc : inner ℝ (highPart d) (B (lowPart d)) =
      inner ℝ (lowPart d) (B (highPart d)) := by
    rw [← B_symmetric, real_inner_comm]
  rw [reciprocalMoment, orthogonalVector_eq_low_add_high, map_add,
    inner_add_left, inner_add_right, inner_add_right, hc]
  ring

theorem lowPart_tendsto :
    Tendsto lowPart atTop (𝓝 fixedOrthogonalVector) := by
  exact tendsto_const_nhds.sub (parityCoefficient_tendsto.smul tendsto_const_nhds)

theorem B_highPart_tendsto_zero :
    Tendsto (fun d : ℕ => B (highPart d)) atTop (𝓝 0) := by
  have hn : Tendsto (fun d : ℕ => B (normalizedConductor d)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr B_normalizedConductor_norm_tendsto_zero
  have hs : Tendsto (fun d : ℕ => (10 : ℝ) • B (normalizedConductor d))
      atTop (𝓝 ((10 : ℝ) • (0 : QHilbert))) := tendsto_const_nhds.smul hn
  simpa only [highPart_eq, map_smul, smul_zero] using hs

theorem highPart_reciprocal_energy_tendsto_zero :
    Tendsto (fun d : ℕ => inner ℝ (highPart d) (B (highPart d)))
      atTop (𝓝 0) := by
  simpa only [highPart_eq, map_smul, real_inner_smul_left,
    real_inner_smul_right, mul_zero] using
      (normalizedConductor_reciprocal_energy_tendsto_zero.const_mul 10).const_mul 10

/-- Complete reciprocal energy converges even though the high part has a
nonvanishing ordinary norm. -/
theorem reciprocalMoment_tendsto :
    Tendsto reciprocalMoment atTop
      (𝓝 (inner ℝ fixedOrthogonalVector (B fixedOrthogonalVector))) := by
  have hBl : Tendsto (fun d => B (lowPart d)) atTop
      (𝓝 (B fixedOrthogonalVector)) :=
    (B.continuous.tendsto fixedOrthogonalVector).comp lowPart_tendsto
  have hcross : Tendsto (fun d => inner ℝ (lowPart d) (B (highPart d)))
      atTop (𝓝 (inner ℝ fixedOrthogonalVector (0 : QHilbert))) :=
    lowPart_tendsto.inner B_highPart_tendsto_zero
  have hlow : Tendsto (fun d => inner ℝ (lowPart d) (B (lowPart d)))
      atTop (𝓝 (inner ℝ fixedOrthogonalVector (B fixedOrthogonalVector))) :=
    lowPart_tendsto.inner hBl
  have htotal := (hlow.add (hcross.const_mul 2)).add
    highPart_reciprocal_energy_tendsto_zero
  change Tendsto (fun d => reciprocalMoment d) atTop
    (𝓝 (inner ℝ fixedOrthogonalVector (B fixedOrthogonalVector)))
  simpa only [reciprocalMoment_expansion, inner_zero_right, mul_zero, add_zero]
    using htotal

theorem fixedOrthogonalVector_reciprocal_energy_le :
    inner ℝ fixedOrthogonalVector (B fixedOrthogonalVector) ≤ 4 / 9 := by
  calc
    _ ≤ ‖fixedOrthogonalVector‖ * ‖B fixedOrthogonalVector‖ := real_inner_le_norm _ _
    _ ≤ ‖fixedOrthogonalVector‖ * ‖fixedOrthogonalVector‖ :=
      mul_le_mul_of_nonneg_left (B_norm_le _) (norm_nonneg _)
    _ = ‖fixedOrthogonalVector‖ ^ 2 := by ring
    _ ≤ _ := fixedOrthogonalVector_norm_sq_le

theorem reciprocalMoment_upper_eventually :
    ∀ᶠ d : ℕ in atTop, reciprocalMoment d ≤ 1 := by
  have he : inner ℝ fixedOrthogonalVector (B fixedOrthogonalVector) < 1 := by
    linarith [fixedOrthogonalVector_reciprocal_energy_le]
  exact (reciprocalMoment_tendsto.eventually (gt_mem_nhds he)).mono (fun _ h => h.le)

theorem sourceMoment_uniform_lower (d : ℕ) : 1 / 36 ≤ sourceMoment d := by
  calc
    _ ≤ 1 / (18 * zetaTwo) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 36)
        (mul_pos (by norm_num) zetaTwo_pos)).mpr
      nlinarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.2]
    _ ≤ _ := sourceMoment_lower d

/-- The coefficient lower bound now has actual, unconditional providers. -/
theorem correctionCoefficient_lower_eventually :
    ∀ᶠ d : ℕ in atTop,
      7 / (36 * 303 ^ 2 : ℝ) ≤ correctionCoefficient d := by
  filter_upwards [gram_bounds_eventually, targetMoment_upper_eventually,
    reciprocalMoment_upper_eventually] with d hG ha hE
  exact actualCorrection_coefficient_lower d hG.1 hG.2
    (targetMoment_nonneg d) ha (sourceMoment_uniform_lower d) hE

end RiemannResearch.RH.QLegalMixedConductor

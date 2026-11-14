/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinContour
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
/-!
# Actual residues of the Conrey--Baluyot Mellin kernel

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*
(2017), Lemma 3.1.1, equation (3.1.3), pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The residues at 0 and 1 - 2 sigma are computed from Mathlib's residue
of zeta at 1. Both the punctured-neighborhood limits and their values
in the repository's rectangle-residue API are proved. The second
coefficient is real and is retained with its sign.

These local results alone do not prove a contour shift or normalization.
The actual integrable negative contour, signed shift and nonzero normalizing
weight are proved in the sibling NegativeContour, Shift and Normalization modules.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem zeta_shifted_residue (c : ℂ) :
    Tendsto (fun z : ℂ => (z - (1 - c)) * riemannZeta (c + z))
      (𝓝[≠] (1 - c)) (𝓝 1) := by
  have hs : Tendsto (fun z : ℂ => c + z) (𝓝[≠] (1 - c)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun z : ℂ => c + z) (1 - c) := by fun_prop
      simpa using hc.continuousWithinAt.tendsto
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change c + z ≠ 1
      change z ≠ 1 - c at hz
      intro he
      apply hz
      calc z = (c + z) - c := by ring
           _ = 1 - c := by rw [he]
  have hh := riemannZeta_residue_one.comp hs
  convert hh using 1
  funext z
  congr 1
  ring

/-- The actual residue at zero is 1; the nonzero normalizing zeta value is proved. -/
theorem mellinKernel_residue_zero {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) :
    Tendsto (fun z : ℂ => z * mellinKernel σ ξ z) (𝓝[≠] 0) (𝓝 1) := by
  have hne : riemannZeta (2 * σ : ℝ) ≠ 0 := by
    have hh := one_le_norm_riemannZeta_real (show 1 < 2 * σ by linarith)
    intro he
    rw [he, norm_zero] at hh
    norm_num at hh
  have hs : Tendsto (fun z : ℂ => z * riemannZeta (1 + z))
      (𝓝[≠] 0) (𝓝 1) := by simpa using zeta_shifted_residue 1
  have hg : ContinuousAt (fun z : ℂ => Gamma (z + 1)) 0 := by
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (continuousAt_id.add continuousAt_const)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hl : ContinuousAt (fun z : ℂ => riemannZeta ((2 * σ : ℝ) + z)) 0 := by
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hnξ : NeZero (ξ : ℂ) := ⟨by exact_mod_cast hξ.ne'⟩
  have hp : ContinuousAt (fun z : ℂ => (ξ : ℂ) ^ z) 0 :=
    (continuous_const_cpow (ξ : ℂ)).continuousAt
  have hh := (((hg.continuousWithinAt.tendsto.mul
    (hl.div_const (riemannZeta (2 * σ : ℝ))).continuousWithinAt.tendsto).mul hs).mul hp.continuousWithinAt.tendsto)
  have hm : Tendsto
      (fun z : ℂ => Gamma (z + 1) *
        (riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)) *
        (z * riemannZeta (1 + z)) * (ξ : ℂ) ^ z) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [zero_add, add_zero, Complex.Gamma_one, Complex.cpow_zero,
      div_self hne, one_mul, mul_one] using hh
  exact hm.congr' (Eventually.of_forall fun z => by dsimp [mellinKernel]; ring)

/-- The signed coefficient in Baluyot (2017), equation (3.1.3). -/
def secondaryResidueCoefficient (σ : ℝ) : ℂ :=
  Gamma ((2 : ℂ) - (2 * σ : ℝ)) * riemannZeta ((2 : ℂ) - (2 * σ : ℝ)) /
    riemannZeta (2 * σ : ℝ)

/-- The secondary coefficient is real; its sign is retained in the residue formula. -/
theorem secondaryResidueCoefficient_im_eq_zero (σ : ℝ) :
    (secondaryResidueCoefficient σ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simp only [secondaryResidueCoefficient, map_mul, map_div₀, ← Complex.Gamma_conj,
    ← riemannZeta_conj, map_sub, ← Complex.ofReal_ofNat, Complex.conj_ofReal]

/-- The actual second residue, including its coefficient and complex power. -/
theorem mellinKernel_residue_secondary {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hξ : 0 < ξ) :
    Tendsto (fun z : ℂ => (z - ((1 : ℂ) - (2 * σ : ℝ))) * mellinKernel σ ξ z)
      (𝓝[≠] ((1 : ℂ) - (2 * σ : ℝ)))
      (𝓝 (secondaryResidueCoefficient σ * (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)))) := by
  let p : ℂ := (1 : ℂ) - (2 * σ : ℝ)
  have hg : ContinuousAt (fun z : ℂ => Gamma (z + 1)) p := by
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (continuousAt_id.add continuousAt_const)
    intro n hn
    have he := congrArg Complex.re hn
    simp [p] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hr : ContinuousAt (fun z : ℂ => riemannZeta (1 + z)) p := by
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      (continuousAt_const.add continuousAt_id)
    intro he
    have hh := congrArg Complex.re he
    simp [p] at hh
    linarith
  have hnξ : NeZero (ξ : ℂ) := ⟨by exact_mod_cast hξ.ne'⟩
  have hp : ContinuousAt (fun z : ℂ => (ξ : ℂ) ^ z) p :=
    (continuous_const_cpow (ξ : ℂ)).continuousAt
  have hs := zeta_shifted_residue (2 * σ : ℝ)
  have hh := (((hg.continuousWithinAt.tendsto.mul
    (hs.div_const (riemannZeta (2 * σ : ℝ)))).mul
      hr.continuousWithinAt.tendsto).mul hp.continuousWithinAt.tendsto)
  have harg1 : p + 1 = (2 : ℂ) - (2 * σ : ℝ) := by dsimp [p]; ring
  have harg2 : 1 + p = (2 : ℂ) - (2 * σ : ℝ) := by dsimp [p]; ring
  convert hh using 1
  · funext z
    dsimp [mellinKernel, p]
    ring
  · simp only [harg1, harg2, secondaryResidueCoefficient, p]
    congr 1
    ring

/-- The first coefficient in the repository's rectangle-residue API. -/
theorem residue_mellinKernel_zero {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) :
    residue (mellinKernel σ ξ) 0 = 1 := by
  apply residue_eq_of_tendsto
  simpa only [sub_zero, smul_eq_mul] using mellinKernel_residue_zero hσ hξ

/-- The signed second coefficient in the repository's rectangle-residue API. -/
theorem residue_mellinKernel_secondary {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hξ : 0 < ξ) :
    residue (mellinKernel σ ξ) ((1 : ℂ) - (2 * σ : ℝ)) =
      secondaryResidueCoefficient σ * (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) := by
  apply residue_eq_of_tendsto
  simpa only [smul_eq_mul] using mellinKernel_residue_secondary hσ hσ1 hξ

end RiemannResearch.Analysis.ConreyBaluyot

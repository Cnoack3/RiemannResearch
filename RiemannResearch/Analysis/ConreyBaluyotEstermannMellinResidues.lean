/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotEstermann
import RiemannResearch.Analysis.ConreyBaluyotEstermannMellinKernel
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local residues of the Gamma–Estermann Mellin kernel

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
proof of Lemma 3.1.3, pp. 96–97:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The source supports the three-pole contour calculation. We prove the
actual local limits and their values in the rectangle-residue API.

The local results need only nonzero complex damping. The two shifted
residues require distinct shifts and Gamma regularity at the relevant
pole. The zero residue requires neither invertibility of h nor distinct
shifts. Pole collisions and global contour shifts are separate tasks.
-/

open Complex Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The full kernel residue at the left shifted pole, including Gamma and damping. -/
theorem estermannMellinKernel_residue_left {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β lam : ℂ} (hα : α.re < 1) (hne : α ≠ β) (hlam : lam ≠ 0) :
    Tendsto (fun s : ℂ => (s - (1 - α)) * estermannMellinKernel (h : ZMod K) α β lam s)
      (𝓝[≠] (1 - α))
      (𝓝 (Gamma (1 - α) * lam ^ (α - 1) *
        (K : ℂ) ^ (-(1 - α + β)) * riemannZeta (1 - α + β))) := by
  have hg : ContinuousAt Gamma (1 - α) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hp : ContinuousAt (fun s : ℂ => lam ^ (-s)) (1 - α) :=
    continuousAt_id.neg.const_cpow (.inl hlam)
  have hh := (hg.continuousWithinAt.tendsto.mul hp.continuousWithinAt.tendsto).mul
    (estermann_shifted_residue_left h hne)
  have hh' : Tendsto
      (fun s : ℂ => (s - (1 - α)) * estermannMellinKernel (h : ZMod K) α β lam s)
      (𝓝[≠] (1 - α))
      (𝓝 ((Gamma (1 - α) * lam ^ (-(1 - α))) *
        ((K : ℂ) ^ (-(1 - α + β)) * riemannZeta (1 - α + β)))) :=
    hh.congr' (Eventually.of_forall fun s => by dsimp [estermannMellinKernel]; ring)
  simpa only [show -(1 - α) = α - 1 by ring, mul_assoc] using hh'

/-- The full kernel residue at the right shifted pole. -/
theorem estermannMellinKernel_residue_right {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β lam : ℂ} (hβ : β.re < 1) (hne : α ≠ β) (hlam : lam ≠ 0) :
    Tendsto (fun s : ℂ => (s - (1 - β)) * estermannMellinKernel (h : ZMod K) α β lam s)
      (𝓝[≠] (1 - β))
      (𝓝 (Gamma (1 - β) * lam ^ (β - 1) *
        (K : ℂ) ^ (-(1 - β + α)) * riemannZeta (1 - β + α))) := by
  have hh := estermannMellinKernel_residue_left h hβ hne.symm hlam
  exact hh.congr' (Eventually.of_forall fun s => by
    dsimp [estermannMellinKernel]
    rw [estermann_swap (h : ZMod K) (s + β) (s + α)])

/-- The Gamma pole at zero contributes the actual continued Estermann value. -/
theorem estermannMellinKernel_residue_zero {K : ℕ} [NeZero K] (h : ZMod K)
    {α β lam : ℂ} (hα : α ≠ 1) (hβ : β ≠ 1) (hlam : lam ≠ 0) :
    Tendsto (fun s : ℂ => s * estermannMellinKernel h α β lam s)
      (𝓝[≠] 0) (𝓝 (estermann h α β)) := by
  have hg : ContinuousAt (fun s : ℂ => Gamma (s + 1)) 0 := by
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (continuousAt_id.add continuousAt_const)
    intro n hn
    have he := congrArg Complex.re hn
    simp at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs : Tendsto (fun s : ℂ => s * Gamma s) (𝓝[≠] 0) (𝓝 1) := by
    have hh : Tendsto (fun s : ℂ => Gamma (s + 1)) (𝓝[≠] 0) (𝓝 1) := by
      simpa only [zero_add, Gamma_one] using hg.continuousWithinAt.tendsto
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    change s ≠ 0 at hs
    exact Complex.Gamma_add_one s hs
  have hp : ContinuousAt (fun s : ℂ => lam ^ (-s)) 0 :=
    continuousAt_id.neg.const_cpow (.inl hlam)
  have hd : ContinuousAt (fun s : ℂ => estermann h (s + α) (s + β)) 0 :=
    (analyticAt_estermann_shifted h α β (by simpa using hα) (by simpa using hβ)).continuousAt
  have hh := (hs.mul hp.continuousWithinAt.tendsto).mul hd.continuousWithinAt.tendsto
  have hh' : Tendsto (fun s : ℂ => (s * Gamma s) * lam ^ (-s) *
      estermann h (s + α) (s + β)) (𝓝[≠] 0) (𝓝 (estermann h α β)) := by
    simpa only [neg_zero, cpow_zero, zero_add, one_mul] using hh
  exact hh'.congr' (Eventually.of_forall fun s => by dsimp [estermannMellinKernel]; ring)


/-- The left-pole coefficient in the rectangle-residue API. -/
theorem residue_estermannMellinKernel_left {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β lam : ℂ} (hα : α.re < 1) (hne : α ≠ β) (hlam : lam ≠ 0) :
    residue (estermannMellinKernel (h : ZMod K) α β lam) (1 - α) =
      Gamma (1 - α) * lam ^ (α - 1) *
        (K : ℂ) ^ (-(1 - α + β)) * riemannZeta (1 - α + β) := by
  apply residue_eq_of_tendsto
  simpa only [smul_eq_mul] using estermannMellinKernel_residue_left h hα hne hlam

/-- The right-pole coefficient in the rectangle-residue API. -/
theorem residue_estermannMellinKernel_right {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β lam : ℂ} (hβ : β.re < 1) (hne : α ≠ β) (hlam : lam ≠ 0) :
    residue (estermannMellinKernel (h : ZMod K) α β lam) (1 - β) =
      Gamma (1 - β) * lam ^ (β - 1) *
        (K : ℂ) ^ (-(1 - β + α)) * riemannZeta (1 - β + α) := by
  apply residue_eq_of_tendsto
  simpa only [smul_eq_mul] using estermannMellinKernel_residue_right h hβ hne hlam

/-- The zero-pole coefficient in the rectangle-residue API. -/
theorem residue_estermannMellinKernel_zero {K : ℕ} [NeZero K] (h : ZMod K)
    {α β lam : ℂ} (hα : α ≠ 1) (hβ : β ≠ 1) (hlam : lam ≠ 0) :
    residue (estermannMellinKernel h α β lam) 0 = estermann h α β := by
  apply residue_eq_of_tendsto
  simpa only [sub_zero, smul_eq_mul] using estermannMellinKernel_residue_zero h hα hβ hlam

end RiemannResearch.Analysis.ConreyBaluyot

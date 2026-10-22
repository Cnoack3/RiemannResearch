import RiemannResearch.Analysis.DyadicHatRefinement
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compact support and integrability of the actual centered hats

Source: user-provided argument,
`RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Sections 29 and 36.  These are unconditional well-posedness providers for the
actual hat integrals.  They do not assume an autocorrelation formula or any
prime-discrepancy estimate.

The compact-support and integrability APIs are documented in Mathlib:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Algebra/Support.html
https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LocallyIntegrable.html
https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/LpSpace/Indicator.html
-/

noncomputable section

namespace RiemannResearch.Analysis

open MeasureTheory

theorem hasCompactSupport_centeredHat {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (centeredHat h) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-h) h) isCompact_Icc
  rw [support_centeredHat hh]
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem integrable_centeredHat {h : ℝ} (hh : 0 < h) :
    Integrable (centeredHat h) volume :=
  (continuous_centeredHat h).integrable_of_hasCompactSupport
    (hasCompactSupport_centeredHat hh)

/-- Includes the `L²` membership needed by the Weil form. -/
theorem memLp_centeredHat {h : ℝ} (hh : 0 < h) (p : ENNReal) :
    MemLp (centeredHat h) p volume :=
  (continuous_centeredHat h).memLp_of_hasCompactSupport
    (hasCompactSupport_centeredHat hh)

theorem continuous_centeredHat_translate (h c : ℝ) :
    Continuous (fun x => centeredHat h (x - c)) :=
  (continuous_centeredHat h).comp (continuous_id.sub continuous_const)

theorem hasCompactSupport_centeredHat_translate {h : ℝ} (hh : 0 < h) (c : ℝ) :
    HasCompactSupport (fun x => centeredHat h (x - c)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (c - h) (c + h)) isCompact_Icc
  intro x hx
  have hn : centeredHat h (x - c) ≠ 0 := hx
  have hp : 0 < centeredHat h (x - c) :=
    lt_of_le_of_ne (centeredHat_nonneg h (x - c)) (Ne.symm hn)
  obtain ⟨hl, hr⟩ := (centeredHat_pos_iff hh).mp hp
  constructor <;> linarith

theorem integrable_centeredHat_translate {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable (fun x => centeredHat h (x - c)) volume :=
  (continuous_centeredHat_translate h c).integrable_of_hasCompactSupport
    (hasCompactSupport_centeredHat_translate hh c)

theorem memLp_centeredHat_translate {h : ℝ} (hh : 0 < h) (c : ℝ) (p : ENNReal) :
    MemLp (fun x => centeredHat h (x - c)) p volume :=
  (continuous_centeredHat_translate h c).memLp_of_hasCompactSupport
    (hasCompactSupport_centeredHat_translate hh c)

theorem integrable_centeredHat_mul_continuous {h : ℝ} (hh : 0 < h)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun x => centeredHat h x * g x) volume :=
  ((continuous_centeredHat h).mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_centeredHat hh).mul_right

theorem integrable_centeredHat_sq {h : ℝ} (hh : 0 < h) :
    Integrable (fun x => centeredHat h x ^ 2) volume := by
  simpa only [pow_two] using
    integrable_centeredHat_mul_continuous hh (continuous_centeredHat h)

/-- The autocorrelation integrand is integrable at every translation. -/
theorem integrable_centeredHat_autocorrelation {h : ℝ} (hh : 0 < h) (u : ℝ) :
    Integrable (fun x => centeredHat h x * centeredHat h (x - u)) volume :=
  integrable_centeredHat_mul_continuous hh (continuous_centeredHat_translate h u)

/-- Every real exponential moment of the hat is an actual integrable function. -/
theorem integrable_centeredHat_exponential {h : ℝ} (hh : 0 < h) (c : ℝ) :
    Integrable (fun x => centeredHat h x * Real.exp (c * x)) volume :=
  integrable_centeredHat_mul_continuous hh
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

end RiemannResearch.Analysis

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated scalar Fourier extraction from an actual approximation

Source: `FourierBridgeUniformSignedEnergy20260910.md`, Section 3.4,
September 10, 2026. The proof uses Mathlib's Tannery theorem, whose statement
and proof are in `Mathlib/Analysis/Normed/Group/Tannery.lean`.

This is the precise dominated-limit deduction used by the residue bridge.
The residue-kernel bound, individual kernel limits, and identification of the
finite approximation with the actual coordinate are explicit hypotheses.
They are not supplied by this module.
-/

namespace RiemannResearch.Analysis

open scoped BigOperators
noncomputable section

/-- A uniformly bounded partial Fourier kernel inherits its bound at the
pointwise limit. This is the bound needed to prove summability of that limit. -/
theorem fourier_kernel_limit_norm_le
    {ι : Type*} (D : ℕ → ι → ℂ) (d : ι → ℂ) (B : ι → ℝ)
    (hD : ∀ n h, ‖D n h‖ ≤ B h)
    (hd : ∀ h, Filter.Tendsto (fun n => D n h) Filter.atTop (nhds (d h))) :
    ∀ h, ‖d h‖ ≤ B h := by
  intro h
  exact le_of_tendsto (hd h).norm (Filter.Eventually.of_forall (fun n => hD n h))

/-- Absolute convergence of the limiting Fourier row from a summable
uniform partial-kernel majorant. -/
theorem summable_fourier_kernel_limit_of_majorant
    {ι : Type*} (c : ι → ℂ) (D : ℕ → ι → ℂ) (d : ι → ℂ) (B : ι → ℝ)
    (hB : Summable (fun h => ‖c h‖ * B h))
    (hD : ∀ n h, ‖D n h‖ ≤ B h)
    (hd : ∀ h, Filter.Tendsto (fun n => D n h) Filter.atTop (nhds (d h))) :
    Summable (fun h => ‖c h * d h‖) := by
  apply hB.of_norm_bounded
  intro h
  rw [norm_norm, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (fourier_kernel_limit_norm_le D d B hD hd h) (norm_nonneg _)

/-- The full scalar Fourier sum equals an independently identified actual
limit. The `v n` may be coordinates of finite physical residue approximants.
The proof does not posit the desired limiting Fourier identity: it derives
it from the exact finite identities and uniform cutoff-independent bounds. -/
theorem hasSum_fourier_kernel_limit_of_actual_approximation
    {ι : Type*} (c : ι → ℂ) (D : ℕ → ι → ℂ) (d : ι → ℂ) (B : ι → ℝ)
    (hB : Summable (fun h => ‖c h‖ * B h))
    (hD : ∀ n h, ‖D n h‖ ≤ B h)
    (hd : ∀ h, Filter.Tendsto (fun n => D n h) Filter.atTop (nhds (d h)))
    (v : ℕ → ℂ) (a : ℂ)
    (hv : ∀ n, v n = ∑' h, c h * D n h)
    (ha : Filter.Tendsto v Filter.atTop (nhds a)) :
    HasSum (fun h => c h * d h) a := by
  have hpoint : ∀ h, Filter.Tendsto (fun n => c h * D n h)
      Filter.atTop (nhds (c h * d h)) := by
    intro h
    exact tendsto_const_nhds.mul (hd h)
  have hmajor : ∀ᶠ n in Filter.atTop, ∀ h,
      ‖c h * D n h‖ ≤ ‖c h‖ * B h := by
    apply Filter.Eventually.of_forall
    intro n h
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hD n h) (norm_nonneg _)
  have hlimit := tendsto_tsum_of_dominated_convergence hB hpoint hmajor
  have hvfun : v = (fun n => ∑' h, c h * D n h) := funext hv
  rw [hvfun] at ha
  have hactual : a = ∑' h, c h * d h := tendsto_nhds_unique ha hlimit
  rw [hactual]
  exact (summable_fourier_kernel_limit_of_majorant c D d B hB hD hd).of_norm.hasSum

end
end RiemannResearch.Analysis

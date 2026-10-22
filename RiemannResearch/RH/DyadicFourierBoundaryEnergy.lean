import RiemannResearch.Analysis.AbelFourierCancellation
import RiemannResearch.RH.DyadicSignedBoundaryNormCriterion

/-! Exact transfer of scalar Fourier HasSum identities to the actual signed
boundary energy. Source: user-provided FourierBridgeUniformSignedEnergy20260910.md,
Sections 5–6. The component expansions remain explicit analytic hypotheses. -/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- The actual normalized remainder has the signed Fourier series, provided
the two separate Fourier expansions and the exact scalar mean identity hold.
The conclusion uses the existing arithmetic coefficient, not a new surrogate. -/
theorem dyadicNormalizationBoundaryCoefficient_hasSum_fourier_of_components
    {ι : Type*} {ε : ℝ} (hε : 0 < ε)
    (c0 : ℕ → ℂ) (c : ℕ → ι → ℂ) (z M : ι → ℂ)
    (hd : ∀ h, 1 - (triadicDampingRatio ε : ℂ) * z h ≠ 0)
    (hc : ∀ i, HasSum (c i) (-c0 i))
    (hg : ∀ i, HasSum
      (fun h => c i h *
        (M h * abelCancellationMultiplier (triadicDampingRatio ε) (z h)))
      ((dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) - c0 i))
    (hk : ∀ i, HasSum
      (fun h => c i h * ((1 - (triadicDampingRatio ε : ℂ)) * z h /
        (1 - (triadicDampingRatio ε : ℂ) * z h)))
      (-(dyadicBoundaryCoordinate (dyadicNormalizationComparison ε) i : ℂ))) :
    ∀ i, HasSum
      (fun h => c i h * (M h - 1) *
        abelCancellationMultiplier (triadicDampingRatio ε) (z h))
      (dyadicNormalizationBoundaryCoefficient ε i : ℂ) := by
  intro i
  have hs := abelCancellationMultiplier_hasSum_mean_cancellation
    (triadicDampingRatio ε) (c0 i)
    (dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ)
    (dyadicBoundaryCoordinate (dyadicNormalizationComparison ε) i : ℂ)
    (c i) z M hd (hc i) (hg i) (hk i)
  have hactual :
      (dyadicBoundaryCoordinate (dyadicRegularizedFamily ε) i : ℂ) -
        (dyadicBoundaryCoordinate (dyadicNormalizationComparison ε) i : ℂ) =
      (dyadicNormalizationBoundaryCoefficient ε i : ℂ) := by
    rw [← Complex.ofReal_sub, ← dyadicBoundaryCoordinate_sub,
      ← dyadicNormalizationRemainder,
      dyadicNormalizationRemainder_boundaryCoordinate hε]
  rwa [hactual] at hs

/-- Full square summability of an identified Fourier representation follows
from the actual Hilbert vector. No diagonal frequency bound is substituted. -/
theorem dyadicNormalizationFourier_energy_summable_of_hasSum
    {ι : Type*} {ε : ℝ} (hε : 0 < ε) (f : ℕ → ι → ℂ)
    (hf : ∀ i, HasSum (f i) (dyadicNormalizationBoundaryCoefficient ε i : ℂ)) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) * ‖∑' h, f i h‖ ^ 2) := by
  apply (dyadicNormalizationBoundaryCoefficient_square_summable hε).congr
  intro i
  rw [(hf i).tsum_eq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Exact full-norm Fourier bridge from a proved coordinatewise `HasSum`.
All infinitely many boundary coordinates and all frequency cross terms
remain inside the norm squares. -/
theorem dyadicNormalizationRemainder_norm_sq_eq_fourier_of_hasSum
    {ι : Type*} {ε : ℝ} (hε : 0 < ε) (f : ℕ → ι → ℂ)
    (hf : ∀ i, HasSum (f i) (dyadicNormalizationBoundaryCoefficient ε i : ℂ)) :
    ‖dyadicNormalizationRemainder ε‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) * ‖∑' h, f i h‖ ^ 2 := by
  rw [dyadicNormalizationRemainder_norm_sq_eq_signedBoundary hε]
  apply tsum_congr
  intro i
  rw [(hf i).tsum_eq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The outer boundary-energy limit is an actual convergent sum after the
frequency sums have been evaluated coordinatewise. This is the permissible
order of limits in the analytic note. -/
theorem dyadicNormalizationFourier_energy_hasSum_of_hasSum
    {ι : Type*} {ε : ℝ} (hε : 0 < ε) (f : ℕ → ι → ℂ)
    (hf : ∀ i, HasSum (f i) (dyadicNormalizationBoundaryCoefficient ε i : ℂ)) :
    HasSum (fun i : ℕ => (1 / 4 : ℝ) * ‖∑' h, f i h‖ ^ 2)
      (‖dyadicNormalizationRemainder ε‖ ^ 2) := by
  rw [dyadicNormalizationRemainder_norm_sq_eq_fourier_of_hasSum hε f hf]
  exact (dyadicNormalizationFourier_energy_summable_of_hasSum hε f hf).hasSum

/-- The full actual norm criterion can be discharged by a uniform finite
boundary bound on a separately identified Fourier series. This reduction
retains all mixed terms; it does not supply the bound itself. -/
theorem dyadicRegularized_norm_obligations_of_fourier_energy
    {ι : Type*} (f : ℝ → ℕ → ι → ℂ)
    (hf : ∀ ε, 0 < ε → ε ≤ 1 / 2 → ∀ i,
      HasSum (f ε i) (dyadicNormalizationBoundaryCoefficient ε i : ℂ))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ s : Finset ℕ,
      (∑ i ∈ s, (1 / 4 : ℝ) * ‖∑' h, f ε i h‖ ^ 2) ≤ C) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  apply dyadicRegularized_norm_obligations_of_signedBoundary C hC
  intro ε hε hhalf s
  have hb := hbound ε hε hhalf s
  have hcoord (i : ℕ) : ∑' h, f ε i h =
      (dyadicNormalizationBoundaryCoefficient ε i : ℂ) :=
    (hf ε hε hhalf i).tsum_eq
  simpa only [hcoord, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb

end
end RiemannResearch.RH.Pareto

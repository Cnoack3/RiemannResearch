import RiemannResearch.Analysis.HilbertBasisWeakLimit
import RiemannResearch.Analysis.WeakConvexRepair
import RiemannResearch.RH.DyadicSignedDampingPackets
import RiemannResearch.RH.DyadicFourierFrequencyDomination
import Mathlib.Analysis.Convex.Combination

/-!
# Conditional convex repair of the actual normalization remainder

Source: user-provided FourierZeroDampingVerification20260911(1).md;
independently developed continuation via the standard weak-convergence and
convex-closure argument (Mazur's lemma), implemented by WeakConvexRepair.

A uniform norm bound and vanishing actual boundary coordinates imply weak
convergence in the full physical Hilbert space. The two existing named
analytic targets therefore yield arbitrarily small finite convex mixtures
of actual remainders. The exact Fourier energy keeps every mixed term.
Neither analytic provider is proved here. Individual energy tightness is
unnecessary for mixtures, but centered-comparison control and full legal
recovery remain separate. This module does not prove RH.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped Topology
open scoped BigOperators
noncomputable section

theorem dyadicNormalizationRemainder_pairing_tendsto_zero
    {α : Type*} {l : Filter α} (ε : α → ℝ)
    (hε : ∀ᶠ a in l, 0 < ε a)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ a in l, ‖dyadicNormalizationRemainder (ε a)‖ ≤ C)
    (hcoord : ∀ i, Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (𝓝 0))
    (x : ThresholdHilbert) :
    Tendsto (fun a => inner ℝ x (dyadicNormalizationRemainder (ε a))) l (𝓝 0) := by
  let u : α → dyadicQuotientSubspace :=
    fun a => dyadicQuotientVector (dyadicNormalizationRemainder (ε a))
  have hb : ∀ᶠ a in l, ‖u a‖ ≤ C := by
    filter_upwards [hε, hbound] with a ha hba
    change ‖dyadicQuotientProjection (dyadicNormalizationRemainder (ε a))‖ ≤ C
    rwa [dyadicNormalizationRemainder_projection (ε a) ha]
  have hc : ∀ n, Tendsto
      (fun a => inner ℝ (dyadicBoundaryHilbertBasis n) (u a)) l (𝓝 0) := by
    intro n
    cases n with
    | zero =>
      have he : (fun a => inner ℝ (dyadicBoundaryHilbertBasis 0) (u a)) =ᶠ[l]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hε] with a ha
        rw [dyadicBoundaryHilbertBasis_inner_zero, real_inner_comm,
          dyadicNormalizationRemainder_inner_one (ε a) ha]
      exact (tendsto_congr' he).mpr tendsto_const_nhds
    | succ i =>
      have he : (fun a => inner ℝ (dyadicBoundaryHilbertBasis (i+1)) (u a)) =ᶠ[l]
          (fun a => (1/2 : ℝ) * dyadicNormalizationBoundaryCoefficient (ε a) i) := by
        filter_upwards [hε] with a ha
        rw [dyadicBoundaryHilbertBasis_inner_succ]
        rw [← dyadicNormalizationRemainder_boundaryCoordinate ha i]
        dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
        ring
      apply (tendsto_congr' he).mpr
      simpa using (hcoord i).const_mul (1/2 : ℝ)
  have ht := dyadicBoundaryHilbertBasis.inner_tendsto_zero_of_bounded_coordinates
    u hC hb hc (dyadicQuotientVector x)
  have he : (fun a => inner ℝ (dyadicQuotientVector x) (u a)) =ᶠ[l]
      (fun a => inner ℝ x (dyadicNormalizationRemainder (ε a))) := by
    filter_upwards [hε] with a ha
    change inner ℝ (dyadicQuotientProjection x)
      (dyadicQuotientProjection (dyadicNormalizationRemainder (ε a))) = _
    rw [dyadicNormalizationRemainder_projection (ε a) ha,
      dyadicQuotientProjection_inner,
      dyadicNormalizationRemainder_projection (ε a) ha]
  exact ht.congr' he

/-- Coordinate decay and an eventual norm bound give genuine weak convergence
of the actual remainder in the full physical Hilbert space. -/
theorem dyadicNormalizationRemainder_weak_tendsto_zero
    {α : Type*} {l : Filter α} (ε : α → ℝ)
    (hε : ∀ᶠ a in l, 0 < ε a)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ a in l, ‖dyadicNormalizationRemainder (ε a)‖ ≤ C)
    (hcoord : ∀ i, Tendsto
      (fun a => dyadicNormalizationBoundaryCoefficient (ε a) i) l (𝓝 0)) :
    Tendsto (fun a => toWeakSpace ℝ ThresholdHilbert
      (dyadicNormalizationRemainder (ε a))) l (𝓝 0) := by
  exact RiemannResearch.Analysis.weak_tendsto_zero_of_inner_tendsto
    (dyadicNormalizationRemainder_pairing_tendsto_zero ε hε hC hbound hcoord)

/-- Conditional specialization to the two existing named analytic targets.
Neither the multiplier bound nor the uniform remainder energy is supplied here. -/
theorem dyadicNormalizationRemainder_weak_tendsto_zero_of_bounds
    (hfrequency : DyadicUniformSignedFourierMultiplierSqrtBound)
    (henergy : DyadicNormalizationRemainderUniformEnergyBound) :
    Tendsto (fun ε => toWeakSpace ℝ ThresholdHilbert
      (dyadicNormalizationRemainder ε))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨C, hC, henergy⟩ := henergy
  have hhalf : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1/2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)).filter_mono inf_le_left
  apply dyadicNormalizationRemainder_weak_tendsto_zero (fun ε : ℝ => ε)
    eventually_mem_nhdsWithin (show 0 ≤ C+1 by linarith) _
    (dyadicNormalizationBoundaryCoefficient_tendsto_zero_of_sqrt_bound hfrequency)
  filter_upwards [eventually_mem_nhdsWithin, hhalf] with ε hε hεhalf
  have he := henergy ε hε hεhalf.le
  nlinarith [norm_nonneg (dyadicNormalizationRemainder ε)]

/-- Each arbitrarily small damping interval contains a finite convex mixture
of actual remainders with arbitrarily small norm, conditional on the existing
frequency-growth and energy targets. Individual boundary-tail tightness is
not required. This is not a statement of physical/legal recovery. -/
theorem exists_small_dyadicNormalizationRemainder_convex_mixture
    (hfrequency : DyadicUniformSignedFourierMultiplierSqrtBound)
    (henergy : DyadicNormalizationRemainderUniformEnergyBound)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ v ∈ convexHull ℝ (dyadicNormalizationRemainder '' Set.Ioo 0 δ), ‖v‖ < η := by
  have hA : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono inf_le_left] with ε hε hεδ
    exact ⟨hε, hεδ⟩
  exact RiemannResearch.Analysis.exists_norm_lt_mem_convexHull_image_of_weak_tendsto
    (dyadicNormalizationRemainder_weak_tendsto_zero_of_bounds hfrequency henergy) hA hη

/-- Explicit finite nonnegative weights realize the conditional small mixture,
with the complete Fourier energy below the squared requested tolerance. -/
theorem exists_dyadicNormalizationRemainder_convex_weights_small_fourier_energy
    (hfrequency : DyadicUniformSignedFourierMultiplierSqrtBound)
    (henergy : DyadicNormalizationRemainderUniformEnergyBound)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ (κ : Type) (_ : Fintype κ) (a ε : κ → ℝ),
      (∀ k, 0 ≤ a k) ∧ (∑ k, a k) = 1 ∧
      (∀ k, ε k ∈ Set.Ioo 0 δ) ∧
      ‖∑ k, a k • dyadicNormalizationRemainder (ε k)‖ < η ∧
      (∑' i : ℕ, (1/4 : ℝ) *
        ‖∑ k, (a k : ℂ) * (∑' h, dyadicSignedFourierTerm (ε k) i h)‖ ^ 2) < η^2 := by
  classical
  obtain ⟨v, hv, hvnorm⟩ :=
    exists_small_dyadicNormalizationRemainder_convex_mixture hfrequency henergy hδ hη
  obtain ⟨κ, hκ, a, z, ha, haone, hz, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  let := hκ
  choose ε hε hzε using hz
  have hvsum : (∑ k, a k • dyadicNormalizationRemainder (ε k)) = v := by
    simpa only [hzε] using hsum
  have hn : ‖∑ k, a k • dyadicNormalizationRemainder (ε k)‖ < η := by
    rwa [hvsum]
  refine ⟨κ, hκ, a, ε, ha, haone, hε, hn, ?_⟩
  rw [← dyadicNormalizationRemainder_finite_norm_sq_eq_signed_fourier
    Finset.univ a ε (fun k _ => (hε k).1)]
  nlinarith [norm_nonneg (∑ k, a k • dyadicNormalizationRemainder (ε k))]

end
end RiemannResearch.RH.Pareto

import RiemannResearch.RH.ParetoL1Equality
import RiemannResearch.RH.ResidueSchurLimits
import RiemannResearch.RH.ThresholdHilbertL1

/-!
# L1 convergence and the actual Pareto projection defect

Source: the user's projection convergence and squared-error expansion,
22 September 2026. Stage n is manuscript cutoff N=n+1.
All norms and expectations use the complete infinite Pareto measure.

Established: the projection error satisfies E_n <= L1_error_n <= sqrt(E_n).
Hence L1 convergence to one, L2 convergence to one, zero limiting defect,
and membership of one in the closed residue span are equivalent.
The unconditional first and second projection moments tend to 1-D;
the expanded squared error tends to D.

Conditional research reduction: riemannHypothesis_of_projection_l1_tendsto_zero.
Open: L1 convergence to one, equivalently limitEnergy = 0.
The prior convergence audit proves existence of the limit projection,
not that the limiting defect vanishes.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The actual coefficient limits force the actual limiting defect to vanish. -/
theorem limitEnergy_zero_of_coefficients_tendsto_mobius
    (h : ∀ d : ℕ, 1 < d →
      Tendsto (fun n => coefficient n d) atTop
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) :
    limitEnergy = 0 := by
  apply limitEnergy_zero_iff_mem.mpr
  exact limitCoefficients_eq_mobius_iff_mem.mp
    (coefficients_tendsto_mobius_iff.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur

theorem inner_one_projection_eq_captured (n : ℕ) :
    inner ℝ hilbertOne (projection n) = captured n := by
  have h := norm_sub_sq_real hilbertOne (projection n)
  rw [hilbertOne_norm_sq, ← captured_eq_norm_sq n,
    error_eq_one_sub_captured n] at h
  linarith

theorem inner_one_projection_eq_one_sub_energy (n : ℕ) :
    inner ℝ hilbertOne (projection n) = 1 - energy n := by
  rw [inner_one_projection_eq_captured]
  have h := error_eq_one_sub_captured n
  change energy n = 1 - captured n at h
  linarith

theorem inner_one_residual_eq_energy (n : ℕ) :
    inner ℝ hilbertOne (hilbertOne - projection n) = energy n := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    inner_one_projection_eq_one_sub_energy]
  ring

theorem energy_expansion (n : ℕ) :
    energy n = 1 - 2 * inner ℝ hilbertOne (projection n) + ‖projection n‖ ^ 2 := by
  change ‖hilbertOne - projection n‖ ^ 2 = _
  rw [norm_sub_sq_real, hilbertOne_norm_sq]

theorem inner_one_projection_tendsto :
    Tendsto (fun n => inner ℝ hilbertOne (projection n))
      atTop (𝓝 (1 - limitEnergy)) := by
  simp_rw [inner_one_projection_eq_one_sub_energy]
  exact tendsto_const_nhds.sub energy_tendsto

theorem projection_norm_sq_tendsto :
    Tendsto (fun n => ‖projection n‖ ^ 2) atTop (𝓝 (1 - limitEnergy)) := by
  simpa only [captured_eq_norm_sq] using
    (show Tendsto (fun n => captured n) atTop (𝓝 (1 - limitEnergy)) from captured_tendsto)

theorem expanded_energy_tendsto :
    Tendsto (fun n => 1 - 2 * inner ℝ hilbertOne (projection n) + ‖projection n‖ ^ 2)
      atTop (𝓝 limitEnergy) := by
  simpa only [energy_expansion] using
    (show Tendsto (fun n => energy n) atTop (𝓝 limitEnergy) from energy_tendsto)

theorem inner_one_limitProjection :
    inner ℝ hilbertOne limitProjection = 1 - limitEnergy :=
  tendsto_nhds_unique
    (((innerSL ℝ hilbertOne).continuous.tendsto _).comp projection_tendsto)
    inner_one_projection_tendsto

theorem energy_le_l1_error (n : ℕ) :
    energy n ≤ hilbertL1Norm (hilbertOne - projection n) := by
  rw [← inner_one_residual_eq_energy, real_inner_comm]
  exact inner_one_le_hilbertL1Norm _

theorem l1_error_le_l2_error (n : ℕ) :
    hilbertL1Norm (hilbertOne - projection n) ≤ ‖hilbertOne - projection n‖ :=
  hilbertL1Norm_le_norm _

theorem projection_l1_tendsto_limit :
    Tendsto (fun n => hilbertL1Norm (projection n - limitProjection)) atTop (𝓝 0) := by
  apply hilbertL1Norm_tendsto_zero_of_norm
  have hc : Tendsto (fun _ : ℕ => limitProjection) atTop (𝓝 limitProjection) :=
    tendsto_const_nhds
  simpa only [sub_self, norm_zero] using (projection_tendsto.sub hc).norm

/-- L1 convergence to the target is equivalent to vanishing of the actual defect. -/
theorem l1_error_tendsto_zero_iff_limitEnergy_zero :
    Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n)) atTop (𝓝 0) ↔
      limitEnergy = 0 := by
  constructor
  · intro h
    have hE : Tendsto energy atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg ‖hilbertOne - projection n‖)
        energy_le_l1_error h
    exact tendsto_nhds_unique energy_tendsto hE
  · intro hD
    apply hilbertL1Norm_tendsto_zero_of_norm
    exact projection_norm_tendsto_zero_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hD)

theorem l1_error_tendsto_zero_iff_l2 :
    Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n)) atTop (𝓝 0) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) :=
  l1_error_tendsto_zero_iff_limitEnergy_zero.trans
    (limitEnergy_zero_iff_mem.trans projection_norm_tendsto_zero_iff_mem.symm)

/-- This is closure of the span of all actual residue generators. -/
theorem l1_error_tendsto_zero_iff_closed_span :
    Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n)) atTop (𝓝 0) ↔
      hilbertOne ∈ (Submodule.span ℝ (Set.range residueAtom)).topologicalClosure :=
  l1_error_tendsto_zero_iff_limitEnergy_zero.trans limitEnergy_zero_iff_mem

theorem projection_tendsto_one_of_limitEnergy_zero (hD : limitEnergy = 0) :
    Tendsto projection atTop (𝓝 hilbertOne) := by
  have hr : hilbertOne - limitProjection = 0 :=
    limitResidual_zero_iff_energy_zero.mpr hD
  have hu : limitProjection = hilbertOne := (sub_eq_zero.mp hr).symm
  simpa only [hu] using projection_tendsto

/-- Conditional research reduction: L1 convergence of the actual projections
remains an open hypothesis; the closure-to-RH bridge is already proved. -/
theorem riemannHypothesis_of_projection_l1_tendsto_zero
    (h : Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  exact closedSpace_le_legalClosure
    (l1_error_tendsto_zero_iff_closed_span.mp h)

/-- Conditional research reduction: the user's entire chain, starting with
the simultaneous fixed-conductor Mobius limits for the actual projections. -/
theorem convergence_chain_of_coefficients_tendsto_mobius
    (h : ∀ d : ℕ, 1 < d →
      Tendsto (fun n => coefficient n d) atTop
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) :
    limitEnergy = 0 ∧
    Tendsto projection atTop (𝓝 hilbertOne) ∧
    Tendsto (fun n => hilbertL1Norm (hilbertOne - projection n)) atTop (𝓝 0) ∧
    Tendsto (fun n => inner ℝ hilbertOne (projection n)) atTop (𝓝 1) ∧
    Tendsto (fun n => ‖projection n‖ ^ 2) atTop (𝓝 1) ∧
    Tendsto (fun n => 1 - 2 * inner ℝ hilbertOne (projection n) + ‖projection n‖ ^ 2)
      atTop (𝓝 0) ∧
    hilbertOne ∈ (Submodule.span ℝ (Set.range residueAtom)).topologicalClosure ∧
    RiemannHypothesis := by
  have hD := limitEnergy_zero_of_coefficients_tendsto_mobius h
  have hL1 := l1_error_tendsto_zero_iff_limitEnergy_zero.mpr hD
  refine ⟨hD, projection_tendsto_one_of_limitEnergy_zero hD, hL1, ?_, ?_, ?_,
    l1_error_tendsto_zero_iff_closed_span.mp hL1,
    riemannHypothesis_of_projection_l1_tendsto_zero hL1⟩
  · simpa only [hD, sub_zero] using inner_one_projection_tendsto
  · simpa only [hD, sub_zero] using projection_norm_sq_tendsto
  · simpa only [hD] using expanded_energy_tendsto

open RiemannResearch.Analysis.UnitVectorVariance

/-- The mean of the actual full-conductor Pareto residual is its complete energy. -/
theorem limitResidual_mean_eq_energy :
    inner ℝ hilbertOne limitResidual = limitEnergy := by
  change inner ℝ hilbertOne (hilbertOne - limitProjection) = limitEnergy
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
    inner_one_limitProjection]
  ring

theorem limitResidual_norm_sq : ‖limitResidual‖ ^ 2 = limitEnergy := rfl

/-- Exact residual variance; matching first and second moments does not remove it. -/
theorem limitResidual_variance_eq :
    ‖limitResidual - limitEnergy • hilbertOne‖ ^ 2 =
      limitEnergy * (1 - limitEnergy) := by
  have h := centered_norm_sq hilbertOne limitResidual hilbertOne_norm_sq
  rw [limitResidual_mean_eq_energy, limitResidual_norm_sq] at h
  rw [h]
  ring

theorem limitProjection_variance_eq :
    ‖limitProjection - (1 - limitEnergy) • hilbertOne‖ ^ 2 =
      limitEnergy * (1 - limitEnergy) := by
  have hn : ‖limitProjection‖ ^ 2 = 1 - limitEnergy :=
    tendsto_nhds_unique (projection_tendsto.norm.pow 2) projection_norm_sq_tendsto
  have h := centered_norm_sq hilbertOne limitProjection hilbertOne_norm_sq
  rw [inner_one_limitProjection, hn] at h
  rw [h]
  ring

/-- First-moment/second-moment agreement is not Cauchy--Schwarz equality. -/
theorem limitResidual_cs_equality_iff :
    |inner ℝ hilbertOne limitResidual| = ‖limitResidual‖ ↔
      limitEnergy = 0 ∨ limitEnergy = 1 := by
  rw [limitResidual_mean_eq_energy]
  have hn := limitResidual_norm_sq
  constructor
  · intro h
    have hs := congrArg (fun t : ℝ => t ^ 2) h
    rw [sq_abs, hn] at hs
    have hz : limitEnergy * (1 - limitEnergy) = 0 := by
      nlinarith only [hs]
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · intro h
    rcases h with h | h
    · rw [h] at hn ⊢
      have hz : ‖limitResidual‖ = 0 := sq_eq_zero_iff.mp hn
      simp [hz]
    · rw [h] at hn ⊢
      have hone : ‖limitResidual‖ = 1 := by nlinarith [norm_nonneg limitResidual]
      simp [hone]

end RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur

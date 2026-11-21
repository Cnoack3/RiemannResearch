import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.Analysis.OrthogonalDistanceBound
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Approximating the difference between the constant and the screened vector

Both vectors are orthogonal to the mixed-conductor closure. The best mixed
approximant to their difference is zero. The exact squared error identifies
convergence of finite mixed packet combinations with membership of the ambient
constant in the legal closure. The latter is the approximation condition in
B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, Theorem 1, https://arxiv.org/abs/math/0607733.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- The ambient constant minus the screened mean-one vector is orthogonal to all mixed vectors. -/
theorem one_sub_screenedTwo_mem_mixed_orthogonal :
    hilbertOne - normalizedScreenedTwo ∈ mixedClosureᗮ :=
  mixedClosure.orthogonal.sub_mem one_mem_mixedClosure_orthogonal
    ((Submodule.starProjection_apply_eq_zero_iff _).mp mixed_starProjection_screenedTwo)

/-- Any mixed approximant contributes its full squared norm to the error. -/
theorem one_sub_screenedTwo_mixed_error_sq {m : ThresholdHilbert} (hm : m ∈ mixedClosure) :
    ‖(hilbertOne - normalizedScreenedTwo) - m‖ ^ 2 =
      limitEnergy / (1 - limitEnergy) + ‖m‖ ^ 2 := by
  have ho : inner ℝ (hilbertOne - normalizedScreenedTwo) m = 0 :=
    mixedClosure.inner_left_of_mem_orthogonal hm one_sub_screenedTwo_mem_mixed_orthogonal
  rw [norm_sub_sq_real, ho, norm_sub_rev hilbertOne normalizedScreenedTwo,
    normalizedScreenedTwo_error_sq_eq_limitEnergy]
  ring

/-- The squared distance from the discrepancy to the entire closed mixed span. -/
theorem one_sub_screenedTwo_mixed_infDist_sq :
    Metric.infDist (hilbertOne - normalizedScreenedTwo) (mixedClosure : Set ThresholdHilbert) ^ 2 =
      limitEnergy / (1 - limitEnergy) := by
  rw [mixedClosure.infDist_eq_norm_sub_starProjection,
    (Submodule.starProjection_apply_eq_zero_iff _).mpr one_sub_screenedTwo_mem_mixed_orthogonal,
    sub_zero, norm_sub_rev, normalizedScreenedTwo_error_sq_eq_limitEnergy]

/-- The proposed mixed membership is equivalent to the original legal-closure condition. -/
theorem one_sub_screenedTwo_mem_mixedClosure_iff :
    hilbertOne - normalizedScreenedTwo ∈ mixedClosure ↔ hilbertOne ∈ closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro hm
    have h := (mixedClosure.mem_orthogonal _).mp one_sub_screenedTwo_mem_mixed_orthogonal _ hm
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp h)).symm
  · intro hu
    rw [hu, sub_self]
    exact mixedClosure.zero_mem

/-- Finite mixed packet fits to the discrepancy converge exactly when the constant is legal.
In that case the zero combination at every cutoff realizes the convergence. -/
theorem finite_mixed_tendsto_one_sub_screenedTwo_iff :
    (∃ p : ℕ → ThresholdHilbert, (∀ N, p N ∈ mixedSpace (Finset.Icc 2 N)) ∧
      Tendsto p atTop (𝓝 (hilbertOne - normalizedScreenedTwo))) ↔ hilbertOne ∈ closedSpace := by
  constructor
  · rintro ⟨p, hp, hlim⟩
    apply one_sub_screenedTwo_mem_mixedClosure_iff.mp
    have hclosed : IsClosed (mixedClosure : Set ThresholdHilbert) :=
      (⨆ N : ℕ, mixedSpace (Finset.Icc 2 N)).isClosed_topologicalClosure
    exact hclosed.mem_of_tendsto hlim (Eventually.of_forall fun N =>
      mixedSpace_window_le_closure N (hp N))
  · intro h
    rw [one_mem_closedSpace_iff_normalizedScreenedTwo] at h
    rw [h, sub_self]
    exact ⟨fun _ => 0, fun N => (mixedSpace (Finset.Icc 2 N)).zero_mem, tendsto_const_nhds⟩

/-- Finite screening at conductor two changes the limit vector by a mixed vector. -/
theorem fixedTwoTrial_sub_screenedTwo_mem_mixedClosure (N : ℕ) :
    fixedTwoTrial N - normalizedScreenedTwo ∈ mixedClosure := by
  let z := ramanujanPacketHilbert 2
  let K := mixedSpace (Finset.Icc 2 N)
  change (Real.log 2)⁻¹ • (z - K.starProjection z) -
    (Real.log 2)⁻¹ • (z - mixedClosure.starProjection z) ∈ mixedClosure
  rw [← smul_sub]
  apply mixedClosure.smul_mem
  rw [show (z - K.starProjection z) - (z - mixedClosure.starProjection z) =
    mixedClosure.starProjection z - K.starProjection z by abel]
  exact mixedClosure.sub_mem (mixedClosure.starProjection_apply_mem z)
    (mixedSpace_window_le_closure N (K.starProjection_apply_mem z))

/-- At each finite cutoff the error splits into the limiting squared discrepancy
and the squared distance to the screened limit. -/
theorem fixedTwoTrial_error_sq_eq_limit_add_tail (N : ℕ) :
    ‖hilbertOne - fixedTwoTrial N‖ ^ 2 = limitEnergy / (1 - limitEnergy) +
      ‖fixedTwoTrial N - normalizedScreenedTwo‖ ^ 2 := by
  have h := one_sub_screenedTwo_mixed_error_sq (fixedTwoTrial_sub_screenedTwo_mem_mixedClosure N)
  rwa [show (hilbertOne - normalizedScreenedTwo) - (fixedTwoTrial N - normalizedScreenedTwo) =
    hilbertOne - fixedTwoTrial N by abel] at h

end RiemannResearch.RH.Pareto.PrimePowerSchur

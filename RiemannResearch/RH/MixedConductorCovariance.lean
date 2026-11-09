import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.PsiNormalizedRamanujan
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Independent prime and mixed cutoffs for complete Pareto screening

The mixed-conductor CRT handoff supplies the two-cutoff setup. These results
identify the exact diagonal and off-diagonal errors, select finite mixed
cutoffs for arbitrary moving inputs, and attain the centered dual bound.
The final RH implication assumes decay of the complete covariance.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.Analysis.ExhaustiveWalk
open CoefficientStabilization

def finiteScreening (M : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  1 - (mixedSpace (Finset.Icc 2 M)).starProjection

theorem finiteScreening_apply (M : ℕ) (z : ThresholdHilbert) :
    finiteScreening M z = z - (mixedSpace (Finset.Icc 2 M)).starProjection z := rfl

theorem one_mem_mixedClosure_orthogonal : hilbertOne ∈ mixedClosureᗮ := by
  apply (Submodule.starProjection_apply_eq_zero_iff mixedClosure).mp
  have h := fullScreening_one
  change hilbertOne - mixedClosure.starProjection hilbertOne = hilbertOne at h
  exact sub_eq_self.mp h

theorem fullScreening_mem_orthogonal (z : ThresholdHilbert) :
    fullScreening z ∈ mixedClosureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal z

theorem fullScreening_inner_right_of_orthogonal (z h : ThresholdHilbert)
    (hh : h ∈ mixedClosureᗮ) :
    inner ℝ (fullScreening z) h = inner ℝ z h := by
  change inner ℝ (z - mixedClosure.starProjection z) h = _
  rw [inner_sub_left, (mixedClosure.mem_orthogonal h).mp hh _
    (mixedClosure.starProjection_apply_mem z), sub_zero]

theorem finiteScreening_energy_split (M L : ℕ) (hML : M ≤ L) (z : ThresholdHilbert) :
    ‖finiteScreening M z‖ ^ 2 = ‖finiteScreening L z‖ ^ 2 +
      ‖(mixedSpace (Finset.Icc 2 L)).starProjection z -
        (mixedSpace (Finset.Icc 2 M)).starProjection z‖ ^ 2 :=
  nested_projection_energy _ _ (mixedSpace_mono (Finset.Icc_subset_Icc le_rfl hML)) z

theorem finiteScreening_energy_eq_full_add_tail (M : ℕ) (z : ThresholdHilbert) :
    ‖finiteScreening M z‖ ^ 2 = ‖fullScreening z‖ ^ 2 +
      ‖mixedClosure.starProjection z -
        (mixedSpace (Finset.Icc 2 M)).starProjection z‖ ^ 2 :=
  nested_projection_energy _ _ (mixedSpace_window_le_closure M) z

/-- An arbitrary positive error tolerance is available separately for each
input, even when the inputs move and their norms grow. -/
theorem exists_finiteScreening_cutoffs (x : ℕ → ThresholdHilbert)
    (lower : ℕ → ℕ) (ε : ℕ → ℝ) (hε : ∀ N, 0 < ε N) :
    ∃ M : ℕ → ℕ, ∀ N, lower N ≤ M N ∧
      ‖finiteScreening (M N) (x N) - fullScreening (x N)‖ < ε N := by
  classical
  have ht (N : ℕ) : Tendsto (fun M => finiteScreening M (x N)) atTop
      (𝓝 (fullScreening (x N))) := by
    have hmono : Monotone (fun M : ℕ => mixedSpace (Finset.Icc 2 M)) :=
      fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
    simpa only [finiteScreening_apply, fullScreening, sub_apply,
      one_apply_eq_self, mixedClosure] using
      (tendsto_const_nhds (x := x N)).sub
        (Submodule.starProjection_tendsto_closure_iSup _ hmono (x N))
  have h (N : ℕ) : ∃ M, lower N ≤ M ∧
      ‖finiteScreening M (x N) - fullScreening (x N)‖ < ε N := by
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp (ht N) (ε N) (hε N)
    exact ⟨max L (lower N), le_max_right _ _, by
      simpa only [dist_eq_norm] using hL _ (le_max_left _ _)⟩
  choose M hM using h
  exact ⟨M, hM⟩

theorem exists_finiteScreening_cutoffs_tendsto (x : ℕ → ThresholdHilbert)
    (lower : ℕ → ℕ) :
    ∃ M : ℕ → ℕ, (∀ N, lower N ≤ M N) ∧
      Tendsto (fun N => finiteScreening (M N) (x N) - fullScreening (x N)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := exists_finiteScreening_cutoffs x lower
    (fun N => 1 / ((N : ℝ) + 1)) (fun _ => by positivity)
  exact ⟨M, fun N => (hM N).1, squeeze_zero_norm
    (fun N => (hM N).2.le) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))⟩

theorem fullScreening_finiteScreening (M : ℕ) (x : ThresholdHilbert) :
    fullScreening (finiteScreening M x) = fullScreening x := by
  rw [finiteScreening_apply, map_sub]
  let z := (mixedSpace (Finset.Icc 2 M)).starProjection x
  have hx : z ∈ mixedClosure :=
    mixedSpace_window_le_closure M ((mixedSpace (Finset.Icc 2 M)).starProjection_apply_mem x)
  have hz : fullScreening z = 0 := by
    change z - mixedClosure.starProjection z = 0
    rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]
  rw [hz, sub_zero]

/-- Full screening converges to a screened target exactly when a finite
mixed cutoff can be chosen for each moving input to reach that target. -/
theorem fullScreening_tendsto_iff_exists_cutoffs (x : ℕ → ThresholdHilbert)
    (lower : ℕ → ℕ) (y : ThresholdHilbert) (hy : fullScreening y = y) :
    Tendsto (fun N => fullScreening (x N)) atTop (𝓝 y) ↔
      ∃ M : ℕ → ℕ, (∀ N, lower N ≤ M N) ∧
        Tendsto (fun N => finiteScreening (M N) (x N)) atTop (𝓝 y) := by
  constructor
  · intro ht
    obtain ⟨M, hM, hd⟩ := exists_finiteScreening_cutoffs_tendsto x lower
    exact ⟨M, hM, by simpa only [sub_add_cancel, zero_add] using hd.add ht⟩
  · rintro ⟨M, _, ht⟩
    simpa only [Function.comp_def, fullScreening_finiteScreening, hy] using
      (fullScreening.continuous.tendsto y).comp ht

/-- Any unit-ball mixed annihilator gives a rigorous lower bound on the
complete squared screening error. -/
theorem mixed_dual_pairing_sq_le (z h : ThresholdHilbert)
    (hh : h ∈ mixedClosureᗮ) (hnorm : ‖h‖ ≤ 1) :
    (inner ℝ z h) ^ 2 ≤ ‖fullScreening z‖ ^ 2 := by
  rw [← fullScreening_inner_right_of_orthogonal z h hh]
  have hC := (abs_real_inner_le_norm (fullScreening z) h).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg (fullScreening z)))
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hC

/-- The bound is attained by a centered mixed annihilator when the input is
centered. No compactness hypothesis on the dual unit ball is needed. -/
theorem exists_centered_mixed_dual_maximizer (z : ThresholdHilbert)
    (hz : inner ℝ z hilbertOne = 0) :
    ∃ h ∈ mixedClosureᗮ, inner ℝ h hilbertOne = 0 ∧ ‖h‖ ≤ 1 ∧
      (inner ℝ z h) ^ 2 = ‖fullScreening z‖ ^ 2 := by
  let v := fullScreening z
  have hv : v ∈ mixedClosureᗮ := fullScreening_mem_orthogonal z
  have hvmean : inner ℝ v hilbertOne = 0 :=
    (fullScreening_inner_right_of_orthogonal _ _ one_mem_mixedClosure_orthogonal).trans hz
  by_cases hn : ‖v‖ = 0
  · exact ⟨0, mixedClosure.orthogonal.zero_mem, by simp, by simp, by simp [← show
      v = fullScreening z from rfl, hn]⟩
  · let h : ThresholdHilbert := ‖v‖⁻¹ • v
    have hh : h ∈ mixedClosureᗮ := mixedClosure.orthogonal.smul_mem _ hv
    refine ⟨h, hh, ?_, ?_, ?_⟩
    · simp [h, real_inner_smul_left, hvmean]
    · change ‖‖v‖⁻¹ • v‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hn]
    · rw [← fullScreening_inner_right_of_orthogonal z h hh]
      change (inner ℝ v (‖v‖⁻¹ • v)) ^ 2 = ‖v‖ ^ 2
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two ‖v‖,
        ← mul_assoc, inv_mul_cancel₀ hn, one_mul, pow_two]

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur CoefficientStabilization RiemannResearch.LinearAlgebra

def centeredInput (N : ℕ) : ThresholdHilbert :=
  primeCombination (window N) (fun _ => 1) - Chebyshev.psi (N : ℝ) • hilbertOne

def offDiagonalCovarianceMass (N M : ℕ) : ℝ := ‖finiteScreening M (centeredInput N)‖ ^ 2

def fullCovarianceMass (N : ℕ) : ℝ := ‖fullScreening (centeredInput N)‖ ^ 2

theorem offDiagonalCovarianceMass_diagonal (N : ℕ) :
    offDiagonalCovarianceMass N N = covarianceMass N := by
  have h1 : finiteScreening N hilbertOne = hilbertOne := by
    rw [finiteScreening_apply, (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (one_mem_mixed_orthogonal _), sub_zero]
  have h2 : finiteScreening N (primeCombination (window N) (fun _ => 1)) =
      screenedCombination (window N) (fun _ => 1) := by
    rw [finiteScreening_apply, screenedCombination, screened_combination, window]
  unfold offDiagonalCovarianceMass centeredInput covarianceMass
  rw [map_sub, map_smul, h1, h2, screenedCovariance_eq, constant_source, one_mul,
    norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq,
    real_inner_smul_right, screenedCombination_inner_one, constant_source, one_mul]
  ring

theorem offDiagonalCovarianceMass_split (N M : ℕ) :
    offDiagonalCovarianceMass N M = fullCovarianceMass N +
      ‖mixedClosure.starProjection (centeredInput N) -
        (mixedSpace (Finset.Icc 2 M)).starProjection (centeredInput N)‖ ^ 2 :=
  finiteScreening_energy_eq_full_add_tail M (centeredInput N)

theorem offDiagonalCovarianceMass_gain (N M L : ℕ) (hML : M ≤ L) :
    offDiagonalCovarianceMass N M = offDiagonalCovarianceMass N L +
      ‖(mixedSpace (Finset.Icc 2 L)).starProjection (centeredInput N) -
        (mixedSpace (Finset.Icc 2 M)).starProjection (centeredInput N)‖ ^ 2 :=
  finiteScreening_energy_split M L hML (centeredInput N)

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan

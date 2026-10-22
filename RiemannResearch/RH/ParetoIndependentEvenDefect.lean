import RiemannResearch.RH.ParetoIndependentEvenRH
import RiemannResearch.RH.IntegerDPPClosure

/-!
# The invariant legal defect of independently corrected sieves

Source: the user's parity-closure continuation, 2026-09-21.
The full legal projection is used throughout. The exact identities connect
the remaining block means with the actual DPP vacancy. They do not prove
that vacancy vanishes, nor assert the existence of an off-line zero.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

/-- A legal lift fixes the entire orthogonal defect, independently of its coefficients. -/
theorem legal_firstPoint_lift_defect (f : ThresholdHilbert) (a : ℝ)
    (hf : f + a • paretoPointHilbert 0 ∈ closedSpace) :
    f - closedSpace.starProjection f =
      -(a • (paretoPointHilbert 0 - closedSpace.starProjection (paretoPointHilbert 0))) := by
  have hp : closedSpace.starProjection (f + a • paretoPointHilbert 0) =
      f + a • paretoPointHilbert 0 :=
    Submodule.starProjection_eq_self_iff.mpr hf
  calc
    f - closedSpace.starProjection f =
      (f + a • paretoPointHilbert 0 -
        closedSpace.starProjection (f + a • paretoPointHilbert 0)) -
        a • (paretoPointHilbert 0 - closedSpace.starProjection (paretoPointHilbert 0)) := by
          rw [map_add, map_smul, smul_sub]
          abel
    _ = _ := by rw [hp, sub_self, zero_sub]

/-- Exact full energy, with the genuine limiting vacancy retained. -/
theorem legal_firstPoint_lift_energy (f : ThresholdHilbert) (a : ℝ)
    (hf : f + a • paretoPointHilbert 0 ∈ closedSpace) :
    ‖f‖^2 = a^2 * IntegerDPP.limitingVacancy / 2 +
      ‖closedSpace.starProjection f‖^2 := by
  have he := nested_projection_energy (⊥ : Submodule ℝ ThresholdHilbert)
    closedSpace bot_le f
  simp only [Submodule.starProjection_bot, zero_apply, sub_zero] at he
  rw [legal_firstPoint_lift_defect f a hf, norm_neg, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at he
  unfold IntegerDPP.limitingVacancy limitingError
  nlinarith [he]

theorem independentlyCorrectedSieve_defect (P m : ℕ) (hP : P ≠ 0) (h3 : 3 ∣ P) :
    independentlyCorrectedSieve P m -
      closedSpace.starProjection (independentlyCorrectedSieve P m) =
      -(oddHeadConstant • (paretoPointHilbert 0 -
        closedSpace.starProjection (paretoPointHilbert 0))) :=
  legal_firstPoint_lift_defect _ _
    (independentlyCorrectedSieve_lift_mem_closedSpace P m hP h3)

/-- All sieve conductors and all independent even corrections retain the same defect. -/
theorem independentlyCorrectedSieve_energy_vacancy (P m : ℕ)
    (hP : P ≠ 0) (h3 : 3 ∣ P) :
    ‖independentlyCorrectedSieve P m‖^2 =
      oddHeadConstant^2 * IntegerDPP.limitingVacancy / 2 +
      ‖closedSpace.starProjection (independentlyCorrectedSieve P m)‖^2 :=
  legal_firstPoint_lift_energy _ _
    (independentlyCorrectedSieve_lift_mem_closedSpace P m hP h3)

/-- The solved contrast term and the actual block means account for the whole defect. -/
theorem independentlyCorrectedSieve_blockMeans_vacancy (P m : ℕ)
    (hP : P ≠ 0) (h3 : 3 ∣ P) :
    ‖dyadicHalfAdjoint (independentlyCorrectedSieve P m)‖^2 +
        fullOddPairContrastEnergy (independentlyCorrectedSieve P m) / 2 =
      oddHeadConstant^2 * IntegerDPP.limitingVacancy / 4 +
        ‖closedSpace.starProjection (independentlyCorrectedSieve P m)‖^2 / 2 := by
  have he := independentlyCorrectedSieve_energy_vacancy P m hP h3
  have hb := zero_head_fullParity_energy_completion _
    (independentlyCorrectedSieve_firstCoordinate P m)
  linarith

theorem independentlyCorrectedSieve_blockMeans_lower (P m : ℕ)
    (hP : P ≠ 0) (h3 : 3 ∣ P) :
    oddHeadConstant^2 * IntegerDPP.limitingVacancy / 4 ≤
      ‖dyadicHalfAdjoint (independentlyCorrectedSieve P m)‖^2 +
        fullOddPairContrastEnergy (independentlyCorrectedSieve P m) / 2 := by
  rw [independentlyCorrectedSieve_blockMeans_vacancy P m hP h3]
  exact le_add_of_nonneg_right (by positivity)

/-- Under not-RH the obstruction is uniform over every choice of the even dictionary size. -/
theorem independentlyCorrectedSieve_uniform_block_floor_of_not_RH
    (h : ¬ RiemannHypothesis) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      oddHeadConstant^2 * IntegerDPP.limitingVacancy / 8 ≤
        ‖dyadicHalfAdjoint (independentlyCorrectedSieve (n+2).factorial m)‖^2 := by
  have hv := IntegerDPP.limitingVacancy_pos_of_not_RH h
  have hc : 0 < oddHeadConstant^2 * IntegerDPP.limitingVacancy / 4 :=
    div_pos (mul_pos (sq_pos_of_pos oddHeadConstant_pos) hv) (by norm_num)
  have ht := independentlyCorrectedSieve_contrast_tendsto (fun _ => 0)
  have he := ht.eventually (gt_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max N 1, ?_⟩
  intro n hn m
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hP := Nat.factorial_ne_zero (n+2)
  have h3 : 3 ∣ (n+2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hs := hN n (le_trans (le_max_left N 1) hn)
  have hcontrast :
      fullOddPairContrastEnergy (independentlyCorrectedSieve (n+2).factorial m) =
        fullOddPairContrastEnergy (independentlyCorrectedSieve (n+2).factorial 0) := by
    rw [independentlyCorrectedSieve_fullContrast _ m hP h3,
      independentlyCorrectedSieve_fullContrast _ 0 hP h3]
  have hb := independentlyCorrectedSieve_blockMeans_lower (n+2).factorial m hP h3
  rw [hcontrast] at hb
  linarith

end RiemannResearch.RH.Pareto

import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.ContractiveRepairFloor

/-!
# Exact mean-one residual and recurrent repair floors

Source: user-provided stringent-condition catalogue, conditions 3 and 15,
2026-09-21. The sharp variance expression follows from the actual closed
projection and Cauchy--Schwarz. The repair consequence uses the actual positive
residual furnished by failure of RH, rather than assuming a variance floor.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem limitProjection_norm_sq :
    ‖limitProjection‖ ^ 2 = 1 - limitEnergy := by
  have hp : limitProjection ∈ closedSpace := closedSpace.starProjection_apply_mem _
  have ho : inner ℝ limitResidual limitProjection = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hp
  change inner ℝ (hilbertOne - limitProjection) limitProjection = 0 at ho
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have he := limitResidual_inner_one
  change inner ℝ (hilbertOne - limitProjection) hilbertOne = limitEnergy at he
  rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at he
  rw [real_inner_comm hilbertOne limitProjection] at he
  linarith

/-- Every exactly mean-one vector in the actual closed legal space satisfies
the sharp variance lower bound `E/(1-E)`. The same hypotheses force `E<1`.
The squared centered norm is the Pareto variance of such a vector. -/
theorem meanOne_variance_limitEnergy_floor (f : ThresholdHilbert)
    (hf : f ∈ closedSpace) (hm : inner ℝ hilbertOne f = 1) :
    limitEnergy < 1 ∧ limitEnergy / (1 - limitEnergy) ≤ ‖f - hilbertOne‖ ^ 2 := by
  have ho : inner ℝ limitResidual f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hf
  change inner ℝ (hilbertOne - limitProjection) f = 0 at ho
  rw [inner_sub_left, hm] at ho
  have hp : inner ℝ limitProjection f = 1 := by linarith
  have hpn : limitProjection ≠ 0 := by
    intro hz
    rw [hz, inner_zero_left] at hp
    norm_num at hp
  have hden : 0 < 1 - limitEnergy := by
    rw [← limitProjection_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hpn)
  have hcs : 1 ≤ ‖limitProjection‖ * ‖f‖ := by
    simpa only [hp, abs_one] using abs_real_inner_le_norm limitProjection f
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
  rw [one_pow, mul_pow, limitProjection_norm_sq] at hsq
  have hm' : inner ℝ f hilbertOne = 1 := by rw [real_inner_comm]; exact hm
  have herr : ‖f - hilbertOne‖ ^ 2 = ‖f‖ ^ 2 - 1 := by
    calc
      ‖f - hilbertOne‖ ^ 2 = inner ℝ (f - hilbertOne) (f - hilbertOne) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ‖f‖ ^ 2 - 1 := by
        simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
          hm, hm', hilbertOne_norm_sq]
        ring
  refine ⟨by linarith, (div_le_iff₀ hden).mpr ?_⟩
  nlinarith

/-- Every legal mean-one orbit requires repairs at the sharp quantitative
floor, stated in cofinal strict-threshold form. The following theorem proves
this threshold strictly positive under failure of RH. No boundedness of the
orbit or its repairs is required. -/
theorem meanOne_repair_cofinally_large
    (P : ThresholdHilbert →L[ℝ] ThresholdHilbert)
    (F : ℕ → ThresholdHilbert) (q : ℝ) (hq : q < 1)
    (hfix : P hilbertOne = hilbertOne)
    (hlegal : ∀ n, F n ∈ closedSpace)
    (hmean : ∀ n, inner ℝ hilbertOne (F n) = 1)
    (hcontract : ∀ x, inner ℝ hilbertOne x = 0 → ‖P x‖ ≤ q * ‖x‖)
    (b : ℝ) (hb : b < (1 - q) * Real.sqrt (limitEnergy / (1 - limitEnergy)))
    (N : ℕ) :
    ∃ n, N ≤ n ∧ b < ‖F (n + 1) - P (F n)‖ := by
  apply RiemannResearch.Analysis.ContractiveRepair.fixedPoint_repair_cofinally_large
    P.toLinearMap (innerSL ℝ hilbertOne).toLinearMap F hilbertOne
    q (Real.sqrt (limitEnergy / (1 - limitEnergy))) b hq hfix
    (by change inner ℝ hilbertOne hilbertOne = 1
        rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq])
    hmean hcontract (fun n => ?_) hb N
  have hfloor := (meanOne_variance_limitEnergy_floor (F n) (hlegal n) (hmean n)).2
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hfloor

/-- The quantitative threshold in the previous theorem is strictly positive
under failure of RH whenever a legal mean-one vector exists. -/
theorem not_RH_meanOne_repair_floor_pos (hRH : ¬ RiemannHypothesis)
    (f : ThresholdHilbert) (hf : f ∈ closedSpace)
    (hm : inner ℝ hilbertOne f = 1) (q : ℝ) (hq : q < 1) :
    0 < (1 - q) * Real.sqrt (limitEnergy / (1 - limitEnergy)) := by
  exact mul_pos (sub_pos.mpr hq) (Real.sqrt_pos.mpr
    (div_pos (not_RH_limitEnergy_pos hRH)
      (sub_pos.mpr (meanOne_variance_limitEnergy_floor f hf hm).1)))

end RiemannResearch.RH.Pareto.CoefficientStabilization

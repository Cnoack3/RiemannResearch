import RiemannResearch.RH.CanonicalMobiusSourceProjection
import RiemannResearch.RH.ReciprocalChargeInnovations
import RiemannResearch.RH.ReciprocalChargeGeometricInnovation

/-!
# Exact comparison of full and tail-screened innovations

Source: direct projection algebra applied to the actual canonical family,
in continuation of LateralArithmeticSynthesis20260924.md. The complete tail
is retained. The exact energy identity transfers the full innovation bound
to the tail denominator through the adjacent first-head error ratio. It does
not prove the arithmetic source accumulation needed for RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

theorem firstTail_screened_orthogonal_finiteSpace (M : ℕ) (hM : 1 ≤ M)
    (f x : ThresholdHilbert) (hx : x ∈ finiteSpace M) :
    inner ℝ (hilbertTailShift x 1)
      (screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) f) = 0 := by
  classical
  rw [← canonicalMobiusSpan_eq_finiteSpace] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    let j : Fin (M - 1 + 1) := ⟨i.val, by omega⟩
    have hj : canonicalWindowIndex 1 M j = i.val + 1 := by
      dsimp [canonicalWindowIndex, j]
      omega
    have he : hilbertTailShift (canonicalMobiusHilbert (i.val + 1)) 1 =
        tailFamily 1 (canonicalWindowIndex 1 M) j := by simp only [tailFamily, hj]
    rw [he, screenedVector, inner_sub_right]
    have hn := congrFun (screeningCoeff_normal
      (tailFamily 1 (canonicalWindowIndex 1 M)) f) j
    change inner ℝ (tailFamily 1 (canonicalWindowIndex 1 M) j)
      (Fintype.linearCombination ℝ (tailFamily 1 (canonicalWindowIndex 1 M))
        (screeningCoeff (tailFamily 1 (canonicalWindowIndex 1 M)) f)) =
      inner ℝ (tailFamily 1 (canonicalWindowIndex 1 M) j) f at hn
    rw [hn, sub_self]
  | zero =>
    change inner ℝ ((hilbertTailShiftLinear 1) 0) _ = 0
    rw [map_zero, inner_zero_left]
  | add x y hx hy hix hiy =>
    change inner ℝ ((hilbertTailShiftLinear 1) (x + y)) _ = 0
    rw [map_add, inner_add_left]
    change inner ℝ (hilbertTailShift x 1) _ + inner ℝ (hilbertTailShift y 1) _ = 0
    rw [hix, hiy, add_zero]
  | smul a x hx hi =>
    change inner ℝ ((hilbertTailShiftLinear 1) (a • x)) _ = 0
    rw [map_smul, real_inner_smul_left]
    change a * inner ℝ (hilbertTailShift x 1) _ = 0
    rw [hi, mul_zero]

/-- The actual full-space residual equals the screened-tail lift minus the
signed source times the actual first-head residual. The lift is represented
without introducing an inverse of the reindexing tail operator. -/
theorem firstHead_full_innovation_energy (M : ℕ) (hM : 1 ≤ M)
    (v : ThresholdHilbert) (hv : hilbertSequence v 1 = 0) :
    ‖v - (finiteSpace M).starProjection v‖ ^ 2 =
      ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M))
        (hilbertTailShift v 1)‖ ^ 2 +
      singleHeadError M *
        (inner ℝ (hilbertTailShift v 1) (windowNormal 1 M (by omega))) ^ 2 := by
  let e := finiteHeadIndicator 1
  let p := (finiteSpace M).starProjection e
  let r := e - p
  let f := hilbertTailShift v 1
  let a := screeningCoeff (tailFamily 1 (canonicalWindowIndex 1 M)) f
  let y := combination (canonicalWindowIndex 1 M) a
  let s := inner ℝ f (windowNormal 1 M (by omega))
  let d := screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) f
  let b := v - y + s • e
  have hs : s = ∑ i, a i := by
    exact screeningCoeff_source (tailFamily 1 (canonicalWindowIndex 1 M)) f
      (normal 1 (canonicalWindowIndex 1 M) (canonicalWindowIndex_pos 1 M (by omega)))
      (normal_equations 1 (canonicalWindowIndex 1 M) _)
  have hy : y ∈ finiteSpace M := canonicalWindow_combination_mem_finiteSpace 1 M hM a
  have hyseq : hilbertSequence y 1 = s := by
    change hilbertSequence (combination (canonicalWindowIndex 1 M) a) 1 = s
    rw [combination_sequence, hs]
    apply Finset.sum_congr rfl
    intro i hi
    rw [canonicalMobiusHead_exact _ 1 (by omega) (canonicalWindowIndex_ge 1 M i), mul_one]
  have hbseq : hilbertSequence b 1 = 0 := by
    change hilbertSequenceLinear (v - y + s • e) 1 = 0
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    change hilbertSequence v 1 - hilbertSequence y 1 + s * hilbertSequence e 1 = 0
    rw [hv, hyseq, finiteHeadIndicator_exact 1 1 (by omega) le_rfl]
    ring
  have hbhead : ∀ n < 1, b n = 0 := by
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    have hw : Real.sqrt (paretoWeight 0) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    change b 0 / Real.sqrt (paretoWeight 0) = 0 at hbseq
    exact (div_eq_zero_iff.mp hbseq).resolve_right hw
  have hbtail : hilbertTailShift b 1 = d := by
    change (hilbertTailShiftLinear 1) (v - y + s • e) = d
    rw [map_add, map_sub, map_smul]
    change hilbertTailShift v 1 - hilbertTailShift y 1 + s • hilbertTailShift e 1 = d
    dsimp [y, e]
    rw [combination_tail, finiteHeadIndicator_tail_zero, smul_zero, add_zero]
    rfl
  have hborth : b ∈ (finiteSpace M)ᗮ := by
    apply ((finiteSpace M).mem_orthogonal b).mpr
    intro x hx
    rw [← hilbertTailShift_inner x b 1 hbhead, hbtail]
    exact firstTail_screened_orthogonal_finiteSpace M hM f x hx
  have hrorth : r ∈ (finiteSpace M)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal e
  have hbp : inner ℝ b p = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace M).mem_orthogonal b).mp hborth p
      ((finiteSpace M).starProjection_apply_mem e)
  have hbr : inner ℝ b r = 0 := by
    change inner ℝ b (e - p) = 0
    rw [inner_sub_right, hbp, sub_zero]
    change inner ℝ b (finiteHeadIndicator 1) = 0
    rw [inner_singleHeadIndicator, hbseq, mul_zero]
  have hz : v - (finiteSpace M).starProjection v = b - s • r := by
    let w := y - s • p
    have hw : w ∈ finiteSpace M := (finiteSpace M).sub_mem hy
      ((finiteSpace M).smul_mem s ((finiteSpace M).starProjection_apply_mem e))
    have ho : v - w ∈ (finiteSpace M)ᗮ := by
      have hh := ((finiteSpace M)ᗮ).sub_mem hborth (((finiteSpace M)ᗮ).smul_mem s hrorth)
      convert hh using 1
      dsimp [w, b, r]
      module
    have hdm : (finiteSpace M).starProjection v - w ∈ finiteSpace M :=
      (finiteSpace M).sub_mem ((finiteSpace M).starProjection_apply_mem v) hw
    have hdo : (finiteSpace M).starProjection v - w ∈ (finiteSpace M)ᗮ := by
      have hh := ((finiteSpace M)ᗮ).sub_mem ho
        (Submodule.sub_starProjection_mem_orthogonal v)
      convert hh using 1
      module
    have hh := ((finiteSpace M).mem_orthogonal _).mp hdo _ hdm
    rw [real_inner_self_eq_norm_sq] at hh
    have heq := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hh))
    rw [heq]
    dsimp [w, b, r]
    module
  have hbnorm : ‖b‖ ^ 2 = ‖d‖ ^ 2 := by
    have hh := hilbertTailShift_inner b b 1 hbhead
    simpa only [hbtail, real_inner_self_eq_norm_sq] using hh.symm
  rw [hz, norm_sub_sq_real, inner_smul_right, hbr, mul_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hbnorm]
  change ‖d‖ ^ 2 - 2 * 0 + s ^ 2 * ‖r‖ ^ 2 = ‖d‖ ^ 2 + ‖r‖ ^ 2 * s ^ 2
  ring

theorem consecutiveResidue_full_tail_screening_energy (M : ℕ) (hM : 1 ≤ M) :
    ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 =
      ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2 +
      singleHeadError M *
        (inner ℝ (windowStepTail 1 M) (windowNormal 1 M (by omega))) ^ 2 :=
  firstHead_full_innovation_energy M hM (consecutiveResidueHilbert M)
    (consecutiveResidueHilbert_head_zero M 1 hM)

/-- The ratio of consecutive first-head errors is exactly the ratio of the
tail-screened innovation energy to its full-space innovation energy. -/
theorem windowStepScreened_energy_eq_full_mul_error_ratio (M : ℕ) (hM : 1 ≤ M) :
    ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2 =
      ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 *
        singleHeadError (M + 1) / singleHeadError M := by
  let D := ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2
  let A := ‖consecutiveResidueHilbert M -
    (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2
  let s := inner ℝ (windowStepTail 1 M) (windowNormal 1 M (by omega))
  let E := singleHeadError M
  let F := singleHeadError (M + 1)
  let K := windowCapacity 1 M (by omega)
  let L := windowCapacity 1 (M + 1) (by omega)
  have hA : A = D + E * s ^ 2 := consecutiveResidue_full_tail_screening_energy M hM
  have hD : D ≠ 0 := ne_of_gt (windowStepScreened_energy_pos 1 M hM)
  have hE : E ≠ 0 := ne_of_gt (singleHeadError_pos M hM)
  have hK : K + 2 ≠ 0 := by
    have hk : 0 < K := capacity_pos _ _ _
    linarith
  have hL : L + 2 ≠ 0 := by
    have hl : 0 < L := capacity_pos _ _ _
    linarith
  have hEK : E * (K + 2) = 1 := by
    rw [show E = (K + 2)⁻¹ from singleHeadError_eq_inv_capacity_add_two M hM]
    exact inv_mul_cancel₀ hK
  have hFL : F * (L + 2) = 1 := by
    rw [show F = (L + 2)⁻¹ from singleHeadError_eq_inv_capacity_add_two (M + 1) (by omega)]
    exact inv_mul_cancel₀ hL
  have hgain : (L - K) * D = s ^ 2 := by
    apply (eq_div_iff hD).mp
    have hg := windowCapacity_succ 1 M (by omega) hM
    rw [windowGain_eq_step_pairing_quotient 1 M (by omega) hM] at hg
    change L = K + s ^ 2 / D at hg
    linarith
  have heq : D * E = A * F := by
    calc
      D * E = D * E * (F * (L + 2)) := by rw [hFL]; ring
      _ = F * (D * (E * (K + 2)) + E * ((L - K) * D)) := by ring
      _ = F * (D + E * s ^ 2) := by rw [hEK, hgain, mul_one]
      _ = A * F := by rw [← hA]; ring
  exact (eq_div_iff hE).mpr heq

/-- An unconditional lower bound for the actual tail-screened denominator,
with the exact adjacent defect ratio retained. -/
theorem windowStepScreened_energy_lower_by_error_ratio (M : ℕ) (hM : 1 ≤ M) :
    singleHeadError (M + 1) / (42 * singleHeadError M) ≤
      ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2 := by
  rw [windowStepScreened_energy_eq_full_mul_error_ratio M hM]
  have hh := mul_le_mul_of_nonneg_right
    (consecutiveResidue_full_innovation_energy_lower M hM)
    (div_nonneg (singleHeadError_pos (M + 1) (by omega)).le
      (singleHeadError_pos M hM).le)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm, one_mul] using hh

/-- The geometric dual certificate transfers to the actual tail denominator,
with its exact adjacent first-head error ratio. -/
theorem windowStepScreened_eventually_gt_error_ratio (c : ℝ)
    (hc : c < Real.pi ^ 2 / 12) :
    ∀ᶠ M : ℕ in atTop,
      c * singleHeadError (M + 1) / singleHeadError M <
        ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2 := by
  filter_upwards [consecutiveResidue_full_innovation_eventually_gt c hc,
    eventually_ge_atTop 1] with M hA hM
  rw [windowStepScreened_energy_eq_full_mul_error_ratio M hM]
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right hA (singleHeadError_pos (M + 1) (by omega)))
    (singleHeadError_pos M hM)

theorem singleHeadError_succ_ratio_tendsto_of_not_density (hd : closedSpace ≠ ⊤) :
    Tendsto (fun M => singleHeadError (M + 1) / singleHeadError M) atTop (𝓝 1) := by
  have he : singleHeadLimitError ≠ 0 :=
    fun h => hd (singleHeadLimitError_eq_zero_iff_density.mp h)
  have hs : Tendsto (fun M : ℕ => M + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with M hM
    omega
  have ht := (singleHeadError_tendsto.comp hs).div singleHeadError_tendsto he
  convert ht using 1
  · funext M
    rfl
  · rw [div_self he]

/-- Failure of density forces a uniform positive lower bound asymptotically
for the actual screened denominator. This is a consequence of failure of RH,
not a contradiction: the signed source can still be square summable. -/
theorem windowStepScreened_eventually_gt_of_not_density (hd : closedSpace ≠ ⊤)
    (c : ℝ) (hc : c < Real.pi ^ 2 / 12) :
    ∀ᶠ M : ℕ in atTop,
      c < ‖screenedVector (tailFamily 1 (canonicalWindowIndex 1 M)) (windowStepTail 1 M)‖ ^ 2 := by
  obtain ⟨b, hcb, hb⟩ := exists_between hc
  have ht : Tendsto (fun M => b * singleHeadError (M + 1) / singleHeadError M)
      atTop (𝓝 b) := by
    simpa only [mul_one, mul_div_assoc] using
      (singleHeadError_succ_ratio_tendsto_of_not_density hd).const_mul b
  have he := (tendsto_order.1 ht).1 c hcb
  filter_upwards [he, windowStepScreened_eventually_gt_error_ratio b hb] with M h1 h2
  exact h1.trans h2

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Density multiplier interactions with normalized floor dilations

Source: the user's dilation/B discussion, 14 November 2026.
B is dQ/dP = (1 + 1/n)/zeta(2), not the historical shifted-reciprocal B.
The coordinate identity retains the full floor correction. The P and Q
adjoints are transported through the actual change of metric. Complete
norm bounds control the density error on dilated ranges; they do not
assert invariance of the legal closure or prove RH.
-/

noncomputable section
namespace RiemannResearch.RH.ParetoDensityDilation
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QDensityMetricInverse

def densityP : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / zetaTwo) • (ContinuousLinearMap.id ℝ ThresholdHilbert + DP)

def normalizedP (m : ℕ) (hm : 0 < m) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertNormalizedDilation m hm).toContinuousLinearMap

def normalizedQ (m : ℕ) (hm : 0 < m) : QHilbert →L[ℝ] QHilbert :=
  Real.sqrt (m : ℝ) • QFloorDilation.floorDilation m hm

theorem densityP_sequence (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence (densityP f) n =
      (1 / zetaTwo) * (hilbertSequence f n + hilbertSequence f n / (n : ℝ)) := by
  change hilbertSequence ((1 / zetaTwo) • (f + DP f)) n = _
  simp only [hilbertSequence_smul, hilbertSequence_add, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, DP_physical]

theorem normalizedP_sequence (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence (normalizedP m hm f) n =
      Real.sqrt (m : ℝ) * hilbertSequence f (n / m) := by
  change hilbertSequence ((1 / Real.sqrt (m : ℝ)) • hilbertDilation m hm f) n = _
  rw [hilbertSequence_smul, hilbertDilation_sequence]
  change (1 / Real.sqrt (m : ℝ)) * ((m : ℝ) * hilbertSequence f (n / m)) = _
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  have hs0 : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hm))
  field_simp
  rw [hs]

theorem normalizedP_norm (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖normalizedP m hm f‖ = ‖f‖ :=
  (hilbertNormalizedDilation m hm).norm_map f


/-- The normalized integer dilations form a multiplicative semigroup. -/
theorem normalizedP_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ThresholdHilbert) :
    normalizedP m hm (normalizedP n hn f) =
      normalizedP (m * n) (Nat.mul_pos hm hn) f := by
  apply hilbertSequence_injective
  funext k
  simp only [normalizedP_sequence, Nat.div_div_eq_div_mul, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m)]
  ring

theorem normalizedP_one (f : ThresholdHilbert) :
    normalizedP 1 Nat.zero_lt_one f = f := by
  apply hilbertSequence_injective
  funext n
  simp only [normalizedP_sequence, Nat.cast_one, Real.sqrt_one, one_mul, Nat.div_one]

theorem normalizedQ_sequence (m : ℕ) (hm : 0 < m) (f : QHilbert) (n : ℕ) :
    qSequence (normalizedQ m hm f) n =
      Real.sqrt (m : ℝ) * qSequence f (n / m) := by
  change qSequenceLinear (Real.sqrt (m : ℝ) • QFloorDilation.floorDilation m hm f) n = _
  rw [map_smul]
  change Real.sqrt (m : ℝ) * qSequence (QFloorDilation.floorDilation m hm f) n = _
  rw [QFloorDilation.floorDilation_sequence]

theorem normalized_toPareto (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    toPareto (normalizedQ m hm f) = normalizedP m hm (toPareto f) := by
  apply hilbertSequence_injective
  funext n
  simp only [toPareto_sequence, normalizedQ_sequence, normalizedP_sequence]

theorem densityP_toPareto (f : QHilbert) :
    densityP (toPareto f) = toPareto (QDensityMetric.B f) := by
  apply hilbertSequence_injective
  funext n
  simp only [densityP_sequence, toPareto_sequence, QDensityMetric.qSequence_B]

theorem density_commutator_sequence (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence (densityP (normalizedP m hm f) -
      normalizedP m hm (densityP f)) n =
      (Real.sqrt (m : ℝ) / zetaTwo) *
        (1 / (n : ℝ) - 1 / ((n / m : ℕ) : ℝ)) *
        hilbertSequence f (n / m) := by
  change hilbertSequenceLinear (densityP (normalizedP m hm f) -
      normalizedP m hm (densityP f)) n = _
  rw [map_sub]
  change hilbertSequence (densityP (normalizedP m hm f)) n -
    hilbertSequence (normalizedP m hm (densityP f)) n = _
  simp only [densityP_sequence, normalizedP_sequence]
  ring

theorem density_adjoint_intertwining (m : ℕ) (hm : 0 < m) (g : QHilbert) :
    toPareto (QDensityMetric.B ((normalizedQ m hm).adjoint g)) =
      (normalizedP m hm).adjoint (toPareto (QDensityMetric.B g)) := by
  apply ext_inner_left ℝ
  intro f
  obtain ⟨q, hq⟩ := paretoEquiv.surjective f
  change toPareto q = f at hq
  subst f
  rw [← q_inner_density, ContinuousLinearMap.adjoint_inner_right,
    q_inner_density, normalized_toPareto, ContinuousLinearMap.adjoint_inner_right]


theorem density_deviation (f : ThresholdHilbert) :
    densityP f - (1 / zetaTwo) • f = (1 / zetaTwo) • DP f := by
  change (1 / zetaTwo) • (f + DP f) - (1 / zetaTwo) • f = _
  rw [smul_add, add_sub_cancel_left]

private theorem norm_le_of_sequence_bound (f g : ThresholdHilbert) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ n, |hilbertSequence f n| ≤ C * |hilbertSequence g n|) :
    ‖f‖ ≤ C * ‖g‖ := by
  have ht (n : ℕ) : positiveWeight n * hilbertSequence f n ^ 2 ≤
      C ^ 2 * (positiveWeight n * hilbertSequence g n ^ 2) := by
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (abs_nonneg _))).mpr (h n)
    simp only [mul_pow, sq_abs] at hs
    have hh := mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg n)
    nlinarith
  have hs : ‖f‖ ^ 2 ≤ C ^ 2 * ‖g‖ ^ 2 := by
    rw [hilbert_norm_weighted_sq, hilbert_norm_weighted_sq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum ht (hilbertSequence_square_summable f)
      ((hilbertSequence_square_summable g).mul_left _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hs)

theorem normalizedP_head_zero (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert)
    (n : ℕ) (hn : n < m) : hilbertSequence (normalizedP m hm f) n = 0 := by
  rw [normalizedP_sequence, Nat.div_eq_of_lt hn, hilbertSequence_zero, mul_zero]


/-- For m > 1 these operators are not unitary operators on the original space. -/
theorem normalizedP_not_surjective (m : ℕ) (hm : 1 < m) :
    ¬ Function.Surjective (normalizedP m (lt_trans Nat.zero_lt_one hm)) := by
  intro h
  obtain ⟨f, hf⟩ := h hilbertOne
  have hz := normalizedP_head_zero m (lt_trans Nat.zero_lt_one hm) f 1 hm
  rw [hf, hilbertOne_sequence] at hz
  norm_num [zeroAnchor] at hz

theorem reciprocal_normalized_norm_le (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖DP (normalizedP m hm f)‖ ≤ (1 / (m : ℝ)) * ‖f‖ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [← normalizedP_norm m hm f]
  apply norm_le_of_sequence_bound _ _ _ (by positivity)
  intro n
  rw [DP_physical, abs_div]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  by_cases hn : n < m
  · rw [normalizedP_head_zero m hm f n hn]
    simp
  · have hmn : (m : ℝ) ≤ n := Nat.cast_le.mpr (Nat.le_of_not_gt hn)
    simpa only [one_div_mul_eq_div] using
      div_le_div_of_nonneg_left (abs_nonneg (hilbertSequence (normalizedP m hm f) n))
        hmR hmn

theorem density_normalized_error_norm_le (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖densityP (normalizedP m hm f) - (1 / zetaTwo) • normalizedP m hm f‖ ≤
      (1 / (zetaTwo * (m : ℝ))) * ‖f‖ := by
  rw [density_deviation, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (one_div_pos.mpr zetaTwo_pos))]
  have h := mul_le_mul_of_nonneg_left (reciprocal_normalized_norm_le m hm f)
    (le_of_lt (one_div_pos.mpr zetaTwo_pos))
  calc
    _ ≤ (1 / zetaTwo) * ((1 / (m : ℝ)) * ‖f‖) := h
    _ = _ := by ring

theorem adjoint_density_formula (m : ℕ) (hm : 0 < m) (g : QHilbert) :
    (normalizedQ m hm).adjoint g =
      inverse (toQ ((normalizedP m hm).adjoint (toPareto (QDensityMetric.B g)))) := by
  have h := congrArg toQ (density_adjoint_intertwining m hm g)
  rw [toQ_toPareto] at h
  rw [← h, inverse_B]


theorem normalizedP_adjoint_left_inverse (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    (normalizedP m hm).adjoint (normalizedP m hm f) = f := by
  have h := congrArg (fun T : ThresholdHilbert →L[ℝ] ThresholdHilbert => T f)
    (hilbertNormalizedDilation m hm).adjoint_comp_self
  simpa only [normalizedP, ContinuousLinearMap.comp_apply,
    one_apply_eq_self] using h

theorem normalizedP_adjoint_norm_le (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖(normalizedP m hm).adjoint f‖ ≤ ‖f‖ := by
  have he : ‖(normalizedP m hm).adjoint f‖ ^ 2 =
      inner ℝ (normalizedP m hm ((normalizedP m hm).adjoint f)) f := by
    rw [← real_inner_self_eq_norm_sq, ContinuousLinearMap.adjoint_inner_right]
  have hb := real_inner_le_norm
    (normalizedP m hm ((normalizedP m hm).adjoint f)) f
  rw [normalizedP_norm, ← he] at hb
  nlinarith [norm_nonneg ((normalizedP m hm).adjoint f), norm_nonneg f]

theorem compressed_density_error_norm_le (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖(normalizedP m hm).adjoint (densityP (normalizedP m hm f)) -
      (1 / zetaTwo) • f‖ ≤ (1 / (zetaTwo * (m : ℝ))) * ‖f‖ := by
  have he : (normalizedP m hm).adjoint
      (densityP (normalizedP m hm f) - (1 / zetaTwo) • normalizedP m hm f) =
      (normalizedP m hm).adjoint (densityP (normalizedP m hm f)) -
        (1 / zetaTwo) • f := by
    rw [map_sub, map_smul, normalizedP_adjoint_left_inverse]
  rw [← he]
  exact (normalizedP_adjoint_norm_le m hm _).trans
    (density_normalized_error_norm_le m hm f)

theorem compressed_density_opNorm_le (m : ℕ) (hm : 0 < m) :
    ‖(normalizedP m hm).adjoint.comp (densityP.comp (normalizedP m hm)) -
      (1 / zetaTwo) • ContinuousLinearMap.id ℝ ThresholdHilbert‖ ≤
        1 / (zetaTwo * (m : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [zetaTwo_pos])
  exact compressed_density_error_norm_le m hm


/-- B transports the Q-orthogonal complement to the P-orthogonal complement. -/
theorem density_orthogonal_transport_iff (S : Submodule ℝ QHilbert) (f : QHilbert) :
    f ∈ Sᗮ ↔
      toPareto (QDensityMetric.B f) ∈ (S.map toParetoCLM.toLinearMap)ᗮ := by
  constructor
  · intro h
    apply ((S.map toParetoCLM.toLinearMap).mem_orthogonal _).mpr
    rintro g ⟨q, hq, rfl⟩
    change inner ℝ (toPareto q) (toPareto (QDensityMetric.B f)) = 0
    rw [← q_inner_density]
    exact Submodule.inner_right_of_mem_orthogonal hq h
  · intro h
    apply (S.mem_orthogonal _).mpr
    intro q hq
    rw [q_inner_density]
    exact Submodule.inner_right_of_mem_orthogonal
      (show toPareto q ∈ S.map toParetoCLM.toLinearMap from ⟨q, hq, rfl⟩) h

theorem density_orthogonal_transport (S : Submodule ℝ QHilbert) :
    Sᗮ.map (toParetoCLM.comp QDensityMetric.B).toLinearMap =
      (S.map toParetoCLM.toLinearMap)ᗮ := by
  apply le_antisymm
  · rintro f ⟨q, hq, rfl⟩
    exact (density_orthogonal_transport_iff S q).mp hq
  · intro f hf
    refine ⟨inverse (toQ f), ?_, ?_⟩
    · apply (density_orthogonal_transport_iff S _).mpr
      simpa only [B_inverse, toPareto_toQ] using hf
    · change toPareto (QDensityMetric.B (inverse (toQ f))) = f
      rw [B_inverse, toPareto_toQ]

#print axioms density_orthogonal_transport
#print axioms density_commutator_sequence
#print axioms adjoint_density_formula
#print axioms compressed_density_opNorm_le

end RiemannResearch.RH.ParetoDensityDilation

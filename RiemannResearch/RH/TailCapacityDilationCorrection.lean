import RiemannResearch.RH.MobiusResidualFirstCoordinate

/-!
# Exact legal dilation corrections for the first-coordinate constraint

Source: user-provided `RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 17, for the statements and proof strategy. The correction applies to the
actual weighted Hilbert space and retains its full infinite norm. Its exact gain
does not supply a lower bound for the accumulated arithmetic correlations.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

/-- The paper's unscaled dilation, as a linear map on the actual Pareto space. -/
def unscaledResidueDilation (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →ₗ[ℝ] ThresholdHilbert :=
  (1 / (m : ℝ)) • hilbertDilationLinear m hm

theorem unscaledResidueDilation_sequence (m : ℕ) (hm : 0 < m)
    (F : ThresholdHilbert) (k : ℕ) :
    hilbertSequence (unscaledResidueDilation m hm F) k = hilbertSequence F (k / m) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  change hilbertSequence ((1 / (m : ℝ)) • hilbertDilation m hm F) k = _
  rw [hilbertSequence_smul, hilbertDilation_sequence]
  simp only [Pi.smul_apply, smul_eq_mul, dilation]
  field_simp [hm0]

theorem unscaledResidueDilation_norm_sq (m : ℕ) (hm : 0 < m)
    (F : ThresholdHilbert) :
    ‖unscaledResidueDilation m hm F‖ ^ 2 = ‖F‖ ^ 2 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  change ‖(1 / (m : ℝ)) • hilbertDilation m hm F‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertDilation_norm_sq]
  field_simp [hm0]

/-- The norm factor of the unscaled physical pullback. -/
theorem unscaledResidueDilation_norm (k : ℕ) (hk : 0 < k) (x : ThresholdHilbert) :
    ‖unscaledResidueDilation k hk x‖ = (1 / Real.sqrt k) * ‖x‖ := by
  calc
    _ = Real.sqrt (‖unscaledResidueDilation k hk x‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2 / (k : ℝ)) := by rw [unscaledResidueDilation_norm_sq]
    _ = ‖x‖ / Real.sqrt k := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ = _ := by ring

theorem unscaledResidueDilation_firstCoordinate (m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) :
    hilbertSequence (unscaledResidueDilation m (by omega) F) 1 = 0 := by
  rw [unscaledResidueDilation_sequence, Nat.div_eq_of_lt (by omega)]
  exact hilbertSequence_zero F

theorem unscaledResidueDilation_residueAtom (m : ℕ) (hm : 0 < m) (i : ℕ) :
    unscaledResidueDilation m hm (residueAtom i) =
      normalizedResidueHilbert (m * (i + 2)) (by positivity) -
        (1 / ((i + 2 : ℕ) : ℝ)) • normalizedResidueHilbert m hm := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hc1 : (1 / (m : ℝ)) * (m : ℝ) = 1 := by field_simp [hm0]
  have hc2 : (1 / (m : ℝ)) * ((m : ℝ) / ((i + 2 : ℕ) : ℝ)) =
      1 / ((i + 2 : ℕ) : ℝ) := by
    calc
      _ = ((1 / (m : ℝ)) * (m : ℝ)) / ((i + 2 : ℕ) : ℝ) := by ring
      _ = _ := by rw [hc1]
  change (1 / (m : ℝ)) • hilbertDilation m hm (residueAtom i) = _
  rw [hilbertDilation_residueAtom]
  simp only [smul_sub, smul_smul, hc1, hc2, one_smul]

theorem residueCombination_firstCoordinate (n : ℕ) (a : Fin n → ℝ) :
    hilbertSequence (∑ j : Fin n, a j • residueAtom j.val) 1 =
      ∑ j : Fin n, a j / ((j.val + 2 : ℕ) : ℝ) := by
  have hcoord (j : Fin n) : hilbertSequenceLinear (residueAtom j.val) 1 =
      1 / ((j.val + 2 : ℕ) : ℝ) := by
    change hilbertSequence (residueAtom j.val) 1 = _
    rw [residueAtom, normalizedResidueHilbert_sequence]
    have hmod : 1 % (j.val + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    simp [residueFraction, hmod]
  change (hilbertSequenceLinear (∑ j : Fin n, a j • residueAtom j.val)) 1 = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcoord]
  simp only [div_eq_mul_inv, one_mul]

/-- Exact finite coefficient identity. No independent probabilistic atoms are introduced. -/
theorem unscaledResidueDilation_combination (n m : ℕ) (hm : 0 < m)
    (a : Fin n → ℝ) :
    unscaledResidueDilation m hm (∑ j : Fin n, a j • residueAtom j.val) =
      (∑ j : Fin n, a j • normalizedResidueHilbert (m * (j.val + 2)) (by positivity)) -
        (∑ j : Fin n, a j / ((j.val + 2 : ℕ) : ℝ)) • normalizedResidueHilbert m hm := by
  rw [map_sum]
  simp_rw [map_smul, unscaledResidueDilation_residueAtom, smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  simp only [div_eq_mul_inv, one_mul]

theorem unscaledResidueDilation_normalized_combination (n m : ℕ) (hm : 0 < m)
    (a : Fin n → ℝ)
    (hhead : hilbertSequence (∑ j : Fin n, a j • residueAtom j.val) 1 = 1) :
    unscaledResidueDilation m hm (∑ j : Fin n, a j • residueAtom j.val) =
      (∑ j : Fin n, a j • normalizedResidueHilbert (m * (j.val + 2)) (by positivity)) -
        normalizedResidueHilbert m hm := by
  rw [residueCombination_firstCoordinate] at hhead
  rw [unscaledResidueDilation_combination, hhead, one_smul]

theorem normalizedResidue_mem_finiteSpace (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n + 1) :
    normalizedResidueHilbert d (by omega) ∈ finiteSpace n := by
  have hind : d - 2 < n := by omega
  have he : d - 2 + 2 = d := by omega
  apply Submodule.subset_span
  exact ⟨⟨d - 2, hind⟩, by simp only [id_eq, residueAtom, he]⟩

/-- The old maximum modulus is n+1; after dilation it is m*(n+1). -/
theorem unscaledResidueDilation_mem_finiteSpace (n m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) (hF : F ∈ finiteSpace n) :
    unscaledResidueDilation m (by omega) F ∈ finiteSpace (m * (n + 1) - 1) := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n F hF
  rw [map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul, unscaledResidueDilation_residueAtom]
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · apply normalizedResidue_mem_finiteSpace
    · nlinarith
    · have hjn : j.val + 2 ≤ n + 1 := by omega
      have hmul := Nat.mul_le_mul_left m hjn
      have hpos : 1 ≤ m * (n + 1) := by nlinarith
      omega
  · apply Submodule.smul_mem
    apply normalizedResidue_mem_finiteSpace
    · exact hm
    · have hpos : 1 ≤ m * (n + 1) := by nlinarith
      have hbound : m ≤ m * (n + 1) := by
        simpa only [Nat.mul_one] using
          Nat.mul_le_mul_left m (show 1 ≤ n + 1 by omega)
      omega

theorem firstCoordinate_one_norm_sq_pos (F : ThresholdHilbert)
    (hhead : hilbertSequence F 1 = 1) : 0 < ‖F‖ ^ 2 := by
  have hF : F ≠ 0 := by
    intro hz
    rw [hz] at hhead
    simp [hilbertSequence] at hhead
  exact sq_pos_of_pos (norm_pos_iff.mpr hF)

/-- The explicit scalar minimizing the norm along the unscaled dilation direction. -/
def dilationCorrection (m : ℕ) (hm : 0 < m) (F : ThresholdHilbert) : ThresholdHilbert :=
  F - (((m : ℝ) * inner ℝ F (unscaledResidueDilation m hm F)) / ‖F‖ ^ 2) •
    unscaledResidueDilation m hm F

theorem dilationCorrection_firstCoordinate (m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) (hhead : hilbertSequence F 1 = 1) :
    hilbertSequence (dilationCorrection m (by omega) F) 1 = 1 := by
  change (hilbertSequenceLinear (F - _)) 1 = _
  rw [map_sub, map_smul]
  change hilbertSequence F 1 - _ *
    hilbertSequence (unscaledResidueDilation m _ F) 1 = 1
  rw [hhead, unscaledResidueDilation_firstCoordinate m hm]
  ring

theorem dilationCorrection_mem_finiteSpace (n m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) (hF : F ∈ finiteSpace n) :
    dilationCorrection m (by omega) F ∈ finiteSpace (m * (n + 1) - 1) := by
  have hindex : n ≤ m * (n + 1) - 1 := by
    have hpos : n + 1 ≤ m * (n + 1) := by nlinarith
    omega
  apply Submodule.sub_mem
  · exact walkSpan_mono residueAtom id hindex hF
  · exact Submodule.smul_mem _ _ (unscaledResidueDilation_mem_finiteSpace n m hm F hF)

/-- The gain is the square of the actual signed correlation with the dilation. -/
theorem dilationCorrection_norm_sq (m : ℕ) (hm : 0 < m)
    (F : ThresholdHilbert) (hhead : hilbertSequence F 1 = 1) :
    ‖dilationCorrection m hm F‖ ^ 2 = ‖F‖ ^ 2 -
      (m : ℝ) * (inner ℝ F (unscaledResidueDilation m hm F)) ^ 2 / ‖F‖ ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hnorm : ‖F‖ ^ 2 ≠ 0 := ne_of_gt (firstCoordinate_one_norm_sq_pos F hhead)
  have hnorm0 : ‖F‖ ≠ 0 := by
    intro hz
    apply hnorm
    rw [hz]
    norm_num
  unfold dilationCorrection
  rw [sub_eq_add_neg, norm_add_sq_real]
  simp only [norm_neg, inner_neg_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, real_inner_smul_right]
  rw [unscaledResidueDilation_norm_sq]
  field_simp [hm0, hnorm0]
  ring

/-- Subtracting the unchanged physical first-coordinate energy gives Section 17.2. -/
theorem dilationCorrection_tail_energy (m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) (hhead : hilbertSequence F 1 = 1) :
    ‖dilationCorrection m (by omega) F‖ ^ 2 - 1 / 2 = (‖F‖ ^ 2 - 1 / 2) -
      (m : ℝ) * (inner ℝ F (unscaledResidueDilation m (by omega) F)) ^ 2 / ‖F‖ ^ 2 := by
  rw [dilationCorrection_norm_sq m (by omega) F hhead]
  ring

theorem dilationCorrection_strict_improvement (m : ℕ) (hm : 0 < m)
    (F : ThresholdHilbert) (hhead : hilbertSequence F 1 = 1)
    (hc : inner ℝ F (unscaledResidueDilation m hm F) ≠ 0) :
    ‖dilationCorrection m hm F‖ ^ 2 < ‖F‖ ^ 2 := by
  rw [dilationCorrection_norm_sq m hm F hhead]
  have hgain : 0 < (m : ℝ) * (inner ℝ F (unscaledResidueDilation m hm F)) ^ 2 /
      ‖F‖ ^ 2 :=
    div_pos (mul_pos (by positivity) (sq_pos_of_ne_zero hc))
      (firstCoordinate_one_norm_sq_pos F hhead)
  linarith

/-- Reciprocal-capacity gain from a certified nonnegative energy improvement.
The hypothesis comparing the next true minimum to the trial energy is explicit. -/
theorem reciprocal_capacity_gain (ε εnext η : ℝ)
    (hnext : 0 < εnext) (hη : 0 ≤ η) (htrial : εnext ≤ ε - η) :
    η / ε ^ 2 ≤ η / (ε * (ε - η)) ∧
      η / (ε * (ε - η)) ≤ 1 / εnext - 1 / ε := by
  have hremain : 0 < ε - η := lt_of_lt_of_le hnext htrial
  have hε : 0 < ε := by linarith
  have hidentity : 1 / (ε - η) - 1 / ε = η / (ε * (ε - η)) := by
    field_simp [ne_of_gt hε, ne_of_gt hremain]
    ring
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos hε) (mul_pos hε hremain)).mpr
    apply mul_le_mul_of_nonneg_left _ hη
    nlinarith [mul_nonneg (le_of_lt hε) hη]
  · have hrecip : 1 / (ε - η) ≤ 1 / εnext :=
      one_div_le_one_div_of_le hnext htrial
    linarith

/-- Actual-dilation specialization of the lower capacity gain in Section 17.3.
For a true next constrained minimum, `htrial` follows by evaluating this legal witness. -/
theorem dilationCorrection_capacity_gain (m : ℕ) (hm : 2 ≤ m)
    (F : ThresholdHilbert) (hhead : hilbertSequence F 1 = 1)
    (εnext : ℝ) (hnext : 0 < εnext)
    (htrial : εnext ≤ ‖dilationCorrection m (by omega) F‖ ^ 2 - 1 / 2) :
    (m : ℝ) / ‖F‖ ^ 2 *
        (inner ℝ F (unscaledResidueDilation m (by omega) F) / (‖F‖ ^ 2 - 1 / 2)) ^ 2 ≤
      1 / εnext - 1 / (‖F‖ ^ 2 - 1 / 2) := by
  let η : ℝ := (m : ℝ) * (inner ℝ F (unscaledResidueDilation m (by omega) F)) ^ 2 /
    ‖F‖ ^ 2
  have hη : 0 ≤ η := by
    dsimp [η]
    positivity
  have htrial' : εnext ≤ (‖F‖ ^ 2 - 1 / 2) - η := by
    simpa only [dilationCorrection_tail_energy m hm F hhead] using htrial
  obtain ⟨hlower, hgain⟩ := reciprocal_capacity_gain (‖F‖ ^ 2 - 1 / 2) εnext η
    hnext hη htrial'
  have hε : 0 < ‖F‖ ^ 2 - 1 / 2 := by linarith
  have hnorm0 : ‖F‖ ≠ 0 := by
    intro hz
    have hnorm := firstCoordinate_one_norm_sq_pos F hhead
    rw [hz] at hnorm
    norm_num at hnorm
  have heq : (m : ℝ) / ‖F‖ ^ 2 *
      (inner ℝ F (unscaledResidueDilation m (by omega) F) / (‖F‖ ^ 2 - 1 / 2)) ^ 2 =
      η / (‖F‖ ^ 2 - 1 / 2) ^ 2 := by
    dsimp [η]
    field_simp [hnorm0, ne_of_gt hε]
  rw [heq]
  exact hlower.trans hgain

end RiemannResearch.RH.Pareto.CoefficientStabilization

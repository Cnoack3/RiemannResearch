import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ParetoLegalStructure

/-!
# The first-coordinate target and the actual RH bridge

Source: `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`.
The point target is the actual Pareto vector supported at physical index one.
Its membership in the closed legal space is equivalent to that of the constant
target. This proves the fixed-head approximation-to-RH direction; no converse
from RH or arithmetic convergence estimate is assumed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

theorem paretoPoint_zero_eq_one_sub_dyadic :
    paretoPointHilbert 0 = hilbertOne - (1 / 2 : ℝ) •
      hilbertDilation 2 (by norm_num) hilbertOne := by
  apply hilbertSequence_injective
  rw [show hilbertSequence (hilbertOne - (1 / 2 : ℝ) •
      hilbertDilation 2 (by norm_num) hilbertOne) =
      hilbertSequence hilbertOne - hilbertSequence ((1 / 2 : ℝ) •
      hilbertDilation 2 (by norm_num) hilbertOne) from
      hilbertSequenceLinear.map_sub _ _]
  rw [hilbertSequence_paretoPoint, hilbertSequence_smul,
    hilbertDilation_sequence, hilbertOne_sequence]
  funext k
  by_cases hk : k = 0
  · simp [hk, paretoPointSequence, dilation, zeroAnchor]
  by_cases hk1 : k = 1
  · simp [hk1, paretoPointSequence, dilation, zeroAnchor]
  have hd : k / 2 ≠ 0 := by omega
  simp [paretoPointSequence, dilation, zeroAnchor, hk, hk1, hd]

/-- The dyadic tail operator is strictly contractive in the original norm. -/
theorem dyadic_half_operator_norm_lt_one :
    ‖(1 / 2 : ℝ) • hilbertDilationContinuous 2 (by norm_num)‖ < 1 := by
  apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 3 / 4) ?_) (by norm_num)
  intro f
  have hs := hilbertDilation_norm_sq 2 (by norm_num) f
  have hn : 0 ≤ ‖hilbertDilation 2 (by norm_num) f‖ := norm_nonneg _
  have hf : 0 ≤ ‖f‖ := norm_nonneg _
  simp only [smul_apply, hilbertDilationContinuous_apply,
    norm_smul, Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Nat.cast_ofNat] at *
  nlinarith

/-- Fixed-head and constant-target approximation have precisely the same
closure obstruction, for any dilation-invariant legal seed space. -/
theorem paretoPoint_zero_mem_legalClosure_iff (A : Set ℕ) :
    paretoPointHilbert 0 ∈ hilbertLegalClosure A ↔
      hilbertOne ∈ hilbertLegalClosure A := by
  constructor
  · intro he
    let U : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
      (1 / 2 : ℝ) • hilbertDilationContinuous 2 (by norm_num)
    have hU : ‖U‖ < 1 := dyadic_half_operator_norm_lt_one
    have hstable (f : ThresholdHilbert) (hf : f ∈ hilbertLegalClosure A) :
        U f ∈ hilbertLegalClosure A :=
      (hilbertLegalClosure A).smul_mem _
        (hilbertLegalClosure_dilation A hf 2 (by norm_num))
    have hid : hilbertOne - U hilbertOne = paretoPointHilbert 0 :=
      paretoPoint_zero_eq_one_sub_dyadic.symm
    have hm (n : ℕ) : hilbertOne - (U ^ n) hilbertOne ∈ hilbertLegalClosure A := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hh := (hilbertLegalClosure A).add_mem he (hstable _ ih)
        rw [map_sub, ← hid] at hh
        rw [pow_succ', mul_apply_eq_comp]
        convert hh using 1; abel
    have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hU
    have hn : Tendsto (fun n => ‖(U ^ n) hilbertOne‖) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (show Tendsto (fun n => ‖U ^ n‖ * ‖hilbertOne‖) atTop (𝓝 0) by
          simpa using hp.norm.mul_const ‖hilbertOne‖)
      · intro n; exact norm_nonneg _
      · intro n; exact (U ^ n).le_opNorm hilbertOne
    have ht : Tendsto (fun n => (U ^ n) hilbertOne) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hn)
    have hlim : Tendsto (fun n => hilbertOne - (U ^ n) hilbertOne) atTop
        (𝓝 hilbertOne) := by
      simpa using tendsto_const_nhds.sub ht
    exact (hilbertLegalSubspace A).isClosed_topologicalClosure.mem_of_tendsto
      hlim (Eventually.of_forall hm)
  · intro h
    rw [paretoPoint_zero_eq_one_sub_dyadic]
    exact (hilbertLegalClosure A).sub_mem h ((hilbertLegalClosure A).smul_mem _
      (hilbertLegalClosure_dilation A h 2 (by norm_num)))

/-- No finite legal packet equals the point target: its positive period would
repeat the nonzero first coordinate. -/
theorem paretoPoint_zero_not_mem_legalSubspace (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    paretoPointHilbert 0 ∉ hilbertLegalSubspace A := by
  intro he
  obtain ⟨d, hd, hp⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA he
  have h := (hp d (dvd_refl d)).1 1
  change hilbertSequence (paretoPointHilbert 0) (1 + d) =
    hilbertSequence (paretoPointHilbert 0) 1 at h
  rw [hilbertSequence_paretoPoint] at h
  have hne : 1 + d ≠ 1 := by omega
  norm_num [paretoPointSequence, hne] at h
  omega

theorem riemannHypothesis_of_paretoPoint_zero_mem_legalClosure
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (he : paretoPointHilbert 0 ∈ hilbertLegalClosure A) : RiemannHypothesis :=
  riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
    ((paretoPoint_zero_mem_legalClosure_iff A).mp he)

end RiemannResearch.RH.Pareto

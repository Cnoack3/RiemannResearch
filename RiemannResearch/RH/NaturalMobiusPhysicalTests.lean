import RiemannResearch.RH.HardyMobiusFamily
import RiemannResearch.RH.CanonicalMobiusPNT
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Physical tests of the raw Möbius residual

Source: `InverseGramCorrectionAttempt20260923.md`, exact-head and domination
steps. The pairing limit below is proved for an explicit summable physical
test class. Periodic residue generators do not belong to that class, so this
does not discharge their fixed Gram-source limit. The missing periodic
summation-by-parts and logarithm-weighted Möbius mean are kept separate.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

theorem rawMobiusHilbert_sequence (N : ℕ) :
    hilbertSequence (rawMobiusHilbert N) =
      fun k => -(∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d k) := by
  change hilbertSequenceLinear (rawMobiusHilbert N) = _
  unfold rawMobiusHilbert
  simp only [map_neg, map_sum, map_smul]
  change -(∑ d ∈ (Finset.Icc 1 N).attach,
      (ArithmeticFunction.moebius (d : ℕ) : ℝ) •
        hilbertSequence (normalizedResidueHilbert d (Finset.mem_Icc.mp d.property).1)) = _
  simp_rw [normalizedResidueHilbert_sequence]
  funext k
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [Finset.sum_attach (Finset.Icc 1 N)
    (fun d : ℕ => (ArithmeticFunction.moebius d : ℝ) * residueFraction d k)]

/-- Exact positive physical coordinates, including the complete tail. -/
theorem rawMobiusResidual_sequence (N k : ℕ) (hk : 0 < k) :
    hilbertSequence (hilbertOne - rawMobiusHilbert N) k =
      1 + ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d k := by
  have hs := congrFun (hilbertSequenceLinear.map_sub hilbertOne (rawMobiusHilbert N)) k
  change hilbertSequence (hilbertOne - rawMobiusHilbert N) k =
    hilbertSequence hilbertOne k - hilbertSequence (rawMobiusHilbert N) k at hs
  rw [hs, hilbertOne_sequence, rawMobiusHilbert_sequence]
  simp [zeroAnchor, ne_of_gt hk]

/-- The head is exactly the reciprocal Möbius sum multiplied by the index. -/
theorem rawMobiusResidual_head (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    hilbertSequence (hilbertOne - rawMobiusHilbert N) k =
      (k : ℝ) * mobiusReciprocalSum N := by
  rw [rawMobiusResidual_sequence N k hk, mobius_residue_prefix_identity N k hk hkN]
  ring

/-- Every fixed physical coordinate tends to zero, using the proved PNT provider. -/
theorem rawMobiusResidual_coordinate_tendsto_zero (k : ℕ) :
    Tendsto (fun N => hilbertSequence (hilbertOne - rawMobiusHilbert N) k)
      atTop (𝓝 0) := by
  by_cases hk : k = 0
  · simp [hk]
  have ht : Tendsto (fun N => (k : ℝ) * mobiusReciprocalSum N) atTop (𝓝 0) := by
    simpa using mobiusReciprocalSum_tendsto_zero.const_mul (k : ℝ)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with N hN
  exact (rawMobiusResidual_head N k (Nat.pos_of_ne_zero hk) hN).symm

/-- A uniform bound at every positive cutoff, without using PNT. -/
theorem rawMobiusResidual_abs_le_cutoff (N : ℕ) (hN : 0 < N) (k : ℕ) :
    |hilbertSequence (hilbertOne - rawMobiusHilbert N) k| ≤ (N : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  rw [rawMobiusResidual_sequence N k (Nat.pos_of_ne_zero hk)]
  have hb := finite_mobius_sum_abs N hN (fun d => residueFraction d k) 1
    (by simp [residueFraction, Nat.mod_one])
    (fun d hd => residueFraction_abs_le_one d k (Finset.mem_Icc.mp hd).1)
  have ha := abs_add_le (1 : ℝ)
    (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * residueFraction d k)
  norm_num at ha
  linarith

/-- The stronger global domination has constant one, not an unspecified PNT bound. -/
theorem rawMobiusResidual_abs_le_index (N : ℕ) (hN : 0 < N) (k : ℕ) :
    |hilbertSequence (hilbertOne - rawMobiusHilbert N) k| ≤ (k : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hkN : k ≤ N
  · rw [rawMobiusResidual_head N k (Nat.pos_of_ne_zero hk) hkN, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg k)]
    have hb := mul_le_mul_of_nonneg_left (mobiusReciprocalSum_abs_le_one N hN)
      (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    simpa using hb
  · exact (rawMobiusResidual_abs_le_cutoff N hN k).trans (by exact_mod_cast (by omega : N ≤ k))

/-- Unconditional convergence against tests with a summable first physical moment.
The explicit hypothesis is stronger than Hilbert membership; in particular,
this theorem cannot be applied to a residue generator merely because it is bounded. -/
theorem rawMobiusResidual_inner_tendsto_of_summable_test
    (f : ThresholdHilbert)
    (hf : Summable (fun k => positiveWeight k * (k : ℝ) * |hilbertSequence f k|)) :
    Tendsto (fun N => inner ℝ (hilbertOne - rawMobiusHilbert N) f) atTop (𝓝 0) := by
  have hp : ∀ k, Tendsto
      (fun N => positiveWeight k *
        (hilbertSequence (hilbertOne - rawMobiusHilbert N) k * hilbertSequence f k))
      atTop (𝓝 0) := by
    intro k
    simpa using ((rawMobiusResidual_coordinate_tendsto_zero k).mul_const
      (hilbertSequence f k)).const_mul (positiveWeight k)
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k,
      ‖positiveWeight k *
        (hilbertSequence (hilbertOne - rawMobiusHilbert N) k * hilbertSequence f k)‖ ≤
      positiveWeight k * (k : ℝ) * |hilbertSequence f k| := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    have hw : 0 ≤ positiveWeight k := by unfold positiveWeight; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ positiveWeight k * ((k : ℝ) * |hilbertSequence f k|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (rawMobiusResidual_abs_le_index N hN k)
            (abs_nonneg _)) hw
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence hf hp hb
  simpa only [hilbert_inner_weighted, paretoInner, tsum_zero] using ht

end RiemannResearch.RH.Pareto

import RiemannResearch.RH.ArgumentDoublingGenerators

/-!
# Whole dyadic carry blocks

Continuation of the user-supplied odd-carry handoff, 2026-09-20.
The sampled residues converge unconditionally. Approximability of the entire
carry block, which is the substantive new hypothesis below, remains open.
Source: user-provided odd-carry/DPP continuation and the exact argument-doubling
identities in ArgumentDoublingGenerators. No mathematical novelty is claimed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

def argumentDoublingIterate (k : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  (argumentDoublingContinuous : ThresholdHilbert → ThresholdHilbert)^[k] f

@[simp] theorem argumentDoublingIterate_zero (f : ThresholdHilbert) :
    argumentDoublingIterate 0 f = f := rfl

theorem argumentDoublingIterate_succ (k : ℕ) (f : ThresholdHilbert) :
    argumentDoublingIterate (k + 1) f =
      argumentDoublingContinuous (argumentDoublingIterate k f) := by
  exact Function.iterate_succ_apply' _ _ _

@[simp] theorem argumentDoublingIterate_sequence (k : ℕ) (f : ThresholdHilbert) :
    hilbertSequence (argumentDoublingIterate k f) =
      fun n => hilbertSequence f (2 ^ k * n) := by
  induction k with
  | zero => simp [argumentDoublingIterate]
  | succ k ih =>
    rw [argumentDoublingIterate_succ, argumentDoublingContinuous_apply,
      hilbertArgumentDoubling_sequence, ih]
    funext n
    simp only [pow_succ, Nat.mul_assoc]

/-- The entire unnormalized block of k successive doubling carries. -/
def dyadicCarryBlock (k d : ℕ) (hd : 0 < d) : ThresholdHilbert :=
  (2 : ℝ) ^ k • normalizedResidueHilbert d hd -
    argumentDoublingIterate k (normalizedResidueHilbert d hd)

@[simp] theorem dyadicCarryBlock_zero (d : ℕ) (hd : 0 < d) :
    dyadicCarryBlock 0 d hd = 0 := by
  simp [dyadicCarryBlock]

/-- This recurrence retains every transformed carry; no invariance is assumed. -/
theorem dyadicCarryBlock_succ (k d : ℕ) (hd : 0 < d) :
    dyadicCarryBlock (k + 1) d hd =
      argumentDoublingContinuous (dyadicCarryBlock k d hd) +
        (2 : ℝ) ^ k • doublingCarryHilbert d hd := by
  unfold dyadicCarryBlock
  rw [argumentDoublingIterate_succ, map_sub, map_smul]
  simp only [argumentDoublingContinuous_apply, hilbertArgumentDoubling_residue,
    smul_sub, smul_smul, pow_succ]
  abel

@[simp] theorem dyadicCarryBlock_one (d : ℕ) (hd : 0 < d) :
    dyadicCarryBlock 1 d hd = doublingCarryHilbert d hd := by
  simpa only [dyadicCarryBlock_zero, map_zero, pow_zero, one_smul, zero_add] using
    dyadicCarryBlock_succ 0 d hd

/-- Every carry appears with its exact amplification factor.
The order is reversed to make the recurrence and the terminal boundary explicit. -/
theorem dyadicCarryBlock_eq_sum (k d : ℕ) (hd : 0 < d) :
    dyadicCarryBlock k d hd =
      ∑ j ∈ Finset.range k, (2 : ℝ) ^ j •
        argumentDoublingIterate (k - 1 - j) (doublingCarryHilbert d hd) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [dyadicCarryBlock_succ, ih, Finset.sum_range_succ, map_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, argumentDoublingIterate_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul]
    have hjk : j < k := Finset.mem_range.mp hj
    have he : k - j = (k - 1 - j) + 1 := by omega
    rw [he, argumentDoublingIterate_succ]

/-- Reverse residues at moduli 2^k+1. -/
def dyadicSampledResidue (k : ℕ) : ThresholdHilbert :=
  argumentDoublingIterate k
    (normalizedResidueHilbert (2 ^ k + 1) (by positivity))

@[simp] theorem dyadicSampledResidue_sequence (k n : ℕ) :
    hilbertSequence (dyadicSampledResidue k) n =
      residueFraction (2 ^ k + 1) (2 ^ k * n) := by
  simp [dyadicSampledResidue, normalizedResidueHilbert_sequence]

/-- Unconditional convergence in the actual weighted Hilbert norm. -/
theorem dyadicSampledResidue_tendsto_one :
    Tendsto dyadicSampledResidue atTop (𝓝 hilbertOne) := by
  apply hilbert_tendsto_one_of_bounded_coordinates
  · intro k n
    rw [dyadicSampledResidue_sequence]
    unfold residueFraction
    constructor
    · positivity
    · apply le_of_lt
      apply (div_lt_one (by positivity : (0 : ℝ) < ((2 ^ k + 1 : ℕ) : ℝ))).mpr
      exact_mod_cast Nat.mod_lt (2 ^ k * n) (by positivity : 0 < 2 ^ k + 1)
  · have hd : Tendsto (fun k : ℕ => ((2 ^ k + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_add
          (tendsto_const_nhds (x := (1 : ℝ)))
    have hi := tendsto_inv_atTop_zero.comp hd
    intro n hn
    have hl : Tendsto (fun k : ℕ => 1 - (n : ℝ) * ((2 ^ k + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 1) := by
      simpa only [Function.comp_def, mul_zero, sub_zero] using
        tendsto_const_nhds.sub (hi.const_mul (n : ℝ))
    apply (tendsto_congr' ?_).mpr hl
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [dyadicSampledResidue_sequence,
      reverseResidue_head _ _ hn (by
        have ht := Nat.lt_two_pow_self (n := k)
        omega)]
    rw [div_eq_mul_inv]

namespace CoefficientStabilization

/-- Removing the legal residue term leaves exactly the negative sampled residual. -/
theorem dyadicCarryBlock_projection_residual (k : ℕ) :
    dyadicCarryBlock k (2 ^ k + 1) (by positivity) -
        closedSpace.starProjection (dyadicCarryBlock k (2 ^ k + 1) (by positivity)) =
      -(dyadicSampledResidue k - closedSpace.starProjection (dyadicSampledResidue k)) := by
  have hg := Submodule.starProjection_eq_self_iff.mpr
    (normalizedResidue_mem_closedSpace (2 ^ k + 1) (by positivity))
  dsimp [dyadicCarryBlock, dyadicSampledResidue]
  rw [map_sub, map_smul, hg]
  abel

def dyadicCarryGap (k : ℕ) : ℝ :=
  ‖dyadicCarryBlock k (2 ^ k + 1) (by positivity) -
    closedSpace.starProjection (dyadicCarryBlock k (2 ^ k + 1) (by positivity))‖

theorem dyadicCarryGap_eq (k : ℕ) :
    dyadicCarryGap k =
      ‖dyadicSampledResidue k - closedSpace.starProjection (dyadicSampledResidue k)‖ := by
  rw [dyadicCarryGap, dyadicCarryBlock_projection_residual, norm_neg]

/-- The exact limiting optimum for the whole block is the constant's distance. -/
theorem dyadicCarryGap_tendsto :
    Tendsto dyadicCarryGap atTop
      (𝓝 ‖hilbertOne - closedSpace.starProjection hilbertOne‖) := by
  have hp := closedSpace.starProjection.continuous.continuousAt.tendsto.comp
    dyadicSampledResidue_tendsto_one
  change Tendsto (fun k => dyadicCarryGap k) atTop
    (𝓝 ‖hilbertOne - closedSpace.starProjection hilbertOne‖)
  simpa only [dyadicCarryGap_eq, Function.comp_def] using
    (dyadicSampledResidue_tendsto_one.sub hp).norm

theorem dyadicCarryGap_tendsto_zero_iff_one_mem :
    Tendsto dyadicCarryGap atTop (𝓝 0) ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have hz := tendsto_nhds_unique dyadicCarryGap_tendsto h
    have he := sub_eq_zero.mp (norm_eq_zero.mp hz)
    exact Submodule.starProjection_eq_self_iff.mp he.symm
  · intro h
    have he := Submodule.starProjection_eq_self_iff.mpr h
    simpa only [he, sub_self, norm_zero] using dyadicCarryGap_tendsto

/-- Only a sparse unbounded family of entire carry blocks is needed.
The approximation assumption remains unproved. -/
theorem hilbertOne_mem_of_dyadicCarryBlock_approx
    (stages : ℕ → ℕ) (hs : Tendsto stages atTop atTop)
    (v : ℕ → ThresholdHilbert) (hv : ∀ j, v j ∈ closedSpace)
    (he : Tendsto (fun j =>
      ‖dyadicCarryBlock (stages j) (2 ^ stages j + 1) (by positivity) - v j‖)
        atTop (𝓝 0)) :
    hilbertOne ∈ closedSpace := by
  let u (j : ℕ) : ThresholdHilbert :=
    (2 : ℝ) ^ stages j • normalizedResidueHilbert
      (2 ^ stages j + 1) (by positivity) - v j
  have hu (j : ℕ) : u j ∈ closedSpace :=
    closedSpace.sub_mem
      (closedSpace.smul_mem _ (normalizedResidue_mem_closedSpace _ _)) (hv j)
  have hz : Tendsto (fun j =>
      dyadicCarryBlock (stages j) (2 ^ stages j + 1) (by positivity) - v j)
      atTop (𝓝 (0 : ThresholdHilbert)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using he
  have hlim : Tendsto u atTop (𝓝 hilbertOne) := by
    have ht := (dyadicSampledResidue_tendsto_one.comp hs).add hz
    have hu_eq : u = fun j => dyadicSampledResidue (stages j) +
        (dyadicCarryBlock (stages j) (2 ^ stages j + 1) (by positivity) - v j) := by
      funext j
      dsimp [u, dyadicSampledResidue, dyadicCarryBlock]
      abel
    rw [hu_eq]
    simpa only [add_zero, Function.comp_def] using ht
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    (Eventually.of_forall hu)

/-- Conditional RH endpoint for joint dyadic carry-block approximation. -/
theorem riemannHypothesis_of_dyadicCarryBlock_approx
    (stages : ℕ → ℕ) (hs : Tendsto stages atTop atTop)
    (v : ℕ → ThresholdHilbert) (hv : ∀ j, v j ∈ closedSpace)
    (he : Tendsto (fun j =>
      ‖dyadicCarryBlock (stages j) (2 ^ stages j + 1) (by positivity) - v j‖)
        atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr
      (hilbertOne_mem_of_dyadicCarryBlock_approx stages hs v hv he))

end CoefficientStabilization
end RiemannResearch.RH.Pareto

import RiemannResearch.RH.ParetoNymanNorm
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exact translation of centered natural-dilation approximation

Source: Luis Báez-Duarte, arXiv:math/0202141v2, Theorem 1.1,
https://arxiv.org/abs/math/0202141, for the natural-dilation criterion.
The proof here uses the already checked Pareto--Nyman norm identity.

This module identifies the centered Nyman functions on `(0,1]` with the
existing complete Pareto Hilbert space. It proves no external analytic
RH-to-density theorem. In particular the approximation property below
is a proposition, not an axiom or a declared instance.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RiemannResearch.RH.Pareto.BaezDuarte
open CoefficientStabilization

/-- Complete centered Nyman squared error, with Lebesgue measure. -/
def centeredError (s : Finset ℕ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ in Ioc 0 1,
    ENNReal.ofReal ((1 - ∑ n ∈ s, a n *
      (Int.fract (1 / ((n : ℝ) * u)) -
        (1 / (n : ℝ)) * Int.fract (1 / u))) ^ 2)

/-- The explicit continuous approximation statement; no RH implication is built in. -/
def CenteredApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ d ∈ s, 0 < d) ∧ centeredError s a < ENNReal.ofReal ε

/-- A total version of the existing normalized residue vector. The zero index
is only a convenience and never occurs in an admissible approximation. -/
def residueVector (d : ℕ) : ThresholdHilbert :=
  if hd : 0 < d then normalizedResidueHilbert d hd else 0

def finiteResidueSum (s : Finset ℕ) (a : ℕ → ℝ) : ThresholdHilbert :=
  ∑ d ∈ s, a d • residueVector d

theorem finiteResidueSum_sequence (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (k : ℕ) :
    hilbertSequence (finiteResidueSum s a) k =
      ∑ d ∈ s, a d * (((k % d : ℕ) : ℝ) / (d : ℝ)) := by
  change hilbertSequenceLinear (∑ d ∈ s, a d • residueVector d) k = _
  simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  change a d * hilbertSequence (residueVector d) k = _
  rw [residueVector, dif_pos (hs d hd), normalizedResidueHilbert_sequence]
  rfl

/-- There is no hidden norm scaling: the continuous squared error is exactly
the `ofReal` of the complete Pareto squared Hilbert norm. -/
theorem centeredError_eq_hilbert_norm_sq (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    centeredError s a = ENNReal.ofReal (‖hilbertOne - finiteResidueSum s a‖ ^ 2) := by
  rw [centeredError, nyman_finite_lintegral_error s a hs, hilbert_norm_weighted_sq]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
    (hilbertSequence_square_summable (hilbertOne - finiteResidueSum s a))]
  apply tsum_congr
  intro k
  congr 1
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight]
  · have hsub := congrFun
      (hilbertSequenceLinear.map_sub hilbertOne (finiteResidueSum s a)) k
    change hilbertSequence (hilbertOne - finiteResidueSum s a) k =
      hilbertSequence hilbertOne k - hilbertSequence (finiteResidueSum s a) k at hsub
    rw [hsub, finiteResidueSum_sequence s a hs k, hilbertOne_sequence]
    simp [positiveWeight, zeroAnchor, hk]

private theorem residueVector_mem_span (d : ℕ) (hd : 0 < d) :
    residueVector d ∈ Submodule.span ℝ (Set.range residueAtom) := by
  by_cases h1 : d = 1
  · subst d
    have hz : residueVector 1 = 0 := by
      apply hilbertSequence_injective
      rw [residueVector, dif_pos (by omega : 0 < 1), normalizedResidueHilbert_sequence]
      change ArithmeticCumulative.residueFraction 1 = hilbertSequenceLinear 0
      rw [map_zero]
      funext k
      simp [ArithmeticCumulative.residueFraction, Nat.mod_one]
    rw [hz]
    exact Submodule.zero_mem _
  · have he : residueVector d = residueAtom (d - 2) := by
      have hidx : d - 2 + 2 = d := by omega
      simp only [residueVector, dif_pos hd, residueAtom, hidx]
    rw [he]
    exact Submodule.subset_span ⟨d - 2, rfl⟩

theorem finiteResidueSum_mem_span (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    finiteResidueSum s a ∈ Submodule.span ℝ (Set.range residueAtom) := by
  unfold finiteResidueSum
  apply Submodule.sum_mem
  intro d hd
  exact Submodule.smul_mem _ _ (residueVector_mem_span d (hs d hd))

private theorem finiteResidueSum_of_finsupp (c : ℕ →₀ ℝ) :
    finiteResidueSum (c.support.image (fun i => i + 2)) (fun d => c (d - 2)) =
      c.sum (fun i a => a • residueAtom i) := by
  classical
  change (∑ d ∈ c.support.image (fun i => i + 2), c (d - 2) • residueVector d) =
    ∑ i ∈ c.support, c i • residueAtom i
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [residueVector, residueAtom]
  · intro i hi j hj hij
    change i + 2 = j + 2 at hij
    omega

/-- All finite positive-conductor centered functions correspond to the existing
closed residue space, and conversely. The harmless conductor `1` gives zero. -/
theorem centeredApproximation_iff_one_mem :
    CenteredApproximation ↔ hilbertOne ∈ closedSpace := by
  classical
  constructor
  · intro h
    change hilbertOne ∈ closure (Submodule.span ℝ (Set.range residueAtom) : Set ThresholdHilbert)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨s, a, hs, he⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    rw [centeredError_eq_hilbert_norm_sq s a hs] at he
    have hsq : ‖hilbertOne - finiteResidueSum s a‖ ^ 2 < ε ^ 2 := by
      by_contra! hbad
      exact (not_le_of_gt he) (ENNReal.ofReal_le_ofReal hbad)
    refine ⟨finiteResidueSum s a, finiteResidueSum_mem_span s a hs, ?_⟩
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (hilbertOne - finiteResidueSum s a)]
  · intro h ε hε
    have hc : hilbertOne ∈
        closure (Submodule.span ℝ (Set.range residueAtom) : Set ThresholdHilbert) := h
    obtain ⟨f, hf, hdist⟩ := Metric.mem_closure_iff.mp hc
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
    let s := c.support.image (fun i => i + 2)
    let a : ℕ → ℝ := fun d => c (d - 2)
    have hs : ∀ d ∈ s, 0 < d := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      omega
    refine ⟨s, a, hs, ?_⟩
    rw [centeredError_eq_hilbert_norm_sq s a hs]
    have he : finiteResidueSum s a = c.sum (fun i a => a • residueAtom i) :=
      finiteResidueSum_of_finsupp c
    rw [← he, dist_eq_norm] at hdist
    have hsq : ‖hilbertOne - finiteResidueSum s a‖ ^ 2 < ε := by
      have hsqrt := Real.sq_sqrt hε.le
      nlinarith [norm_nonneg (hilbertOne - finiteResidueSum s a), Real.sqrt_nonneg ε]
    apply lt_of_le_of_ne (ENNReal.ofReal_le_ofReal hsq.le)
    intro heq
    have heq' := congrArg ENNReal.toReal heq
    simp only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hε.le] at heq'
    linarith

end RiemannResearch.RH.Pareto.BaezDuarte

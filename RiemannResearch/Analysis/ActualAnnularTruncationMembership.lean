import RiemannResearch.Analysis.WeightedMellinTopologyTargets
import RiemannResearch.RH.AnnularArithmeticIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Lattice

/-!
# Actual finite annular vectors belong to every weighted Mellin space

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The compact-support membership theorem uses the actual von Mangoldt signal;
it closes the previously named local membership obligation without an
infinite-vector energy hypothesis, RH, or a prime-correlation hypothesis.

The finite arithmetic sum is extended to a fixed cutoff on [1,X]. Added
indices have n > x and hence exact annular weight zero. Replacing x by
max 1 x then gives a globally continuous finite extension, whose indicator
has the same actual values. The weighted density is continuous on [1,X].
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
open RiemannResearch.RH
open RiemannResearch.RH.AnnularPrimePair

theorem indices_mono {x X : ℝ} (h : x ≤ X) : indices x ⊆ indices X := by
  intro n hn
  simp only [indices, Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans (Nat.floor_mono h)⟩

/-- The variable arithmetic cutoff can be replaced by any larger fixed
cutoff. This is an exact support identity, rather than an estimate. -/
theorem actualPrimeSignal_eq_fixed_cutoff {x X : ℝ}
    (hx : 1 ≤ x) (hX : x ≤ X) :
    actualPrimeSignal x = annularPrimeFinite (indices X) x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  unfold actualPrimeSignal annularPrimeFinite
  congr 1
  apply Finset.sum_subset (indices_mono hX)
  intro n hn hnnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnf : Nat.floor x < n := by
    by_contra h
    exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
  have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnf
  have hratio : 1 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx0).mpr (by simpa using hxn.le)
  rw [annularArithmeticWeight_eq_zero_of_one_le hratio]
  exact mul_zero _

/-- A continuous finite extension of the actual arithmetic values on
[1,X]. The safe denominator is at least one everywhere. -/
def fixedAnnularVector (X : ℝ) (x : ℝ) : ℂ :=
  (annularPrimeFinite (indices X) (max (1 : ℝ) x) : ℂ)

theorem fixedAnnularVector_continuous (X : ℝ) :
    Continuous (fixedAnnularVector X) := by
  have hd : Continuous (fun x : ℝ => max (1 : ℝ) x) :=
    continuous_const.sup continuous_id
  have hd0 : ∀ x : ℝ, max (1 : ℝ) x ≠ 0 := by
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 x))
  have hf : Continuous
      (fun x : ℝ => annularPrimeFinite (indices X) (max (1 : ℝ) x)) := by
    unfold annularPrimeFinite
    apply Continuous.sub
    · apply continuous_finsetSum
      intro n hn
      exact continuous_const.mul
        (continuous_annularArithmeticWeight.comp (continuous_const.div hd hd0))
    · exact continuous_const.mul hd
  exact Complex.continuous_ofReal.comp hf

theorem actualAnnularTruncation_eq_continuous_indicator (X : ℝ) :
    actualAnnularTruncation X =
      (Icc (1 : ℝ) X).indicator (fixedAnnularVector X) := by
  funext x
  by_cases hx : x ∈ Icc (1 : ℝ) X
  · simp only [actualAnnularTruncation, indicator_of_mem hx,
      actualAnnularVector, fixedAnnularVector, max_eq_right hx.1]
    exact congrArg (fun y : ℝ => (y : ℂ))
      (actualPrimeSignal_eq_fixed_cutoff hx.1 hx.2)
  · simp only [actualAnnularTruncation, indicator_of_notMem hx]

/-- Every continuous function cut off to [1,X] has finite weighted energy
for every real weight. The statement also covers the empty interval X<1. -/
theorem finiteEnergy_continuous_indicator_Icc {f : ℝ → ℂ}
    (hf : Continuous f) (s X : ℝ) :
    FiniteEnergy ((Icc (1 : ℝ) X).indicator f) s := by
  have hm : Measurable ((Icc (1 : ℝ) X).indicator f) :=
    hf.measurable.indicator measurableSet_Icc
  have hw : ContinuousOn (fun x : ℝ => x ^ (-s - 1)) (Icc (1 : ℝ) X) := by
    apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
  have hc : ContinuousOn (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-s - 1))
      (Icc (1 : ℝ) X) := (hf.norm.pow 2).continuousOn.mul hw
  have hi : Integrable
      ((Icc (1 : ℝ) X).indicator (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-s - 1))) :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have he :
      (fun x : ℝ => ‖(Icc (1 : ℝ) X).indicator f x‖ ^ 2 * x ^ (-s - 1)) =
        (Icc (1 : ℝ) X).indicator (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (-s - 1)) := by
    funext x
    by_cases hx : x ∈ Icc (1 : ℝ) X
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        zero_mul]
  refine ⟨hm, ?_⟩
  rw [he]
  exact hi.integrableOn

/-- Actual finite-truncation membership is proved, for all real a and X.
No uniform norm estimate as X grows is inferred. -/
theorem actualAnnularTruncation_Ha (a X : ℝ) :
    Ha a (actualAnnularTruncation X) := by
  rw [actualAnnularTruncation_eq_continuous_indicator]
  exact finiteEnergy_continuous_indicator_Icc (fixedAnnularVector_continuous X) (2 * a) X

theorem actualTruncationMembership : ActualTruncationMembershipProvider := by
  intro a X hX
  exact actualAnnularTruncation_Ha a X

/-- Finite truncations have entire Mellin transforms. Thus full-zero poles
are an infinite-tail phenomenon and cannot obstruct this finite membership. -/
theorem actualAnnularTruncation_transform_analyticAt (X : ℝ) (z : ℂ) :
    AnalyticAt ℂ (transform (actualAnnularTruncation X)) z := by
  have hf := actualAnnularTruncation_Ha (z.re - 1) X
  exact transform_analyticAt hf (by linarith : (2 * (z.re - 1)) / 2 < z.re)

theorem actualAnnularTruncation_transform_differentiable (X : ℝ) :
    Differentiable ℂ (transform (actualAnnularTruncation X)) := by
  intro z
  exact (actualAnnularTruncation_transform_analyticAt X z).differentiableAt

end RiemannResearch.Analysis.WeightedMellinTopology

import RiemannResearch.Analysis.MontgomeryBoundedHeightGaps
import RiemannResearch.Analysis.MontgomeryAllPairWordLimit
import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import Mathlib.Data.Fintype.Option

/-!
# Adjoining a duplicate to the finite sample of zeta ordinates

An extra occurrence at a fixed genuine ordinate changes the integer forward
atom and its excess over the diagonal. Every fixed bounded unfolded
strict-positive-gap statistic nevertheless agrees exactly for large heights.
The construction modifies the occurrence list; it asserts no new zeta zero.
This formalizes the finite-exception issue in the Mellin–prime handoff, §7.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryFixedDuplicate
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryAllPairWordRounding MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- Add one label at height τ. The original labels retain all their heights. -/
def adjoinHeight {ι : Type*} (y : ι → ℝ) (τ : ℝ) : Option ι → ℝ
  | none => τ
  | some i => y i

theorem collision_adjoinHeight {ι : Type*} [Fintype ι] (y : ι → ℝ) (τ : ℝ) :
    occurrenceCollision (adjoinHeight y τ) =
      occurrenceCollision y + 2 * ordinateMultiplicity y τ + 1 := by
  classical
  have hsum : (∑ j : ι, if y j = τ then (1 : ℕ) else 0) = ordinateMultiplicity y τ := by
    simp only [ordinateMultiplicity, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hrev : (∑ j : ι, if τ = y j then (1 : ℕ) else 0) = ordinateMultiplicity y τ := by
    simpa only [eq_comm] using hsum
  simp only [occurrenceCollision, Fintype.sum_option, adjoinHeight, if_true,
    Finset.sum_add_distrib]
  change (1 + (∑ j : ι, if y j = τ then 1 else 0)) +
      ((∑ i : ι, if τ = y i then 1 else 0) +
        ∑ i : ι, ∑ j : ι, if y i = y j then 1 else 0) =
      (∑ i : ι, ∑ j : ι, if y i = y j then 1 else 0) + 2 * ordinateMultiplicity y τ + 1
  rw [hrev, hsum]
  omega

/-- The added label changes the excess by twice the size of its original
ordinate fibre. This formula also applies to an unoccupied height. -/
theorem excess_adjoinHeight {ι : Type*} [Fintype ι] (y : ι → ℝ) (τ : ℝ) :
    occurrenceExcess (adjoinHeight y τ) = occurrenceExcess y + 2 * ordinateMultiplicity y τ := by
  have hid := collision_adjoinHeight y τ
  rw [occurrenceCollision_eq_card_add_excess, occurrenceCollision_eq_card_add_excess,
    Fintype.card_option] at hid
  omega

private theorem positiveTestSum_adjoin_of_isolated {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (τ : ℝ) (f : ℝ → ℝ)
    (hup : ∀ j, τ < y j → f (y j - τ) = 0)
    (hdn : ∀ j, y j < τ → f (τ - y j) = 0) :
    positiveTestSum (adjoinHeight y τ) f = positiveTestSum y f := by
  classical
  have hu (j : ι) : (if τ < y j then f (y j - τ) else 0) = 0 := by
    by_cases h : τ < y j <;> simp [h, hup]
  have hd (j : ι) : (if y j < τ then f (τ - y j) else 0) = 0 := by
    by_cases h : y j < τ <;> simp [h, hdn]
  simp only [positiveTestSum, Fintype.sum_option, adjoinHeight, lt_self_iff_false,
    if_false, zero_add, Finset.sum_add_distrib]
  change (∑ j : ι, if τ < y j then f (y j - τ) else 0) +
      ((∑ j : ι, if y j < τ then f (τ - y j) else 0) +
        ∑ i : ι, ∑ j : ι, if y j < y i then f (y i - y j) else 0) =
      ∑ i : ι, ∑ j : ι, if y j < y i then f (y i - y j) else 0
  simp only [hd, hu, Finset.sum_const_zero, zero_add]

/-- Compact positive-gap tests of the enlarged list agree exactly with
those of the true ordinates, simultaneously over every test of a fixed
maximum unfolded width. No pair-correlation hypothesis is used. -/
theorem eventually_adjoin_actualPositiveTest_eq (i : Site) (Q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ f : ℝ → ℝ, (∀ x, Q < x → f x = 0) →
      positiveTestSum (adjoinHeight (copyOrdinate T) (ordinate i))
        (fun d => f (Real.log T / (2 * Real.pi) * d)) /
        (T * Real.log T / (2 * Real.pi)) = actualPositiveTest T f := by
  filter_upwards [eventually_ge_atTop (ordinate i),
    eventually_unfolded_gap_gt_of_bounded_anchor (ordinate i) Q] with T hT hg
  intro f hf
  obtain ⟨c, hc⟩ := liftCopy_surj_below T i hT
  have hτ : copyOrdinate T c = ordinate i := congrArg ordinate hc
  unfold actualPositiveTest
  congr 1
  apply positiveTestSum_adjoin_of_isolated
  · intro j hj
    exact hf _ (by simpa only [hτ] using hg c j hτ.le (hτ.trans_lt hj))
  · intro j hj
    exact hf _ (by simpa only [hτ] using hg j c hj.le (hj.trans_eq hτ.symm))

/-- The added collision excess stabilizes at one fixed positive even
integer, independent of the sampling height and all test widths. -/
theorem eventually_extra_excess_exact (i : Site) :
    ∀ᶠ T : ℝ in atTop,
      occurrenceExcess (adjoinHeight (copyOrdinate T) (ordinate i)) =
        occurrenceExcess (copyOrdinate T) + 2 * (ordinateFiber i).card := by
  filter_upwards [eventually_ge_atTop (ordinate i)] with T hT
  obtain ⟨c, hc⟩ := liftCopy_surj_below T i hT
  have hτ : copyOrdinate T c = ordinate i := congrArg ordinate hc
  rw [excess_adjoinHeight]
  change _ + 2 * actualOrdinateMultiplicity T (ordinate i) = _
  rw [← hτ, ← ordinateFiber_card_liftCopy T c, hc]

/-- After bulk normalization even the extra forward-atom excess vanishes.
Its unnormalized value is at least two at every sufficiently high cutoff. -/
theorem extra_excess_invisible_after_normalization (i : Site) :
    (∀ᶠ T : ℝ in atTop,
      occurrenceExcess (copyOrdinate T) + 2 ≤
        occurrenceExcess (adjoinHeight (copyOrdinate T) (ordinate i))) ∧
    Tendsto (fun T : ℝ =>
      ((occurrenceExcess (adjoinHeight (copyOrdinate T) (ordinate i)) : ℝ) -
        (occurrenceExcess (copyOrdinate T) : ℝ)) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 0) := by
  constructor
  · filter_upwards [eventually_extra_excess_exact i] with T he
    have hpos := ordinateFiber_card_pos i
    omega
  · have hg : Tendsto (fun T : ℝ => T * Real.log T / (2 * Real.pi)) atTop atTop :=
      (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
    have hlim := (tendsto_const_nhds (x := (2 * ((ordinateFiber i).card : ℝ)))).mul
      (tendsto_inv_atTop_zero.comp hg)
    rw [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_extra_excess_exact i] with T he
    rw [he]
    push_cast
    simp [div_eq_mul_inv]

end RiemannResearch.Analysis.MontgomeryFixedDuplicate

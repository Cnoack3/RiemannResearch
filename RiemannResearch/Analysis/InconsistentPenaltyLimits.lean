import RiemannResearch.Analysis.AttainableObservations
import RiemannResearch.Analysis.RegularizedPathAction
import Mathlib.Tactic.FieldSimp

/-!
# Hard-penalty limits with inconsistent or redundant observations

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The asymptotic mismatch is exactly the impossible component of the requested
data, with no row-rank or feasibility assumption. The same quantity is the
limit of the normalized optimal objective and closes the exact action sum.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.InconsistentPenaltyLimits
open FiniteRegularizedConstraints AttainableObservations RegularizedPathAction
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Finite quantitative excess above the irreducible mismatch. -/
theorem mismatch_excess_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (a : ι → ℝ) (ha : ∀ j, observe B a j = projectedTarget B t j) :
    0 ≤ mismatchEnergy B t (coefficients hv B f t ρ) - inconsistency B t ∧
    mismatchEnergy B t (coefficients hv B f t ρ) - inconsistency B t ≤
      ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 / ρ ^ 2 := by
  refine ⟨sub_nonneg.mpr (inconsistency_le_mismatch B t _), ?_⟩
  have he := (excess_objective_bounds hv B f t ρ a ha).2
  unfold objective at he
  apply (le_div_iff₀ (sq_pos_iff.mpr hρ)).mpr
  nlinarith only [he, sq_nonneg ‖f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ)‖]

section Limit
variable {α : Type*} {l : Filter α}

/-- Every observation system, including inconsistent systems, reaches its exact least mismatch. -/
theorem mismatch_tendsto_inconsistency {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => mismatchEnergy B t (coefficients hv B f t (r i))) l
      (𝓝 (inconsistency B t)) := by
  obtain ⟨a, ha⟩ := projectedTarget_feasible B t
  have hb : Tendsto (fun i => ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 / (r i) ^ 2) l (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun i => ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 * (1 / (r i) ^ 2)) l
        (𝓝 (‖f - Fintype.linearCombination ℝ v a‖ ^ 2 * 0)))
  have hz : Tendsto (fun i => mismatchEnergy B t (coefficients hv B f t (r i)) -
      inconsistency B t) l (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun i =>
      sub_nonneg.mpr (inconsistency_le_mismatch B t _))) ?_ hb
    filter_upwards [hne] with i hi
    exact (mismatch_excess_bound hv B f t (r i) hi a ha).2
  simpa only [sub_add_cancel, zero_add] using hz.add_const (inconsistency B t)

/-- The optimal objective grows precisely like penalty squared times the impossible cost. -/
theorem normalized_minimum_tendsto_inconsistency {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => objective v B f t (r i) (coefficients hv B f t (r i)) / (r i) ^ 2) l
      (𝓝 (inconsistency B t)) := by
  obtain ⟨a, ha⟩ := projectedTarget_feasible B t
  have hb : Tendsto (fun i => ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 / (r i) ^ 2) l (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun i => ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 * (1 / (r i) ^ 2)) l
        (𝓝 (‖f - Fintype.linearCombination ℝ v a‖ ^ 2 * 0)))
  have hz : Tendsto (fun i =>
      (objective v B f t (r i) (coefficients hv B f t (r i)) -
        (r i) ^ 2 * inconsistency B t) / (r i) ^ 2) l (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hb
    · exact Filter.Eventually.of_forall (fun i => div_nonneg
        (excess_objective_bounds hv B f t (r i) a ha).1 (sq_nonneg _))
    · exact Filter.Eventually.of_forall (fun i => div_le_div_of_nonneg_right
        (excess_objective_bounds hv B f t (r i) a ha).2 (sq_nonneg _))
  have ht := hz.add_const (inconsistency B t)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [hne] with i hi
  field_simp [hi]
  <;> ring

/-- Feasibility is exactly zero limiting penalized mismatch. -/
theorem zero_mismatch_limit_iff [NeBot l] {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : α → ℝ)
    (hne : ∀ᶠ i in l, r i ≠ 0)
    (hinv : Tendsto (fun i => 1 / (r i) ^ 2) l (𝓝 0)) :
    Tendsto (fun i => mismatchEnergy B t (coefficients hv B f t (r i))) l (𝓝 0) ↔
      ∃ a : ι → ℝ, ∀ j, observe B a j = t j := by
  have ht := mismatch_tendsto_inconsistency hv B f t r hne hinv
  constructor
  · intro hz
    exact (inconsistency_zero_iff B t).mp (tendsto_nhds_unique ht hz)
  · intro hf
    simpa only [(inconsistency_zero_iff B t).mpr hf] using ht

end Limit

/-- The exact action identity also covers plateaus, reversals and sign changes. -/
theorem penaltyAction_exact_unrestricted {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) :
    penaltyAction hv B f t ρ σ =
      mismatchEnergy B t (coefficients hv B f t ρ) -
      mismatchEnergy B t (coefficients hv B f t σ) := by
  by_cases h : ρ ^ 2 = σ ^ 2
  · have hx := penalty_difference_exact hv B f t ρ σ
    have hd : σ ^ 2 - ρ ^ 2 = 0 := by rw [h, sub_self]
    rw [hd, zero_mul] at hx
    have hp := mul_nonneg (add_nonneg (sq_nonneg ρ) (sq_nonneg σ))
      (observationEnergy_nonneg B (coefficients hv B f t ρ - coefficients hv B f t σ))
    have hz : ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖ ^ 2 = 0 := by
      nlinarith only [hx, hp, sq_nonneg ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖]
    have he : coefficients hv B f t ρ = coefficients hv B f t σ := by
      apply sub_eq_zero.mp
      apply hv.fintypeLinearCombination_injective
      simpa only [map_zero] using norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    simp only [penaltyAction, hd, div_zero, he, sub_self]
  · unfold penaltyAction
    apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm h))).mpr
    nlinarith only [penalty_difference_exact hv B f t ρ σ]

/-- Every finite path telescopes exactly, with no monotonicity hypothesis. -/
theorem finite_path_action_unrestricted {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, penaltyAction hv B f t (r k) (r (k + 1))) =
      mismatchEnergy B t (coefficients hv B f t (r 0)) -
      mismatchEnergy B t (coefficients hv B f t (r N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, penaltyAction_exact_unrestricted]
    ring

/-- Weakly increasing squared penalties suffice; arbitrary plateaus are allowed. -/
theorem path_action_summable_nondecreasing {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ)
    (hr : ∀ k, (r k) ^ 2 ≤ (r (k + 1)) ^ 2) :
    Summable (fun k => penaltyAction hv B f t (r k) (r (k + 1))) := by
  apply summable_of_sum_range_le
    (fun k => ?_) (c := mismatchEnergy B t (coefficients hv B f t (r 0)))
  · intro N
    rw [finite_path_action_unrestricted]
    exact sub_le_self _ (mismatchEnergy_nonneg B t _)
  · rw [penaltyAction_exact_unrestricted]
    exact sub_nonneg.mpr (mismatch_antitone_of_sq_le hv B f t _ _ (hr k))

/-- The entire action equals initial mismatch minus the irreducible inconsistent part. -/
theorem total_action_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (r : ℕ → ℝ)
    (hstep : ∀ k, (r k) ^ 2 ≤ (r (k + 1)) ^ 2)
    (hne : ∀ᶠ k in atTop, r k ≠ 0)
    (hinv : Tendsto (fun k => 1 / (r k) ^ 2) atTop (𝓝 0)) :
    (∑' k, penaltyAction hv B f t (r k) (r (k + 1))) =
      mismatchEnergy B t (coefficients hv B f t (r 0)) - inconsistency B t :=
by
  have hs := (path_action_summable_nondecreasing hv B f t r hstep).hasSum.tendsto_sum_nat
  simp only [finite_path_action_unrestricted] at hs
  have ht : Tendsto (fun N => mismatchEnergy B t (coefficients hv B f t (r 0)) -
      mismatchEnergy B t (coefficients hv B f t (r N))) atTop
      (𝓝 (mismatchEnergy B t (coefficients hv B f t (r 0)) - inconsistency B t)) :=
    tendsto_const_nhds.sub (mismatch_tendsto_inconsistency hv B f t r hne hinv)
  exact tendsto_nhds_unique hs ht

end RiemannResearch.Analysis.InconsistentPenaltyLimits

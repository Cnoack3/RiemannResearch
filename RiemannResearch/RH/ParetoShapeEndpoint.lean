import RiemannResearch.RH.ParetoShapeCapacity
import RiemannResearch.RH.ParetoShapeThreshold
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Uniform control across the critical Pareto shape

Source: continuation of the user-provided Pareto capacity argument.
The shape-one endpoint is recovered from the actual infinite energies by
dominated convergence. The connection to the classical density implication
uses Bagchi, Theorem 1, https://arxiv.org/pdf/math/0607733, as an explicit
hypothesis until its analytic provider has been formalized.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.ShapeCapacity
open CoefficientStabilization
open RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

theorem shapeCellWeight_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun α : ℝ => shapeCellWeight α a) := by
  unfold shapeCellWeight
  fun_prop (disch := positivity)

/-- The complete legal energy, including all mixed terms, is continuous at
every positive shape. No uniform bound on the dictionary is required. -/
theorem shapeLegalTailEnergy_continuousAt (α : ℝ) (hα : 0 < α)
    (n : ℕ) (c : Fin n → ℂ) :
    ContinuousAt (fun β => shapeLegalTailEnergy β n c) α := by
  have hα2 : 0 < α / 2 := by positivity
  have hsum := (shapeLegalTailEnergy_summable (α / 2) hα2 n c).mul_left 4
  have hpoint (k : ℕ) : Tendsto
      (fun β => shapeCellWeight β ((k : ℝ) + 2) *
        ‖shapeLegalCombination n c (k + 1)‖ ^ 2) (𝓝 α)
      (𝓝 (shapeCellWeight α ((k : ℝ) + 2) *
        ‖shapeLegalCombination n c (k + 1)‖ ^ 2)) :=
    ((shapeCellWeight_continuous _ (by positivity)).continuousAt.tendsto).mul_const _
  have hdom : ∀ᶠ β in 𝓝 α, ∀ k : ℕ,
      ‖shapeCellWeight β ((k : ℝ) + 2) *
        ‖shapeLegalCombination n c (k + 1)‖ ^ 2‖ ≤
      4 * (shapeCellWeight (α / 2) ((k : ℝ) + 2) *
        ‖shapeLegalCombination n c (k + 1)‖ ^ 2) := by
    filter_upwards [eventually_gt_nhds (show α / 2 < α by linarith),
      eventually_lt_nhds (show α < 2 * α by linarith)] with β hlo hhi
    intro k
    have hβ : 0 < β := hα2.trans hlo
    have hw0 := (shapeCellWeight_pos (α / 2) ((k : ℝ) + 2) hα2 (by positivity)).le
    have hcmp := shapeCellWeight_div_antitone ((k : ℝ) + 2)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
      hα2 hβ hlo.le
    have hcross := (div_le_div_iff₀ hβ hα2).mp hcmp
    have hw : shapeCellWeight β ((k : ℝ) + 2) ≤
        4 * shapeCellWeight (α / 2) ((k : ℝ) + 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hhi.le hw0]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (shapeCellWeight_pos β _ hβ (by positivity)).le (sq_nonneg _))]
    nlinarith only [mul_le_mul_of_nonneg_right hw
      (sq_nonneg ‖shapeLegalCombination n c (k + 1)‖)]
  exact tendsto_tsum_of_dominated_convergence hsum hpoint hdom

/-- Legal primal energy divided by shape decreases as the shape increases. -/
theorem shapeLegalTailEnergy_div_antitone (n : ℕ) (c : Fin n → ℂ) :
    AntitoneOn (fun α => shapeLegalTailEnergy α n c / α) (Set.Ioi 0) := by
  intro α hα β hβ hαβ
  change shapeLegalTailEnergy β n c / β ≤ shapeLegalTailEnergy α n c / α
  unfold shapeLegalTailEnergy
  rw [← tsum_div_const, ← tsum_div_const]
  apply Summable.tsum_le_tsum _
    ((shapeLegalTailEnergy_summable β hβ n c).div_const β)
    ((shapeLegalTailEnergy_summable α hα n c).div_const α)
  intro k
  have h := mul_le_mul_of_nonneg_right
    (shapeCellWeight_div_antitone ((k : ℝ) + 2)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) hα hβ hαβ)
    (sq_nonneg ‖shapeLegalCombination n c (k + 1)‖)
  simpa only [div_mul_eq_mul_div] using h

/-- Exact identification with the original complexified Pareto tail norm. -/
theorem shapeLegalTailEnergy_one (n : ℕ) (c : Fin n → ℂ) :
    shapeLegalTailEnergy 1 n c = ‖complexTailCombination n c‖ ^ 2 := by
  have ht0 (i : ℕ) : tailAtom i 0 = 0 := by
    have h := tailMap_evaluation (residueAtom i)
    rw [anchoredEvaluationCLM_apply, hilbertSequence_succ] at h
    change tailAtom i 0 / Real.sqrt (paretoWeight 0) = 0 at h
    exact (div_eq_zero_iff.mp h).resolve_right
      (Real.sqrt_pos.mpr (paretoWeight_pos 0)).ne'
  have hzero : complexTailCombination n c 0 = 0 := by
    simp only [complexTailCombination, Fintype.linearCombination_apply,
      lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
      realHilbertComplexify_apply, ht0, Complex.ofReal_zero, smul_zero,
      Finset.sum_const_zero]
  have hs : Summable (fun k => ‖complexTailCombination n c k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (show 0 < (2 : ENNReal).toReal by norm_num)
        (complexTailCombination n c).property
  rw [complexHilbert_norm_sq, hs.tsum_eq_zero_add, hzero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), zero_add]
  unfold shapeLegalTailEnergy
  apply tsum_congr
  intro k
  have hw : shapeCellWeight 1 ((k : ℝ) + 2) = paretoWeight (k + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      shapeCellWeight_one (k + 1)
  rw [hw, complexTailCombination_tail_coordinate, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (paretoWeight_pos (k + 1)).le]
  rfl

/-- A coefficient-uniform endpoint constant is equivalent to the same
normalized constant throughout ANY left neighborhood of shape one. -/
theorem shape_endpoint_coercivity_iff (a ε : ℝ) (ha : a < 1) :
    (∀ (n : ℕ) (c : Fin n → ℂ),
      ε * ‖complexReciprocalSource n c‖ ^ 2 ≤ shapeLegalTailEnergy 1 n c) ↔
    (∀ α : ℝ, 0 < α → a < α → α < 1 → ∀ (n : ℕ) (c : Fin n → ℂ),
      (α * ε) * ‖complexReciprocalSource n c‖ ^ 2 ≤ shapeLegalTailEnergy α n c) := by
  constructor
  · intro h α hα _ hα1 n c
    have he : shapeLegalTailEnergy 1 n c ≤ shapeLegalTailEnergy α n c / α := by
      simpa only [div_one] using
        shapeLegalTailEnergy_div_antitone n c hα
          (show (0 : ℝ) < 1 by norm_num) hα1.le
    have he' := (le_div_iff₀ hα).mp ((h n c).trans he)
    nlinarith only [he']
  · intro h n c
    have hl : Tendsto (fun α : ℝ => (α * ε) * ‖complexReciprocalSource n c‖ ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝 (ε * ‖complexReciprocalSource n c‖ ^ 2)) := by
      have hfull : Tendsto
          (fun α : ℝ => (α * ε) * ‖complexReciprocalSource n c‖ ^ 2)
          (𝓝 (1 : ℝ)) (𝓝 ((1 * ε) * ‖complexReciprocalSource n c‖ ^ 2)) := by
        change ContinuousAt (fun α : ℝ =>
          (α * ε) * ‖complexReciprocalSource n c‖ ^ 2) (1 : ℝ)
        fun_prop
      simpa only [one_mul] using hfull.mono_left
        (show (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
    have hr : Tendsto (fun α : ℝ => shapeLegalTailEnergy α n c)
        (𝓝[<] (1 : ℝ)) (𝓝 (shapeLegalTailEnergy 1 n c)) :=
      (shapeLegalTailEnergy_continuousAt 1 zero_lt_one n c).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds] with α hα1 hα haα
    exact h α hα haα hα1 n c

/-- Uniform bounds near the critical shape are exactly boundedness of the
original full-tail Gram capacities. No zeta or density hypothesis is needed. -/
theorem uniform_shape_coercivity_iff_capacity_bounded (a : ℝ) (ha : a < 1) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ α : ℝ, 0 < α → a < α → α < 1 →
      ∀ (n : ℕ) (c : Fin n → ℂ),
        (α * ε) * ‖complexReciprocalSource n c‖ ^ 2 ≤ shapeLegalTailEnergy α n c) ↔
    ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B := by
  have he : (∃ ε : ℝ, 0 < ε ∧ ∀ α : ℝ, 0 < α → a < α → α < 1 →
      ∀ (n : ℕ) (c : Fin n → ℂ),
        (α * ε) * ‖complexReciprocalSource n c‖ ^ 2 ≤ shapeLegalTailEnergy α n c) ↔
      ComplexUniformTailCoercivity := by
    simp only [← shape_endpoint_coercivity_iff a _ ha,
      shapeLegalTailEnergy_one, ComplexUniformTailCoercivity]
  exact he.trans (complexUniformTailCoercivity_iff_real.trans
    uniformTailCoercivity_iff_capacity_bounded)

/-- CONDITIONAL RESEARCH REDUCTION: the analytic density direction is the
only extra input when converting endpoint-uniform control into not RH. -/
theorem uniform_shape_coercivity_iff_not_RH (a : ℝ) (ha : a < 1)
    (hDensity : RiemannHypothesis → closedSpace = ⊤) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ α : ℝ, 0 < α → a < α → α < 1 →
      ∀ (n : ℕ) (c : Fin n → ℂ),
        (α * ε) * ‖complexReciprocalSource n c‖ ^ 2 ≤ shapeLegalTailEnergy α n c) ↔
    ¬ RiemannHypothesis :=
  (uniform_shape_coercivity_iff_capacity_bounded a ha).trans
    (tailCapacity_bounded_iff_not_RH hDensity)

/-- Sufficient RH criterion with no imported RH-to-density direction:
arbitrarily large normalized ratios in every fixed left neighborhood. -/
theorem riemannHypothesis_of_shape_coercivity_failure (a : ℝ) (ha : a < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ a < α ∧ α < 1 ∧
      ∃ (n : ℕ) (c : Fin n → ℂ),
        shapeLegalTailEnergy α n c < (α * ε) * ‖complexReciprocalSource n c‖ ^ 2) :
    RiemannHypothesis := by
  by_contra hRH
  have hb := firstCoordinateTailGap_pos_iff_capacity_bounded.mp
    (not_RH_firstCoordinateTailGap_pos hRH)
  obtain ⟨ε, hε, he⟩ := (uniform_shape_coercivity_iff_capacity_bounded a ha).mpr hb
  obtain ⟨α, hα, haα, hα1, n, c, hc⟩ := h ε hε
  exact (not_lt_of_ge (he α hα haα hα1 n c)) hc

end RiemannResearch.RH.Pareto.ShapeCapacity

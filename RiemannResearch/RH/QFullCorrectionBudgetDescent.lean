import RiemannResearch.RH.QFullResidualCorrectionCost
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ResidualLossBounds
import RiemannResearch.Analysis.ResidualHarmonicGain
import RiemannResearch.Analysis.FiniteHarmonicBounds
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Growing correction budgets for the actual full-Q residual

Source: user-provided `Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md`,
formula (F), continued on 15 November 2026. The exact cost/gain identity from
`QFullResidualCorrectionCost` is combined with the existing scalar accounting
theorems in `Analysis.ResidualLossBounds`.

Write E_k for the squared actual residual norm at stage σ(k). A correction
inside stage σ(k+1) with normalized cost at most K_k gives exactly
E_k / K_k ≤ E_k - E_(k+1). The finite accounting identity retains the
energy-variation term and the entire slack. Consequently
E_n ≤ E_0 exp(-∑_(k<n) 1/K_k).

An eventual budget suffices if its positive reciprocals are not summable.
In particular, budgets C(k+1), and logarithmic budgets on scales with
log L_k = O(k+1), suffice for RH. Only monotonicity of the stage schedule is
needed: vanishing energy along any schedule already forces qOne into the
closed legal span.

These are conditional research reductions. No arithmetic correction provider,
uniform inverse-Gram estimate, or converse from RH to full-Q density is assumed
or proved. A correction must lie in the specified next stage; an unrestricted
future correction does not provide a prescribed growth schedule.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullCorrectionBudgetDescent
open ZetaTwoHilbert QFullResidueProjection QFullResidualCorrectionCost
open RiemannResearch.Analysis.ResidualGain
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Squared norm of the actual inverse-Gram residual, without truncating Q. -/
def energy (N : ℕ) : ℝ := ‖residual N‖ ^ 2

/-- A finite next-stage correction budget. A zero residual needs no correction. -/
def CorrectionBudget (N M : ℕ) (K : ℝ) : Prop :=
  residual N ≠ 0 →
    ∃ w ∈ stage M, inner ℝ (residual N) w ≠ 0 ∧
      energy N * (‖w‖ ^ 2 / (inner ℝ (residual N) w) ^ 2) ≤ K

/-- Exact cost-to-loss conversion, including finite termination. -/
theorem correctionBudget_iff_loss {N M : ℕ} (hNM : N ≤ M)
    {K : ℝ} (hK : 0 < K) :
    CorrectionBudget N M K ↔ 1 / K * energy N ≤ energy N - energy M := by
  by_cases hr : residual N = 0
  · have he : energy N = 0 := by simp [energy, hr]
    have hM : energy M = 0 := by
      have h := residual_energy_completion N M hNM
      rw [hr, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
      unfold energy
      nlinarith [sq_nonneg ‖residual M‖, sq_nonneg ‖candidate M - candidate N‖]
    simp [CorrectionBudget, hr, he, hM]
  · constructor
    · intro hb
      have h := (correction_budget_iff_gain N M hNM hr K hK).mp (hb hr)
      simpa only [one_div_mul_eq_div, energy] using h
    · intro h _
      apply (correction_budget_iff_gain N M hNM hr K hK).mpr
      simpa only [one_div_mul_eq_div, energy] using h

theorem energy_lower_bound (N : ℕ) :
    ‖qOne - closure.starProjection qOne‖ ^ 2 ≤ energy N := by
  have he := walkError_eq_limitingError_add (fun i => qResidue (i + 2)) id qOne N
  change ‖qOne - (stage N).starProjection qOne‖ ^ 2 =
    ‖qOne - closure.starProjection qOne‖ ^ 2 +
      ‖closure.starProjection qOne - (stage N).starProjection qOne‖ ^ 2 at he
  rw [← candidate_eq_projection] at he
  change ‖qOne - closure.starProjection qOne‖ ^ 2 ≤ ‖qOne - candidate N‖ ^ 2
  nlinarith [sq_nonneg ‖closure.starProjection qOne - candidate N‖]

/-- Energy exhaustion on any stage sequence forces legal closure membership;
no cofinality or monotonicity assumption is required for this implication. -/
theorem qOne_mem_closure_of_subsequence_energy_tendsto_zero
    (σ : ℕ → ℕ) (hz : Tendsto (fun k => energy (σ k)) atTop (𝓝 0)) :
    qOne ∈ closure := by
  have hl : ‖qOne - closure.starProjection qOne‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hz
      (Filter.Eventually.of_forall (fun k => energy_lower_bound (σ k)))
  have he : closure.starProjection qOne = qOne := by
    symm
    exact sub_eq_zero.mp (norm_eq_zero.mp
      (sq_eq_zero_iff.mp (le_antisymm hl (sq_nonneg _))))
  exact Submodule.starProjection_eq_self_iff.mp he

/-- Exact finite accounting of the budget fractions, the changing energies,
and the slack in each actual correction gain. -/
theorem correction_budget_accounting (σ : ℕ → ℕ) (hσ : Monotone σ)
    (K : ℕ → ℝ) (n : ℕ) :
    energy (σ 0) =
      energy (σ n) * (1 + ∑ i ∈ Finset.range n, 1 / K i) +
      (∑ i ∈ Finset.range n, (1 / K i) * (energy (σ i) - energy (σ n))) +
      ∑ i ∈ Finset.range n,
        (‖candidate (σ (i + 1)) - candidate (σ i)‖ ^ 2 -
          (1 / K i) * energy (σ i)) := by
  have he (i : ℕ) : energy (σ i) - energy (σ (i + 1)) =
      ‖candidate (σ (i + 1)) - candidate (σ i)‖ ^ 2 := by
    have h := residual_energy_completion (σ i) (σ (i + 1))
      (hσ (Nat.le_succ i))
    change energy (σ i) = energy (σ (i + 1)) + _ at h
    linarith only [h]
  simpa only [he] using loss_accounting (fun i => energy (σ i)) (fun i => 1 / K i) n

/-- Quantitative decay from the cumulative reciprocal correction budget. -/
theorem energy_le_exp_neg_reciprocal_sum
    (σ : ℕ → ℕ) (hσ : Monotone σ) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k)
    (hb : ∀ k, CorrectionBudget (σ k) (σ (k + 1)) (K k)) (n : ℕ) :
    energy (σ n) ≤ energy (σ 0) *
      Real.exp (-(∑ i ∈ Finset.range n, 1 / K i)) := by
  exact residual_le_exp_neg_cumulative_loss (fun i => sq_nonneg ‖residual (σ i)‖)
    (fun i => (correctionBudget_iff_loss (hσ (Nat.le_succ i)) (hK i)).mp (hb i)) n


/-- Linear correction budgets give an explicit harmonic-exponential bound
at every finite step, before taking any limit. -/
theorem energy_le_exp_neg_harmonic_of_linear_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ k, CorrectionBudget (σ k) (σ (k + 1)) (C * ((k : ℝ) + 1)))
    (n : ℕ) :
    energy (σ n) ≤ energy (σ 0) * Real.exp (-(harmonic n : ℝ) / C) := by
  have hs : (∑ i ∈ Finset.range n, 1 / (C * ((i : ℝ) + 1))) =
      (harmonic n : ℝ) / C := by
    rw [RiemannResearch.Analysis.harmonic_cast_range, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_div, mul_comm C]
  have h := energy_le_exp_neg_reciprocal_sum σ hσ
    (fun k => C * ((k : ℝ) + 1)) (fun k => by positivity) hb n
  simpa only [hs, neg_div] using h

/-- A surviving residual places a finite ceiling on every partial sum of
reciprocal budgets. This keeps the limiting residual explicit. -/
theorem reciprocal_sum_le_of_positive_limiting_energy
    (σ : ℕ → ℕ) (hσ : Monotone σ) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k)
    (hb : ∀ k, CorrectionBudget (σ k) (σ (k + 1)) (K k))
    (hδ : 0 < ‖qOne - closure.starProjection qOne‖ ^ 2) (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / K i) ≤
      energy (σ 0) / ‖qOne - closure.starProjection qOne‖ ^ 2 - 1 := by
  have hs : 0 ≤ ∑ i ∈ Finset.range n, 1 / K i :=
    Finset.sum_nonneg (fun i _ => le_of_lt (one_div_pos.mpr (hK i)))
  have hbnd := residual_mul_one_add_cumulative_loss_le
    (fun i => sq_nonneg ‖residual (σ i)‖)
    (fun i => le_of_lt (one_div_pos.mpr (hK i)))
    (fun i => (correctionBudget_iff_loss (hσ (Nat.le_succ i)) (hK i)).mp (hb i)) n
  have hmul := mul_le_mul_of_nonneg_right (energy_lower_bound (σ n))
    (show 0 ≤ 1 + ∑ i ∈ Finset.range n, 1 / K i by linarith)
  have hdiv : 1 + ∑ i ∈ Finset.range n, 1 / K i ≤
      energy (σ 0) / ‖qOne - closure.starProjection qOne‖ ^ 2 := by
    apply (le_div_iff₀ hδ).mpr
    calc
      _ = ‖qOne - closure.starProjection qOne‖ ^ 2 *
          (1 + ∑ i ∈ Finset.range n, 1 / K i) := by ring
      _ ≤ energy (σ n) * (1 + ∑ i ∈ Finset.range n, 1 / K i) := hmul
      _ ≤ energy (σ 0) := hbnd
  linarith

theorem energy_tendsto_zero_of_reciprocal_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k)
    (hb : ∀ᶠ k in atTop, CorrectionBudget (σ k) (σ (k + 1)) (K k))
    (hdiv : ¬ Summable (fun k => 1 / K k)) :
    Tendsto (fun k => energy (σ k)) atTop (𝓝 0) := by
  apply tendsto_zero_of_eventually_not_summable_loss
    (fun k => sq_nonneg ‖residual (σ k)‖)
    (fun k => le_of_lt (one_div_pos.mpr (hK k))) _ hdiv
  exact hb.mono (fun k hk =>
    (correctionBudget_iff_loss (hσ (Nat.le_succ k)) (hK k)).mp hk)

/-- Conditional RH reduction allowing unbounded, stage-dependent budgets. -/
theorem riemannHypothesis_of_reciprocal_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k)
    (hb : ∀ᶠ k in atTop, CorrectionBudget (σ k) (σ (k + 1)) (K k))
    (hdiv : ¬ Summable (fun k => 1 / K k)) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (qOne_mem_closure_of_subsequence_energy_tendsto_zero σ
      (energy_tendsto_zero_of_reciprocal_budgets σ hσ K hK hb hdiv))

theorem reciprocal_linear_budget_not_summable (C : ℝ) (hC : 0 < C) :
    ¬ Summable (fun k : ℕ => 1 / (C * ((k : ℝ) + 1))) := by
  apply not_summable_of_harmonic_lower (c := 1 / C) (one_div_pos.mpr hC)
  intro k
  have hn : (k : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hc : C ≠ 0 := ne_of_gt hC
  apply le_of_eq
  field_simp

theorem riemannHypothesis_of_linear_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ) (C : ℝ) (hC : 0 < C)
    (hb : ∀ᶠ k in atTop,
      CorrectionBudget (σ k) (σ (k + 1)) (C * ((k : ℝ) + 1))) :
    RiemannHypothesis :=
  riemannHypothesis_of_reciprocal_budgets σ hσ _ (fun k => by positivity)
    hb (reciprocal_linear_budget_not_summable C hC)


theorem CorrectionBudget.mono {N M : ℕ} {K L : ℝ}
    (h : CorrectionBudget N M K) (hKL : K ≤ L) : CorrectionBudget N M L := by
  intro hr
  obtain ⟨w, hw, hs, hb⟩ := h hr
  exact ⟨w, hw, hs, hb.trans hKL⟩

/-- Logarithmic budgets exhaust the residual when the logarithms of the
chosen scales grow at most linearly in the correction index. -/
theorem riemannHypothesis_of_logarithmic_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ) (L : ℕ → ℝ)
    (C A : ℝ) (hC : 0 < C) (hA : 0 < A)
    (hgrowth : ∀ᶠ k in atTop, Real.log (L k) ≤ A * ((k : ℝ) + 1))
    (hb : ∀ᶠ k in atTop,
      CorrectionBudget (σ k) (σ (k + 1)) (C * Real.log (L k))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_linear_budgets σ hσ (C * A) (mul_pos hC hA)
  filter_upwards [hgrowth, hb] with k hk hbk
  apply hbk.mono
  calc
    C * Real.log (L k) ≤ C * (A * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hk hC.le
    _ = _ := by ring

/-- A concrete geometric-scale logarithmic specialization. -/
theorem riemannHypothesis_of_geometric_scale_logarithmic_budgets
    (σ : ℕ → ℕ) (hσ : Monotone σ)
    (C L : ℝ) (hC : 0 < C) (hL : 1 < L)
    (hb : ∀ᶠ k in atTop,
      CorrectionBudget (σ k) (σ (k + 1)) (C * Real.log (L ^ (k + 1)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_logarithmic_budgets σ hσ
    (fun k => L ^ (k + 1)) C (Real.log L) hC (Real.log_pos hL) _ hb
  exact Filter.Eventually.of_forall (fun k => by
    simp only [Real.log_pow, Nat.cast_add, Nat.cast_one]
    nlinarith)

/-- Under failure of RH, every eventual valid budget schedule has summable
reciprocals. No converse implication from RH to Q-density is used. -/
theorem summable_reciprocal_budgets_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis)
    (σ : ℕ → ℕ) (hσ : Monotone σ) (K : ℕ → ℝ)
    (hK : ∀ k, 0 < K k)
    (hb : ∀ᶠ k in atTop, CorrectionBudget (σ k) (σ (k + 1)) (K k)) :
    Summable (fun k => 1 / K k) := by
  by_contra h
  exact hRH (riemannHypothesis_of_reciprocal_budgets σ hσ K hK hb h)

end RiemannResearch.RH.QFullCorrectionBudgetDescent

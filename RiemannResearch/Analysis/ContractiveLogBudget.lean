import RiemannResearch.Analysis.ContractiveProducts
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete logarithmic budgets for positive contractive products

Source: independently formalized elementary product calculus for the user's
Ramanujan zero-product continuation, 23 October 2026. The exact logarithmic
slack precedes every bound. A positive product limit supplies summability;
no summability hypothesis is hidden in the infinite identities.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ContractiveLogBudget

def slack (a : ℝ) : ℝ := -Real.log a - (1 - a)

theorem slack_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ slack a := by
  have := Real.log_le_sub_one_of_pos ha
  unfold slack
  linarith

/-- Exact finite budget, including nonlinear logarithmic slack and unused mass. -/
theorem finite_budget_exact {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) {m : ℝ} (hm : 0 < m) :
    -Real.log m = (∑ i ∈ S, (1 - a i)) + (∑ i ∈ S, slack (a i)) +
      Real.log ((∏ i ∈ S, a i) / m) := by
  rw [Real.log_div (Finset.prod_pos ha).ne' hm.ne', Real.log_prod (fun i hi => (ha i hi).ne')]
  simp only [slack, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

theorem finite_defect_bound {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) {m : ℝ} (hm : 0 < m)
    (hprod : m ≤ ∏ i ∈ S, a i) :
    ∑ i ∈ S, (1 - a i) ≤ -Real.log m := by
  have he := finite_budget_exact S a ha hm
  have hs : 0 ≤ ∑ i ∈ S, slack (a i) :=
    Finset.sum_nonneg (fun i hi => slack_nonneg (ha i hi))
  have hr : 0 ≤ Real.log ((∏ i ∈ S, a i) / m) :=
    Real.log_nonneg ((le_div_iff₀ hm).mpr (by simpa using hprod))
  linarith

/-- Positive limiting product forces a convergent logarithmic charge. -/
theorem hasSum_neg_log (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) :
    HasSum (fun i => -Real.log (a i)) (-Real.log L) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun i => neg_nonneg.mpr (Real.log_nonpos (ha i).le (ha1 i))) _).2
  have h := ((Real.continuousAt_log hL.ne').tendsto.comp ht).neg
  have he (n : ℕ) : -Real.log (Real.partialProduct a n) =
      ∑ i ∈ Finset.range n, -Real.log (a i) := by
    rw [Real.partialProduct, Real.log_prod (fun i _ => (ha i).ne')]
    simp only [Finset.sum_neg_distrib]
  simpa only [Function.comp_def, he] using h

theorem summable_defect (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) :
    Summable (fun i => 1 - a i) := by
  apply Summable.of_nonneg_of_le (fun i => sub_nonneg.mpr (ha1 i))
    (fun i => ?_) (hasSum_neg_log a ha ha1 hL ht).summable
  have := slack_nonneg (ha i)
  unfold slack at this
  linarith

/-- Exact infinite budget: the first-order defect plus every nonlinear slack. -/
theorem infinite_budget_exact (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) :
    Summable (fun i => slack (a i)) ∧
      -Real.log L = (∑' i, (1 - a i)) + ∑' i, slack (a i) := by
  have hs := hasSum_neg_log a ha ha1 hL ht
  have hd := summable_defect a ha ha1 hL ht
  have hr : Summable (fun i => slack (a i)) := hs.summable.sub hd
  refine ⟨hr, ?_⟩
  have he := hd.tsum_add hr
  have hfun : (fun i => (1 - a i) + slack (a i)) = fun i => -Real.log (a i) := by
    funext i
    unfold slack
    ring
  rw [hfun, hs.tsum_eq] at he
  exact he

/-- The infinite first-order charge is bounded by the exact logarithmic loss. -/
theorem infinite_defect_bound (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) :
    (∑' i, (1 - a i)) ≤ -Real.log L := by
  have he := (infinite_budget_exact a ha ha1 hL ht).2
  have hs : 0 ≤ ∑' i, slack (a i) := tsum_nonneg (fun i => slack_nonneg (ha i))
  linarith

/-- An external positive mass leaves its exact unused logarithmic budget. -/
theorem infinite_budget_with_mass (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) {m : ℝ} (hm : 0 < m) :
    -Real.log m = (∑' i, (1 - a i)) + (∑' i, slack (a i)) + Real.log (L / m) := by
  rw [Real.log_div hL.ne' hm.ne']
  have he := (infinite_budget_exact a ha ha1 hL ht).2
  linarith

/-- Exact remaining charge at every cutoff, with all nonlinear slack retained. -/
theorem tail_budget_exact (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) (N : ℕ) :
    Real.log (Real.partialProduct a N / L) =
      (∑' i, (1 - a (i + N))) + ∑' i, slack (a (i + N)) := by
  have hi := infinite_budget_exact a ha ha1 hL ht
  have hd := summable_defect a ha ha1 hL ht
  have hdt := Summable.sum_add_tsum_nat_add N hd
  have hst := Summable.sum_add_tsum_nat_add N hi.1
  have hp := finite_budget_exact (Finset.range N) a (fun i _ => ha i)
    (show 0 < (1 : ℝ) from zero_lt_one)
  simp only [Real.log_one, neg_zero, div_one] at hp
  change 0 = (∑ i ∈ Finset.range N, (1 - a i)) +
    (∑ i ∈ Finset.range N, slack (a i)) + Real.log (Real.partialProduct a N) at hp
  have hpos : 0 < Real.partialProduct a N := Finset.prod_pos (fun i _ => ha i)
  rw [Real.log_div hpos.ne' hL.ne']
  linarith [hi.2]

theorem tail_defect_bound (a : ℕ → ℝ) (ha : ∀ i, 0 < a i)
    (ha1 : ∀ i, a i ≤ 1) {L : ℝ} (hL : 0 < L)
    (ht : Tendsto (Real.partialProduct a) atTop (𝓝 L)) (N : ℕ) :
    (∑' i, (1 - a (i + N))) ≤ Real.log (Real.partialProduct a N / L) := by
  rw [tail_budget_exact a ha ha1 hL ht N]
  exact le_add_of_nonneg_right (tsum_nonneg (fun i => slack_nonneg (ha (i + N))))

end RiemannResearch.Analysis.ContractiveLogBudget

import RiemannResearch.Analysis.BoundedMomentAverages
import RiemannResearch.Analysis.WeakConvergenceDenseTests
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual Q averages of bounded legal exact-head candidates

Source: the user-provided Q candidate discussion, 13 October 2026.
The sparse subsequence argument and complete signed finite Gram expansion
are reused from `Analysis.BoundedMomentAverages`.

This is a conditional research reduction. Exact physical heads and a
uniform bound on the full actual Q error are hypotheses. The module proves
neither that arithmetic bound nor an unconditional approximation of one.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QExactHeadAverages

open ZetaTwoHilbert
open RiemannResearch.Analysis

/-- The actual physical-coordinate tests have dense span in QHilbert. -/
theorem qPoint_span_dense :
    (Submodule.span ℝ (Set.range qPoint)).topologicalClosure = ⊤ := by
  have ho : (Submodule.span ℝ (Set.range qPoint))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro f hf
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext n
    have h : inner ℝ (qPoint n) f = 0 :=
      hf _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [qPoint_inner] at h
    have hp : qSequence f (n + 1) = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt (qWeight_pos n))
    rw [qSequence_succ] at hp
    have hs : Real.sqrt (qWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    change f n = 0
    exact (div_eq_zero_iff.mp hp).resolve_right hs
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho]
  simp

/-- Bounded actual Q residuals with progressively exact physical heads are
weakly null against every QHilbert vector. -/
theorem weak_residual_of_bounded_exact_heads
    (F : ℕ → QHilbert) {B : ℝ}
    (hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1)
    (x : QHilbert) :
    Tendsto (fun N => inner ℝ x (qOne - F N)) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (sq_nonneg ‖qOne - F 0‖).trans (hbound 0)
  have hb : ∀ᶠ N in atTop, ‖qOne - F N‖ ≤ B + 1 := by
    apply Filter.Eventually.of_forall
    intro N
    nlinarith [hbound N, sq_nonneg (‖qOne - F N‖ - 1)]
  have hp : ∀ y ∈ Set.range qPoint,
      Tendsto (fun N => inner ℝ y (qOne - F N)) atTop (𝓝 0) := by
    rintro y ⟨n, rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    rw [qPoint_inner]
    change 0 = qWeight n * qSequenceLinear (qOne - F N) (n + 1)
    rw [map_sub]
    change 0 = qWeight n * (qSequence qOne (n + 1) -
      qSequence (F N) (n + 1))
    rw [hhead N (n + 1) (Nat.succ_pos n) hN, qSequence_qOne]
    simp [qOneSequence]
  exact tendsto_inner_zero_of_mem_closure_span
    (by positivity) hb hp (by rw [qPoint_span_dense]; trivial)

/-- Every term is a finite equal-weight average of the original candidates. -/
def average (F : ℕ → QHilbert) (q : ℕ → ℕ) (m : ℕ) : QHilbert :=
  ((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, F (q i))

theorem average_mem (S : Submodule ℝ QHilbert)
    (F : ℕ → QHilbert) (q : ℕ → ℕ)
    (hlegal : ∀ n, F n ∈ S) (m : ℕ) : average F q m ∈ S := by
  exact S.smul_mem _ <| S.sum_mem (fun i _ => hlegal (q i))

theorem residual_average (F : ℕ → QHilbert) (q : ℕ → ℕ)
    {m : ℕ} (hm : 0 < m) :
    qOne - average F q m = ((m : ℝ)⁻¹) •
      (∑ i ∈ Finset.range m, (qOne - F (q i))) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hconst : (∑ _i ∈ Finset.range m, qOne) = (m : ℝ) • qOne := by
    simp only [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  rw [Finset.sum_sub_distrib, hconst, smul_sub, smul_smul,
    inv_mul_cancel₀ hm', one_smul]
  rfl

/-- Complete exact finite error: every signed cross pairing is retained. -/
theorem average_error_exact (F : ℕ → QHilbert) (q : ℕ → ℕ)
    {m : ℕ} (hm : 0 < m) :
    ‖qOne - average F q m‖ ^ 2 = ((m : ℝ)⁻¹) ^ 2 *
      ((∑ i ∈ Finset.range m, ‖qOne - F (q i)‖ ^ 2) +
        2 * prefixCross (fun i => qOne - F (q i)) m) := by
  rw [residual_average F q hm, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_sq_sum_range_eq_diagonal_add_cross]

/-- The error is the full infinite Q energy, with the physical zero anchor. -/
theorem average_error_weighted (F : ℕ → QHilbert) (q : ℕ → ℕ) (m : ℕ) :
    ‖qOne - average F q m‖ ^ 2 = ∑' n,
      positiveQWeight n * (qOneSequence n - qSequence (average F q m) n) ^ 2 := by
  rw [qNorm_weighted_sq]
  congr 1
  funext n
  change positiveQWeight n * (qSequenceLinear (qOne - average F q m) n) ^ 2 = _
  rw [map_sub]
  change positiveQWeight n * (qSequence qOne n - qSequence (average F q m) n) ^ 2 = _
  rw [qSequence_qOne]

private theorem average_budget_tendsto_zero (B : ℝ) :
    Tendsto (fun m : ℕ => B / m + 4 / (m : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hh := (h.const_mul B).add ((h.pow 2).const_mul 4)
  simpa only [div_pow, one_pow, mul_one_div, mul_zero, zero_pow
    (by norm_num : 2 ≠ 0), zero_add] using hh

theorem average_tendsto_of_error_bound
    (F : ℕ → QHilbert) (q : ℕ → ℕ) {B : ℝ}
    (herror : ∀ m : ℕ, 0 < m →
      ‖qOne - average F q m‖ ^ 2 ≤ B / m + 4 / (m : ℝ) ^ 2) :
    Tendsto (average F q) atTop (𝓝 qOne) := by
  have hsquare : Tendsto (fun m => ‖qOne - average F q m‖ ^ 2)
      atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      exact Filter.Eventually.of_forall (fun m => hx.trans_le (sq_nonneg _))
    · intro ε hε
      filter_upwards [eventually_gt_atTop 0,
        (average_budget_tendsto_zero B).eventually (gt_mem_nhds hε)] with m hm he
      exact (herror m hm).trans_lt he
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hn' : Tendsto (fun m => ‖qOne - average F q m‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hn'

/-- A single uniform bound on actual exact-head error supplies actual finite
legal averages converging to one, with a rate for every positive length.
The index selection is the existing sparse weak-null selection; no
independence or missing-tail estimate is assumed. -/
theorem exists_legal_averages_of_bounded_exact_heads
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert)
    (hlegal : ∀ n, F n ∈ S) {B : ℝ}
    (hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      (∀ m, average F q m ∈ S) ∧
      (∀ m : ℕ, 0 < m → ‖qOne - average F q m‖ ^ 2 ≤
        B / m + 4 / (m : ℝ) ^ 2) ∧
      Tendsto (average F q) atTop (𝓝 qOne) := by
  obtain ⟨q, hq, havg⟩ := exists_strictMono_average_norm_sq_bound
    (fun n => qOne - F n) hbound
    (weak_residual_of_bounded_exact_heads F hbound hhead)
  have he (m : ℕ) (hm : 0 < m) :
      ‖qOne - average F q m‖ ^ 2 ≤ B / m + 4 / (m : ℝ) ^ 2 := by
    rw [residual_average F q hm]
    exact havg m hm
  exact ⟨q, hq, average_mem S F q hlegal, he, average_tendsto_of_error_bound F q he⟩

/-- A bound on the literal finite reciprocal tail over each candidate's
period supplies the full Q bound, with the same constant B. Exact heads
remove the initial segment by an equality before the period comparison.
This is the explicit arithmetic hypothesis still needed in applications. -/
theorem exists_legal_averages_of_periodic_exact_head_tail_bound
    (S : Submodule ℝ QHilbert) (F : ℕ → QHilbert) (L : ℕ → ℕ)
    (hlegal : ∀ n, F n ∈ S)
    (hL : ∀ N, 0 < L N)
    (hbounded : ∀ N, ∃ C : ℝ, ∀ n, |qSequence (F N) n| ≤ C)
    (hperiod : ∀ N n, qSequence (F N) (n + L N) = qSequence (F N) n)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1)
    {B : ℝ}
    (htail : ∀ N, (∑ a ∈ Finset.Icc (N + 1) (L N),
      |1 - qSequence (F N) a| ^ 2 / (a : ℝ) ^ 2) ≤ B) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      (∀ m, average F q m ∈ S) ∧
      (∀ m : ℕ, 0 < m → ‖qOne - average F q m‖ ^ 2 ≤
        B / m + 4 / (m : ℝ) ^ 2) ∧
      Tendsto (average F q) atTop (𝓝 qOne) := by
  apply exists_legal_averages_of_bounded_exact_heads S F hlegal _ hhead
  intro N
  obtain ⟨C, hC⟩ := hbounded N
  have hb := (ZetaTwoProbability.periodic_qError_comparison (L N) (hL N)
    (F N) hC (hperiod N)).2
  rw [Pareto.crtReciprocalEnergy_eq_Icc_tail N (L N) _
    (by intro n hn hnN; rw [hhead N n hn hnN]; ring)] at hb
  exact hb.trans (htail N)

end RiemannResearch.RH.QExactHeadAverages

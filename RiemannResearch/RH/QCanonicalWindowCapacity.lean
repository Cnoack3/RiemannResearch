/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCanonicalWindowMinimum
import RiemannResearch.RH.QCanonicalMovingCovariance
import RiemannResearch.RH.QCanonicalMetricAsymptotics
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.Analysis.FiniteGramSchurBounds
import RiemannResearch.Analysis.FiniteGramCapacityIncrement
import RiemannResearch.Analysis.FiniteGramOneStepCapacity
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact capacity recurrence for complete canonical Q windows

Source: the user's 15 October 2026 request, specializing
FiniteGramOneStepCapacity.one_step_normal_mass_increment to the actual
normalQ constructed in QCanonicalWindowMinimum. The analogous Pareto
window-recursion module supplies the family-map proof strategy.
No mathematical novelty claim is made.

All norms and pairings are complete Q Hilbert quantities. The signed source
and all Schur cross terms are retained before giving inequalities.
Finite monotonicity, a positive Schur denominator, and arbitrarily late strict
gains do not prove a common positive lower bound along growing heads.
The RH theorem below retains that arithmetic obligation explicitly.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.QCanonicalWindowCapacity
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCanonicalWindowMinimum QCanonicalMovingCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The actual inverse-Gram all-ones mass. -/
def normalMass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : ℝ :=
  ∑ i, normalQ N M hN hNM i

def normalVector (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : QHilbert :=
  Fintype.linearCombination ℝ (windowFamily N M) (normalQ N M hN hNM)

def screening (N M T : ℕ) : Fin (M - N + 1) → ℝ :=
  screeningCoeff (windowFamily N M) (residual T)

/-- Complete infinite energy after orthogonal old-window screening. -/
def schur (N M T : ℕ) : ℝ :=
  ‖screenedVector (windowFamily N M) (residual T)‖ ^ 2

/-- The signed all-ones source defect; no absolute values are inserted. -/
def defect (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (T : ℕ) : ℝ :=
  1 - inner ℝ (residual T) (normalVector N M hN hNM)

def windowGain (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : ℝ :=
  (defect N M hN hNM (M + 1)) ^ 2 / schur N M (M + 1)

theorem normalMass_pos (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 < normalMass N M hN hNM := normalQ_mass_pos N M hN hNM

theorem normalVector_energy (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ‖normalVector N M hN hNM‖ ^ 2 = normalMass N M hN hNM :=
  normal_synthesis_energy _ _ (normalQ_normal N M hN hNM)

theorem normalMass_diagonal (N : ℕ) (hN : 0 < N) :
    normalMass N N hN le_rfl = (‖residual N‖ ^ 2)⁻¹ := by
  have hres (i : Fin (N - N + 1)) : windowFamily N N i = residual N := by
    change residual (N + i.val) = residual N
    have hi : i.val = 0 := by
      have := i.isLt
      omega
    rw [hi, Nat.add_zero]
  have h := congrFun (normalQ_normal N N hN le_rfl)
    (⟨0, by omega⟩ : Fin (N - N + 1))
  have hm : normalMass N N hN le_rfl * ‖residual N‖ ^ 2 = 1 := by
    have h' : ‖residual N‖ ^ 2 * normalMass N N hN le_rfl = 1 := by
      simpa only [gram_apply, hres, real_inner_self_eq_norm_sq,
        ← Finset.mul_sum, normalMass] using h
    simpa only [mul_comm] using h'
  have hE : ‖residual N‖ ^ 2 ≠ 0 := by
    intro he
    rw [he, mul_zero] at hm
    norm_num at hm
  rw [← one_div]
  exact (eq_div_iff hE).mpr hm

/-- Exact Schur expansion, including the complete signed projection term. -/
theorem schur_expansion (N M T : ℕ) :
    schur N M T = ‖residual T‖ ^ 2 -
      ∑ i, screening N M T i * inner ℝ (windowFamily N M i) (residual T) := by
  exact screenedVector_energy (windowFamily N M) (residual T)

theorem defect_expansion (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (T : ℕ) :
    defect N M hN hNM T = 1 -
      ∑ i, normalQ N M hN hNM i * inner ℝ (windowFamily N M i) (residual T) := by
  unfold defect normalVector
  rw [real_inner_comm, inner_synthesis_left]

theorem defect_eq_one_sub_sum (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (T : ℕ) :
    defect N M hN hNM T = 1 - ∑ i, screening N M T i := by
  unfold defect normalVector
  rw [screeningCoeff_source _ _ _ (normalQ_normal N M hN hNM)]
  rfl

theorem schur_le_energy (N M T : ℕ) :
    schur N M T ≤ ‖residual T‖ ^ 2 :=
  screenedVector_energy_le (windowFamily N M) (residual T)

/-- Exact normal-vector increment for any nested contiguous windows. -/
theorem normalMass_increment (N M L : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (hML : M ≤ L) :
    normalMass N L hN (by omega) - normalMass N M hN hNM =
      ‖normalVector N L hN (by omega) - normalVector N M hN hNM‖ ^ 2 := by
  exact normal_mass_increment_of_family_map
    (windowFamily N M) (windowFamily N L)
    (normalQ N M hN hNM) (normalQ N L hN (by omega))
    (normalQ_normal N M hN hNM) (normalQ_normal N L hN (by omega))
    (fun i => ⟨i.val, by omega⟩) (fun _ => rfl)

theorem normalMass_mono (N M L : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (hML : M ≤ L) :
    normalMass N M hN hNM ≤ normalMass N L hN (by omega) := by
  have h := normalMass_increment N M L hN hNM hML
  nlinarith only [h,
    sq_nonneg ‖normalVector N L hN (by omega) - normalVector N M hN hNM‖]

private def successorFamily (N M : ℕ) : (Fin (M - N + 1) ⊕ Unit) → QHilbert :=
  Sum.elim (windowFamily N M) (fun _ => residual (M + 1))

private def successorIndex (N M : ℕ) (hNM : N ≤ M) :
    (Fin (M - N + 1) ⊕ Unit) → Fin (M + 1 - N + 1) :=
  Sum.elim (fun i => ⟨i.val, by omega⟩) (fun _ => ⟨M + 1 - N, by omega⟩)

private theorem successorIndex_injective (N M : ℕ) (hNM : N ≤ M) :
    Function.Injective (successorIndex N M hNM) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hv := congrArg Fin.val hij
      exact congrArg Sum.inl (Fin.ext hv)
    | inr j =>
      have hv := congrArg Fin.val hij
      dsimp [successorIndex] at hv
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hv := congrArg Fin.val hij
      dsimp [successorIndex] at hv
      omega
    | inr j => cases i; cases j; rfl

private theorem successorFamily_eq_comp (N M : ℕ) (hNM : N ≤ M) :
    successorFamily N M = (windowFamily N (M + 1)) ∘ successorIndex N M hNM := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    change residual (M + 1) = residual (N + (M + 1 - N))
    congr 1
    omega

private theorem successorFamily_independent (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    LinearIndependent ℝ (successorFamily N M) := by
  rw [successorFamily_eq_comp N M hNM]
  exact (windowFamily_linearIndependent N (M + 1) hN (by omega)).comp
    (successorIndex N M hNM) (successorIndex_injective N M hNM)

private def successorNormal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    (Fin (M - N + 1) ⊕ Unit) → ℝ :=
  (gramEquiv (successorFamily_independent N M hN hNM)).symm (fun _ => 1)

private theorem successorNormal_normal (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    gram (successorFamily N M) (successorNormal N M hN hNM) = fun _ => 1 :=
  (gramEquiv (successorFamily_independent N M hN hNM)).apply_symm_apply _

/-- Reindexing is discharged by maps in both directions, rather than an
assumption that a differently indexed Gram inverse has the same mass. -/
private theorem successorNormal_mass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    (∑ i, successorNormal N M hN hNM i) = normalMass N (M + 1) hN (by omega) := by
  let d : Fin (M + 1 - N + 1) → (Fin (M - N + 1) ⊕ Unit) := fun j =>
    if hj : j.val < M - N + 1 then Sum.inl ⟨j.val, hj⟩ else Sum.inr ()
  have hd : ∀ j, windowFamily N (M + 1) j = successorFamily N M (d j) := by
    intro j
    dsimp [d]
    split_ifs with hj
    · rfl
    · change residual (N + j.val) = residual (M + 1)
      congr 1
      omega
  have he : ∀ j, successorFamily N M j =
      windowFamily N (M + 1) (successorIndex N M hNM j) :=
    fun j => congrFun (successorFamily_eq_comp N M hNM) j
  have h₁ := normal_mass_increment_of_family_map
    (successorFamily N M) (windowFamily N (M + 1))
    (successorNormal N M hN hNM) (normalQ N (M + 1) hN (by omega))
    (successorNormal_normal N M hN hNM) (normalQ_normal N (M + 1) hN (by omega))
    (successorIndex N M hNM) he
  have h₂ := normal_mass_increment_of_family_map
    (windowFamily N (M + 1)) (successorFamily N M)
    (normalQ N (M + 1) hN (by omega)) (successorNormal N M hN hNM)
    (normalQ_normal N (M + 1) hN (by omega)) (successorNormal_normal N M hN hNM) d hd
  have hp₁ := sq_nonneg ‖Fintype.linearCombination ℝ (windowFamily N (M + 1))
      (normalQ N (M + 1) hN (by omega)) -
    Fintype.linearCombination ℝ (successorFamily N M) (successorNormal N M hN hNM)‖
  have hp₂ := sq_nonneg ‖Fintype.linearCombination ℝ (successorFamily N M)
      (successorNormal N M hN hNM) -
    Fintype.linearCombination ℝ (windowFamily N (M + 1)) (normalQ N (M + 1) hN (by omega))‖
  change (∑ i, successorNormal N M hN hNM i) =
    ∑ i, normalQ N (M + 1) hN (by omega) i
  linarith only [h₁, h₂, hp₁, hp₂]

/-- The requested exact recurrence for actual contiguous Q windows. -/
theorem normalMass_succ_sub (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    normalMass N (M + 1) hN (by omega) - normalMass N M hN hNM =
      (defect N M hN hNM (M + 1)) ^ 2 / schur N M (M + 1) := by
  have h := one_step_normal_mass_increment (windowFamily N M) (residual (M + 1))
    (normalQ N M hN hNM) (successorNormal N M hN hNM)
    (normalQ_normal N M hN hNM) (successorNormal_normal N M hN hNM)
  rw [successorNormal_mass] at h
  exact h

/-- Independence proves denominator positivity, not source nonvanishing. -/
theorem schur_succ_pos (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 < schur N M (M + 1) :=
  screenedVector_energy_pos_of_linearIndependent (windowFamily N M) (residual (M + 1))
    (successorFamily_independent N M hN hNM)

theorem windowGain_nonneg (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 ≤ windowGain N M hN hNM := by
  unfold windowGain schur
  positivity

theorem normalMass_succ_strict_iff (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    normalMass N M hN hNM < normalMass N (M + 1) hN (by omega) ↔
      defect N M hN hNM (M + 1) ≠ 0 := by
  rw [← sub_pos, normalMass_succ_sub,
    div_pos_iff_of_pos_right (schur_succ_pos N M hN hNM), sq_pos_iff]

/-- Exact finite telescoping of all the complete signed Schur gains. -/
theorem normalMass_telescope (N M L : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    normalMass N (M + L) hN (by omega) = normalMass N M hN hNM +
      ∑ j ∈ Finset.range L, windowGain N (M + j) hN (by omega) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hs := normalMass_succ_sub N (M + L) hN (by omega)
    change normalMass N (M + L + 1) hN (by omega) -
      normalMass N (M + L) hN (by omega) = windowGain N (M + L) hN (by omega) at hs
    change normalMass N (M + L + 1) hN (by omega) = _
    rw [Finset.sum_range_succ]
    linarith only [hs, ih]

theorem normalMass_eq_base_add_gains (N L : ℕ) (hN : 0 < N) :
    normalMass N (N + L) hN (by omega) = (‖residual N‖ ^ 2)⁻¹ +
      ∑ j ∈ Finset.range L, windowGain N (N + j) hN (by omega) := by
  rw [normalMass_telescope N N L hN le_rfl, normalMass_diagonal]

/-- Every failed normal equation in a later window bounds its total gain. -/
theorem defect_sq_le_window_gain (N M L T : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (hML : M ≤ L) (hNT : N ≤ T) (hTL : T ≤ L) :
    (defect N M hN hNM T) ^ 2 ≤ ‖residual T‖ ^ 2 *
      (normalMass N L hN (by omega) - normalMass N M hN hNM) := by
  have h := normal_equation_defect_sq_le_gain (windowFamily N M) (windowFamily N L)
    (normalQ N M hN hNM) (normalQ N L hN (by omega))
    (normalQ_normal N M hN hNM) (normalQ_normal N L hN (by omega))
    (fun i => ⟨i.val, by omega⟩) (fun _ => rfl)
    (⟨T - N, by omega⟩ : Fin (L - N + 1))
  have he : windowFamily N L (⟨T - N, by omega⟩ : Fin (L - N + 1)) = residual T := by
    change residual (N + (T - N)) = residual T
    congr 1
    omega
  rw [he] at h
  exact h

/-- A computable physical-amplitude bound for the actual inverse-Gram normal.
Its growth is not controlled by finite positivity of the Gram matrix. -/
def normalAmplitude (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) : ℝ :=
  ∑ i, |normalQ N M hN hNM i| * (1 + 2 * ((N + i.val : ℕ) : ℝ))

theorem normalAmplitude_nonneg (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    0 ≤ normalAmplitude N M hN hNM := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (by positivity))

theorem normalVector_physical_bound (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (n : ℕ) (hn : 0 < n) :
    |qSequence (normalVector N M hN hNM) n| ≤ normalAmplitude N M hN hNM := by
  have he : qSequence (normalVector N M hN hNM) n =
      ∑ i, normalQ N M hN hNM i * qSequence (windowFamily N M i) n := by
    change qSequenceLinear (Fintype.linearCombination ℝ (windowFamily N M)
      (normalQ N M hN hNM)) n = _
    simp only [Fintype.linearCombination_apply, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (physical_bound (N + i.val) (by omega) n hn)
    (abs_nonneg _)

/-- Quantitative source control from the sharper existing Q covariance bound. -/
theorem defect_control (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) (T : ℕ) :
    (1 - defect N M hN hNM T) ^ 2 ≤
      ((1 + 1 / ((T : ℝ) + 1)) / zetaTwo) *
        (normalAmplitude N M hN hNM) ^ 2 * energyRate T := by
  have h := QCanonicalMetricAsymptotics.inner_sq_le_sharp
    (normalVector N M hN hNM) T (normalAmplitude N M hN hNM)
    (normalAmplitude_nonneg N M hN hNM) (normalVector_physical_bound N M hN hNM)
  simpa only [defect, sub_sub_cancel, real_inner_comm] using h

/-- The old window is fixed here. This does not control the moving screening
normal in the contiguous-window recurrence uniformly in M. -/
theorem fixed_window_defect_tendsto_one (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    Tendsto (fun T => defect N M hN hNM T) atTop (𝓝 1) := by
  have hrate : Tendsto energyRate atTop (𝓝 0) :=
    squeeze_zero energyRate_nonneg energyRate_le_pareto (by
      simpa only [mul_zero] using
        QCanonicalMetricAsymptotics.pareto_energyRate_tendsto_zero.const_mul (2 / zetaTwo))
  have ht := moving_test_tendsto (fun _ => normalVector N M hN hNM)
    (fun _ => normalAmplitude N M hN hNM)
    (fun _ => normalAmplitude_nonneg N M hN hNM)
    (fun _ => normalVector_physical_bound N M hN hNM)
    (by simpa only [mul_zero] using hrate.const_mul ((normalAmplitude N M hN hNM) ^ 2))
  have hs := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub ht
  simpa only [defect, real_inner_comm, sub_zero] using hs

/-- Unconditional absence of a terminal plateau at each fixed positive head.
Strict increases may have finite total size; no divergence is concluded. -/
theorem exists_larger_normalMass (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    ∃ L : ℕ, ∃ hML : M < L,
      normalMass N M hN hNM < normalMass N L hN (by omega) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((fixed_window_defect_tendsto_one N M hN hNM).eventually
      (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  let L := max (M + 1) K
  have hML : M < L := lt_of_lt_of_le (Nat.lt_succ_self M) (le_max_left _ _)
  have hδ : (1 / 2 : ℝ) < defect N M hN hNM L := hK L (le_max_right _ _)
  have hg := defect_sq_le_window_gain N M L L hN hNM (by omega) (by omega) le_rfl
  refine ⟨L, hML, ?_⟩
  by_contra hnot
  have hp : ‖residual L‖ ^ 2 *
      (normalMass N L hN (by omega) - normalMass N M hN hNM) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  nlinarith only [hg, hp, hδ, sq_nonneg (defect N M hN hNM L - 1 / 2)]

/-- When the explicit moving-normal amplitude budget is small enough, a
complete-energy reciprocal gives a certified contiguous gain. The budget
is a testable finite condition, not an unconditional uniform provider. -/
theorem step_gain_lower_of_amplitude_budget (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M)
    (hbudget : ((1 + 1 / (((M + 1 : ℕ) : ℝ) + 1)) / zetaTwo) *
      (normalAmplitude N M hN hNM) ^ 2 * energyRate (M + 1) ≤ 1 / 4) :
    (1 / 4 : ℝ) / ‖residual (M + 1)‖ ^ 2 ≤
      normalMass N (M + 1) hN (by omega) - normalMass N M hN hNM := by
  have hb := (defect_control N M hN hNM (M + 1)).trans hbudget
  have ha : |1 - defect N M hN hNM (M + 1)| ≤ (1 / 2 : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    simpa only [sq_abs, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num] using hb
  have hδ : (1 / 2 : ℝ) ≤ defect N M hN hNM (M + 1) := by
    linarith only [(abs_le.mp ha).2]
  have hδsq : (1 / 4 : ℝ) ≤ (defect N M hN hNM (M + 1)) ^ 2 := by
    nlinarith only [hδ, sq_nonneg (defect N M hN hNM (M + 1) - 1 / 2)]
  have hg := defect_sq_le_window_gain N M (M + 1) (M + 1)
    hN hNM (by omega) (by omega) le_rfl
  have hE : 0 < ‖residual (M + 1)‖ ^ 2 :=
    (schur_succ_pos N M hN hNM).trans_le (schur_le_energy N M (M + 1))
  apply (div_le_iff₀ hE).mpr
  nlinarith only [hδsq, hg]

/-- Conditional research reduction: finite cumulative gain crossing one
common threshold is enough. No divergence at each fixed head is required.
Open: an arithmetic provider for this growing-head threshold. -/
theorem riemannHypothesis_of_cumulative_gain_lower
    (L : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hbudget : ∀ j,
      c ≤ normalMass (j + 1) (j + 1) (by omega) le_rfl +
        ∑ k ∈ Finset.range (L j), windowGain (j + 1) (j + 1 + k) (by omega) (by omega)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_normalQ_mass_lower (fun j => j + 1 + L j)
    (fun _ => by omega) c hc
  intro j
  change c ≤ normalMass (j + 1) (j + 1 + L j) (by omega) (by omega)
  rw [normalMass_telescope (j + 1) (j + 1) (L j) (by omega) le_rfl]
  exact hbudget j

end RiemannResearch.RH.QCanonicalWindowCapacity

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeEpsilonCriterion
import RiemannResearch.RH.QExactHeadEpsilonBounds
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QCRTFiniteCertificates
import RiemannResearch.RH.QCRTPeriod9699690Certificate
import RiemannResearch.RH.QSquarefreeLatticePackets
import Mathlib.NumberTheory.Primorial
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional dyadic schedules of actual constrained minima

Source: the user's forall-epsilon/exists-witness CRT research request,
29 October 2026. The fixed heads are H(n) = 5 * 4^n and the complete-error
tolerances are epsilon(n) = 2^(-n). A successful energy witness may always
be moved to a later period. This gives strictly increasing, cofinal period
indices while retaining the actual constrained minimizers.

All convergence conclusions in this file depend on an explicit arithmetic
provider. No theorem here proves that provider. The elementary head schedule,
its tail budget, and period-envelope properties are unconditional.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTDyadicEpsilonSchedule
open ZetaTwoHilbert ZetaTwoProbability QCRTPeriodHeadBalance
open QExactHeadEpsilonBounds QSquarefreeEpsilonCriterion

def epsilon (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def head (n : ℕ) : ℕ := 5 * 4 ^ n

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

theorem epsilon_succ (n : ℕ) : epsilon (n + 1) = epsilon n / 2 := by
  simp only [epsilon, pow_succ]
  ring

theorem epsilon_le_one (n : ℕ) : epsilon n ≤ 1 := by
  induction n with
  | zero => norm_num [epsilon]
  | succ n ih => rw [epsilon_succ]; linarith

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem head_pos (n : ℕ) : 0 < head n := by
  unfold head
  positivity

theorem head_succ (n : ℕ) : head (n + 1) = 4 * head n := by
  simp only [head, pow_succ]
  ring

theorem head_strictMono : StrictMono head := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [head_succ]
  have := head_pos n
  omega

theorem head_tendsto : Tendsto head atTop atTop := head_strictMono.tendsto_atTop

theorem head_mul_epsilon_sq (n : ℕ) : (head n : ℝ) * epsilon n ^ 2 = 5 := by
  induction n with
  | zero => norm_num [head, epsilon]
  | succ n ih =>
    rw [head_succ, epsilon_succ]
    push_cast
    nlinarith [ih]

theorem head_tail_budget (n : ℕ) : targetTail (head n) ≤ epsilon n ^ 2 / 8 := by
  apply targetTail_le_of_cutoff (head n) (head_pos n) (epsilon n)
  nlinarith [head_mul_epsilon_sq n]

/-- The rational Q-tail estimate gives a sharper constant for this head schedule. -/
theorem dyadic_error_sq_bound (n : ℕ) (f : QHilbert)
    (hh : ∀ k, 0 < k → k ≤ head n → qSequence f k = 1)
    (he : ‖f‖ ^ 2 ≤ 1 + epsilon n ^ 2 / 8) :
    ‖qOne - f‖ ^ 2 ≤ (1841 / 2500 : ℝ) * epsilon n ^ 2 := by
  have hH : (0 : ℝ) < head n := by exact_mod_cast head_pos n
  have ht : targetTail (head n) ≤ (76 / 625 : ℝ) * epsilon n ^ 2 := by
    apply le_trans (targetTail_le_rational (head n) (head_pos n))
    apply (div_le_iff₀ hH).mpr
    nlinarith [head_mul_epsilon_sq n]
  have hb := error_sq_le_head_energy (head n) f hh
  nlinarith

/-- The unproved arithmetic input is a separate finite witness at each tolerance. -/
def DyadicMinimumProvider : Prop := ∀ n : ℕ, ∃ j : ℕ,
  head n ≤ j + 1 ∧ ‖minimumAt j (head n)‖ ^ 2 ≤ 1 + epsilon n ^ 2 / 8

/-- The published provider implies this fixed-head provider, by asking for
half the tolerance and then dropping surplus head constraints. -/
theorem dyadicProvider_of_minimum_energy_witnesses
    (h : ∀ ε : ℝ, 0 < ε → ∃ j H : ℕ,
      0 < H ∧ H ≤ j + 1 ∧ (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2 ∧
      ‖minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) :
    DyadicMinimumProvider := by
  intro n
  obtain ⟨j, H, _, hHj, hcut, he⟩ :=
    h (epsilon n / 2) (div_pos (epsilon_pos n) (by norm_num))
  have heps : 0 < epsilon n ^ 2 := sq_pos_of_pos (epsilon_pos n)
  have hheadR : (head n : ℝ) ≤ (H : ℝ) := by
    apply (mul_le_mul_iff_left₀ heps).mp
    nlinarith [head_mul_epsilon_sq n]
  have hhead : head n ≤ H := by exact_mod_cast hheadR
  refine ⟨j, hhead.trans hHj, ?_⟩
  have hc := minimumAt_head_cost j (head n) H hhead
  nlinarith [sq_nonneg ‖minimumAt j H - minimumAt j (head n)‖]

/-- Discretizing the tolerances and fixing these heads does not strengthen
the published arithmetic provider. Both formulations remain unproved. -/
theorem dyadicProvider_iff_minimum_energy_witnesses :
    DyadicMinimumProvider ↔
      (∀ ε : ℝ, 0 < ε → ∃ j H : ℕ,
        0 < H ∧ H ≤ j + 1 ∧ (608 / 125 : ℝ) ≤ (H : ℝ) * ε ^ 2 ∧
        ‖minimumAt j H‖ ^ 2 ≤ 1 + ε ^ 2 / 8) := by
  constructor
  · intro h ε hε
    obtain ⟨n, hn⟩ := ((tendsto_order.mp epsilon_tendsto).2 ε hε).exists
    obtain ⟨j, hhead, he⟩ := h n
    have hp : 0 ≤ (ε - epsilon n) * (ε + epsilon n) :=
      mul_nonneg (sub_nonneg.mpr hn.le) (add_nonneg hε.le (epsilon_pos n).le)
    have hsq : epsilon n ^ 2 ≤ ε ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (head n) : (0 : ℝ) ≤ _)
    refine ⟨j, head n, head_pos n, hhead, ?_, ?_⟩
    · nlinarith [head_mul_epsilon_sq n]
    · linarith
  · exact dyadicProvider_of_minimum_energy_witnesses

/-- A running maximum with one index of slack makes the chosen period indices strictly grow. -/
def periodEnvelope (j : ℕ → ℕ) : ℕ → ℕ
  | 0 => j 0
  | n + 1 => max (j (n + 1)) (periodEnvelope j n + 1)

theorem periodEnvelope_dom (j : ℕ → ℕ) (n : ℕ) : j n ≤ periodEnvelope j n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem periodEnvelope_strictMono (j : ℕ → ℕ) : StrictMono (periodEnvelope j) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

theorem periodEnvelope_tendsto (j : ℕ → ℕ) :
    Tendsto (periodEnvelope j) atTop atTop := (periodEnvelope_strictMono j).tendsto_atTop

/-- Conditional conclusion for actual minimum-energy vectors, with an explicit
geometric complete-error bound and increasing, cofinal period indices. -/
theorem exists_cofinal_minimum_schedule (h : DyadicMinimumProvider) :
    ∃ J : ℕ → ℕ, StrictMono J ∧ Tendsto J atTop atTop ∧
      (∀ n, head n ≤ J n + 1) ∧
      (∀ n, minimumAt (J n) (head n) ∈ qSquarefreeCRTSpan) ∧
      (∀ n k, 0 < k → k ≤ head n → qSequence (minimumAt (J n) (head n)) k = 1) ∧
      (∀ n, ‖minimumAt (J n) (head n)‖ ^ 2 ≤ 1 + epsilon n ^ 2 / 8) ∧
      (∀ n, ‖qOne - minimumAt (J n) (head n)‖ < epsilon n) ∧
      (∀ n, ‖minimumAt (J n) (head n)‖ ^ 2 ≤ 9 / 8) ∧
      Tendsto (fun n => minimumAt (J n) (head n)) atTop (𝓝 qOne) := by
  classical
  choose j hhead henergy using h
  let J : ℕ → ℕ := periodEnvelope j
  have hheadJ (n : ℕ) : head n ≤ J n + 1 :=
    (hhead n).trans (Nat.add_le_add_right (periodEnvelope_dom j n) 1)
  have he (n : ℕ) : ‖minimumAt (J n) (head n)‖ ^ 2 ≤ 1 + epsilon n ^ 2 / 8 :=
    minimum_energy_witness_at_later_period (j n) (J n) (head n)
      (periodEnvelope_dom j n) (hhead n) (epsilon n) (henergy n)
  have herr (n : ℕ) : ‖qOne - minimumAt (J n) (head n)‖ < epsilon n :=
    norm_error_lt_of_epsilon_budget (head n) (minimumAt (J n) (head n))
      (minimumAt_head (J n) (head n) (hheadJ n)) (epsilon n) (epsilon_pos n)
      (he n) (head_tail_budget n)
  refine ⟨J, periodEnvelope_strictMono j, periodEnvelope_tendsto j,
    hheadJ, fun n => minimumAt_legal _ _,
    fun n => minimumAt_head _ _ (hheadJ n), he, herr, ?_, ?_⟩
  · intro n
    have := he n
    have := epsilon_le_one n
    have := epsilon_pos n
    have hsq : 0 ≤ (1 - epsilon n) * (1 + epsilon n) :=
      mul_nonneg (sub_nonneg.mpr (epsilon_le_one n)) (by linarith [epsilon_pos n])
    nlinarith
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hz := squeeze_zero (fun n => norm_nonneg (qOne - minimumAt (J n) (head n)))
      (fun n => (herr n).le) epsilon_tendsto
    simpa only [norm_sub_rev] using hz

open ZetaTwoHilbert QCRTPeriodHeadBalance QCRTFiniteCertificates QSquarefreeLatticePackets
theorem dyadic_zero_certificate :
    head 0 ≤ 4 + 1 ∧ ‖minimumAt 4 (head 0)‖ ^ 2 ≤ 1 + epsilon 0 ^ 2 / 8 := by
  constructor
  · norm_num [head]
  · have hp : primorial (4 + 2) = 30 := by decide
    have hc := minimumAt_completion 4 5 (by norm_num) thirtyCertificate
      (by simpa only [hp] using thirtyCertificate_mem_stage) thirtyCertificate_exact_head
    have he := thirtyCertificate_energy_le_one
    norm_num only [head, epsilon, pow_zero, mul_one, one_div_one] at *
    nlinarith [sq_nonneg ‖thirtyCertificate - minimumAt 4 5‖]
theorem dyadic_one_certificate :
    head 1 ≤ 19 + 1 ∧ ‖minimumAt 19 (head 1)‖ ^ 2 ≤ 1 + epsilon 1 ^ 2 / 8 := by
  constructor
  · norm_num [head]
  · have hp : primorial (19 + 2) = 9699690 := by decide
    have hc := minimumAt_completion 19 20 (by norm_num)
      QCRTPeriod9699690Certificate.certificate
      (by simpa only [hp] using QCRTPeriod9699690Certificate.certificate_mem_stage)
      QCRTPeriod9699690Certificate.certificate_exact_head
    have he := QCRTPeriod9699690Certificate.certificate_energy_bound
    norm_num only [head, epsilon, pow_one, Nat.cast_ofNat] at *
    nlinarith [sq_nonneg ‖QCRTPeriod9699690Certificate.certificate - minimumAt 19 20‖]
end RiemannResearch.RH.QCRTDyadicEpsilonSchedule

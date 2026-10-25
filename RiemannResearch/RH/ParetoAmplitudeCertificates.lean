/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoWeights
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Refinable complete Pareto energy certificates

Source: user-provided capacity/energy agenda, 24 October 2026, and the
elementary summable-series head/tail decomposition. Physical coordinates
are indexed by n + 1. No omitted tail is silently discarded. The explicit
cutoff gives certificates within one of the true energy, preserving
regularized reciprocal mass within a factor of two.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.AmplitudeCertificates
open RiemannResearch.RH.Pareto

def energy (r : ℕ → ℝ) : ℝ := ∑' n, paretoWeight n * (r (n + 1))^2
def head (r : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, paretoWeight n * (r (n + 1))^2
def tail (r : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑' n, paretoWeight (n + K) * (r (n + K + 1))^2
def certificate (r : ℕ → ℝ) (U : ℝ) (K : ℕ) : ℝ :=
  head r K + U ^ 2 / ((K : ℝ)+1)

theorem energy_summable (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) :
    Summable (fun n => paretoWeight n * (r (n + 1))^2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
    (fun n => ?_) (paretoWeight_hasSum.summable.mul_right (U ^ 2))
  exact mul_le_mul_of_nonneg_left
    (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr (hr n))
    (paretoWeight_pos n).le

theorem head_add_tail_exact (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) (K : ℕ) :
    head r K + tail r K = energy r := by
  exact (energy_summable r U hU hr).sum_add_tsum_nat_add K

theorem tail_nonneg (r : ℕ → ℝ) (K : ℕ) : 0 ≤ tail r K :=
  tsum_nonneg (fun _n => mul_nonneg (paretoWeight_pos _).le (sq_nonneg _))

theorem tail_le (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) (K : ℕ) :
    tail r K ≤ U ^ 2 / ((K : ℝ)+1) := by
  have hs := (energy_summable r U hU hr).comp_injective
    (i := fun n : ℕ => n + K) (fun _ _ h => Nat.add_right_cancel h)
  have hw := paretoWeight_hasSum.summable.comp_injective
    (i := fun n : ℕ => n + K) (fun _ _ h => Nat.add_right_cancel h)
  have hm : (∑' n, paretoWeight (n + K)) = 1 / ((K : ℝ)+1) := by
    have he := paretoWeight_hasSum.summable.sum_add_tsum_nat_add K
    rw [paretoWeight_tsum, paretoWeight_partial_sum] at he
    linarith
  calc
    tail r K ≤ ∑' n, paretoWeight (n + K) * U ^ 2 := by
      apply Summable.tsum_le_tsum _ hs (hw.mul_right _)
      intro n
      exact mul_le_mul_of_nonneg_left
        (by simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hU).mpr (hr (n + K)))
        (paretoWeight_pos _).le
    _ = U ^ 2 / ((K : ℝ)+1) := by rw [tsum_mul_right, hm]; ring

theorem certificate_gap_exact (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) (K : ℕ) :
    certificate r U K - energy r = U ^ 2 / ((K : ℝ)+1) - tail r K := by
  have he := head_add_tail_exact r U hU hr K
  unfold certificate
  linarith

theorem certificate_bounds (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) (K : ℕ) :
    energy r ≤ certificate r U K ∧
      certificate r U K ≤ energy r + U ^ 2 / ((K : ℝ)+1) := by
  have he := certificate_gap_exact r U hU hr K
  have hn := tail_nonneg r K
  have hb := tail_le r U hU hr K
  constructor <;> linarith

theorem certificate_step_exact (r : ℕ → ℝ) (U : ℝ) (K : ℕ) :
    certificate r U (K + 1) - certificate r U K =
      paretoWeight K * ((r (K + 1))^2 - U ^ 2) := by
  simp only [certificate, head, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  rw [paretoWeight_eq_inv_sub]
  ring

theorem certificate_antitone (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) : Antitone (certificate r U) := by
  apply antitone_nat_of_succ_le
  intro K
  have hs : (r (K + 1))^2 ≤ U ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr (hr K)
  have he := certificate_step_exact r U K
  have hn := mul_nonpos_of_nonneg_of_nonpos (paretoWeight_pos K).le (sub_nonpos.mpr hs)
  linarith

theorem certificate_tendsto (r : ℕ → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) :
    Tendsto (certificate r U) atTop (𝓝 (energy r)) := by
  have hh : Tendsto (head r) atTop (𝓝 (energy r)) :=
    (energy_summable r U hU hr).hasSum.tendsto_sum_nat
  have ht := tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hi : Tendsto (fun K : ℕ => ((K : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      ht.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun K => head r K + U ^ 2 / ((K : ℝ) + 1)) atTop (𝓝 (energy r))
  simpa only [div_eq_mul_inv, mul_zero, add_zero] using
    hh.add (hi.const_mul (U ^ 2))

/-- An explicit numerical cutoff certifies any requested positive accuracy. -/
theorem certificate_gap_le (r : ℕ → ℝ) (U ε : ℝ) (hU : 0 ≤ U)
    (hr : ∀ n, |r (n + 1)| ≤ U) (K : ℕ)
    (hcut : U ^ 2 ≤ ε * ((K : ℝ) + 1)) :
    0 ≤ certificate r U K - energy r ∧ certificate r U K - energy r ≤ ε := by
  have hb := certificate_bounds r U hU hr K
  have hrem : U ^ 2 / ((K : ℝ) + 1) ≤ ε :=
    (div_le_iff₀ (by positivity)).mpr hcut
  constructor <;> linarith

def unitCertificate (r : ℕ → ℝ) (U : ℕ) : ℝ :=
  max 1 (certificate r (U : ℝ) (U ^ 2))

theorem unitCertificate_bounds (r : ℕ → ℝ) (U : ℕ)
    (hr : ∀ n, |r (n + 1)| ≤ (U : ℝ)) :
    max 1 (energy r) ≤ unitCertificate r U ∧
      unitCertificate r U ≤ 2 * max 1 (energy r) := by
  have hb := certificate_bounds r U (Nat.cast_nonneg _) hr (U ^ 2)
  have hrem : (U : ℝ)^2 / (((U ^ 2 : ℕ) : ℝ)+1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    linarith
  have hm1 : 1 ≤ max 1 (energy r) := le_max_left _ _
  have hmE : energy r ≤ max 1 (energy r) := le_max_right _ _
  unfold unitCertificate
  constructor
  · exact max_le_max_left 1 hb.1
  · apply max_le
    · linarith
    · linarith [hb.2]

theorem unitCertificate_reciprocal_bounds (r : ℕ → ℝ) (U : ℕ)
    (hr : ∀ n, |r (n + 1)| ≤ (U : ℝ)) :
    (2 * max 1 (energy r))⁻¹ ≤ (unitCertificate r U)⁻¹ ∧
      (unitCertificate r U)⁻¹ ≤ (max 1 (energy r))⁻¹ := by
  have hb := unitCertificate_bounds r U hr
  have hm : 0 < max 1 (energy r) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < unitCertificate r U := hm.trans_le hb.1
  exact ⟨(inv_le_inv₀ (mul_pos (by norm_num) hm) hc).mpr hb.2,
    (inv_le_inv₀ hc hm).mpr hb.1⟩

theorem reciprocal_summable_iff (r : ℕ → ℕ → ℝ) (U : ℕ → ℕ)
    (hr : ∀ j n, |r j (n + 1)| ≤ (U j : ℝ)) :
    Summable (fun j => (unitCertificate (r j) (U j))⁻¹) ↔
      Summable (fun j => (max 1 (energy (r j)))⁻¹) := by
  have hm (j : ℕ) : 0 < max 1 (energy (r j)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc (j : ℕ) : 0 < unitCertificate (r j) (U j) :=
    (hm j).trans_le (unitCertificate_bounds (r j) (U j) (hr j)).1
  constructor
  · intro hs
    apply Summable.of_nonneg_of_le (fun j => (inv_pos.mpr (hm j)).le)
      (fun j => ?_) (hs.mul_left 2)
    have h := (unitCertificate_reciprocal_bounds (r j) (U j) (hr j)).1
    rw [mul_inv_rev] at h
    norm_num at h
    linarith
  · intro hs
    exact Summable.of_nonneg_of_le (fun j => (inv_pos.mpr (hc j)).le)
      (fun j => (unitCertificate_reciprocal_bounds (r j) (U j) (hr j)).2) hs

end RiemannResearch.RH.Pareto.AmplitudeCertificates

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PeriodicWeightedMean
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Inverse-square Abel tails with the signed mean retained

Independently developed in the user-authorized continuation of the squarefree
power-cost program, 18 October 2026. Uses the existing finite Abel identity in
PeriodicWeightedMean. This module makes no RH or arithmetic source assumption.

The exact centered series identity precedes the estimate. A uniform bound B on
centered partial sums yields error at most B/(K + 1)^2 about the signed mean times
the complete inverse-square mass. Finite signed assembly retains the signed
combined mean; all components and their entire infinite tails are included.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.InverseSquareAbelTail
open PeriodicWeightedMean

def weight (K k : ℕ) : ℝ := 1 / ((k + K + 1 : ℕ) : ℝ) ^ 2

theorem weight_nonneg (K k : ℕ) : 0 ≤ weight K k := by
  unfold weight
  positivity

theorem weight_antitone (K : ℕ) : Antitone (weight K) := by
  intro i j hij
  unfold weight
  apply one_div_le_one_div_of_le (by positivity)
  have hcast : ((i + K + 1 : ℕ) : ℝ) ≤ ((j + K + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : i + K + 1 ≤ j + K + 1)
  have hp : (0 : ℝ) ≤ ((i + K + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem weight_summable (K : ℕ) : Summable (weight K) := by
  unfold weight
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (K + 1)).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

theorem bounded_summable (a : ℕ → ℝ) (K : ℕ) (C : ℝ)
    (ha : ∀ k, |a k| ≤ C) :
    Summable (fun k => a k * weight K k) := by
  apply ((weight_summable K).mul_left C).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg K k)]
  exact mul_le_mul_of_nonneg_right (ha k) (weight_nonneg K k)

theorem centered_identity (a : ℕ → ℝ) (K : ℕ) (μ : ℝ)
    (hs : Summable (fun k => a k * weight K k)) :
    (∑' k, a k * weight K k) =
      μ * (∑' k, weight K k) +
        ∑' k, (a k - μ) * weight K k := by
  have hw := weight_summable K
  simp_rw [sub_mul]
  rw [hs.tsum_sub (hw.mul_left μ), tsum_mul_left]
  ring

theorem centered_error_bound (a : ℕ → ℝ) (K : ℕ) (μ B : ℝ)
    (hs : Summable (fun k => a k * weight K k))
    (hb : ∀ n, |partialSum (fun k => a k - μ) n| ≤ B) :
    |(∑' k, a k * weight K k) - μ * (∑' k, weight K k)| ≤
      B / ((K + 1 : ℕ) : ℝ) ^ 2 := by
  have hw := weight_summable K
  have hc : Summable (fun k => (a k - μ) * weight K k) := by
    simpa only [sub_mul] using hs.sub (hw.mul_left μ)
  have hfin (n : ℕ) :
      |∑ k ∈ Finset.range n, (a k - μ) * weight K k| ≤
        B * weight K 0 := by
    exact abel_bound _ _ n B (fun k _ => hb k)
      (weight_nonneg K n) (fun i _ => weight_antitone K (Nat.le_succ i))
  have hlim := le_of_tendsto' hc.tendsto_sum_tsum_nat.abs hfin
  have he : (∑' k, (a k - μ) * weight K k) =
      (∑' k, a k * weight K k) - μ * (∑' k, weight K k) := by
    simp_rw [sub_mul]
    rw [hs.tsum_sub (hw.mul_left μ), tsum_mul_left]
  rw [he] at hlim
  simpa only [weight, Nat.zero_add, mul_one_div] using hlim

theorem periodic_centered_error_bound (a : ℕ → ℝ) (K p : ℕ) (μ B C : ℝ)
    (hp : 0 < p) (hper : ∀ k, a (k + p) = a k)
    (hmean : partialSum (fun k => a k - μ) p = 0)
    (hshort : ∀ n < p, |partialSum (fun k => a k - μ) n| ≤ B)
    (ha : ∀ k, |a k| ≤ C) :
    |(∑' k, a k * weight K k) - μ * (∑' k, weight K k)| ≤
      B / ((K + 1 : ℕ) : ℝ) ^ 2 := by
  apply centered_error_bound a K μ B (bounded_summable a K C ha)
  exact periodic_prefix_bound _ p B hp (fun k => by rw [hper k]) hmean hshort


theorem weight_mass_lower (K : ℕ) :
    1 / ((K + 1 : ℕ) : ℝ) ≤ ∑' k, weight K k := by
  let u : ℕ → ℝ := fun n => 1 / ((n + K + 1 : ℕ) : ℝ)
  have hstep (n : ℕ) : u n - u (n + 1) ≤ weight K n := by
    dsimp [u, weight]
    have hx : (0 : ℝ) < ((n + K + 1 : ℕ) : ℝ) := by positivity
    have he : ((n + 1 + K + 1 : ℕ) : ℝ) =
        ((n + K + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [he]
    field_simp
    nlinarith
  have hsum (n : ℕ) :
      u 0 - u n ≤ ∑' k, weight K k := by
    calc
      _ = ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
        (telescoping_weights u n).symm
      _ ≤ ∑ k ∈ Finset.range n, weight K k :=
        Finset.sum_le_sum (fun k _ => hstep k)
      _ ≤ _ := (weight_summable K).sum_le_tsum _ (fun k _ => weight_nonneg K k)
  have huinf : Filter.Tendsto
      (fun n : ℕ => ((n + K + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    exact_mod_cast (by omega : n ≤ n + K + 1)
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := huinf.const_div_atTop 1
  have h := le_of_tendsto' (hu.const_sub (u 0)) hsum
  simpa only [sub_zero, u, Nat.zero_add] using h

theorem weighted_sum_neg (a : ℕ → ℝ) (K : ℕ) (μ B C : ℝ)
    (ha : ∀ k, |a k| ≤ C)
    (hb : ∀ n, |partialSum (fun k => a k - μ) n| ≤ B)
    (hμ : μ < 0) (hgap : B < -μ * ((K + 1 : ℕ) : ℝ)) :
    (∑' k, a k * weight K k) < 0 := by
  have he := centered_error_bound a K μ B (bounded_summable a K C ha) hb
  have hu := (abs_le.mp he).2
  have hm := mul_le_mul_of_nonpos_left (weight_mass_lower K) hμ.le
  have hx : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hn : μ / ((K + 1 : ℕ) : ℝ) +
      B / ((K + 1 : ℕ) : ℝ)^2 < 0 := by
    have heq : μ / ((K + 1 : ℕ) : ℝ) +
        B / ((K + 1 : ℕ) : ℝ)^2 =
        (μ * ((K + 1 : ℕ) : ℝ) + B) / ((K + 1 : ℕ) : ℝ)^2 := by
      field_simp
    rw [heq]
    exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hx)
  have hn' : μ * (1 / ((K + 1 : ℕ) : ℝ)) +
      B / ((K + 1 : ℕ) : ℝ)^2 < 0 := by
    convert hn using 1 <;> ring
  linarith


theorem weight_mass_upper (K : ℕ) (hK : 0 < K) :
    (∑' k, weight K k) ≤ 1 / (K : ℝ) := by
  let u : ℕ → ℝ := fun n => 1 / ((n + K : ℕ) : ℝ)
  have hstep (n : ℕ) : weight K n ≤ u n - u (n + 1) := by
    dsimp [u, weight]
    have hx : (0 : ℝ) < ((n + K : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + K)
    have he : ((n + 1 + K : ℕ) : ℝ) = ((n + K : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    have he' : ((n + K + 1 : ℕ) : ℝ) = ((n + K : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [he, he']
    field_simp
    nlinarith
  apply (weight_summable K).tsum_le_of_sum_range_le
  intro n
  calc
    _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
      Finset.sum_le_sum (fun k _ => hstep k)
    _ = u 0 - u n := telescoping_weights u n
    _ ≤ _ := by
      dsimp [u]
      simp only [Nat.zero_add]
      have hu : (0 : ℝ) ≤ 1 / ((n + K : ℕ) : ℝ) := by positivity
      linarith

theorem finite_signed_error_bound {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a : ι → ℕ → ℝ) (K : ℕ) (μ B C : ι → ℝ)
    (ha : ∀ i ∈ s, ∀ k, |a i k| ≤ C i)
    (hb : ∀ i ∈ s, ∀ n, |partialSum (fun k => a i k - μ i) n| ≤ B i) :
    |(∑' k, (∑ i ∈ s, c i * a i k) * weight K k) -
        (∑ i ∈ s, c i * μ i) * (∑' k, weight K k)| ≤
      (∑ i ∈ s, |c i| * B i) / ((K + 1 : ℕ) : ℝ)^2 := by
  apply centered_error_bound _ K _ _
  · apply bounded_summable _ K (∑ i ∈ s, |c i| * C i)
    intro k
    calc
      _ ≤ ∑ i ∈ s, |c i * a i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ha i hi k) (abs_nonneg _)
  · intro n
    have he : partialSum
        (fun k => (∑ i ∈ s, c i * a i k) - ∑ i ∈ s, c i * μ i) n =
        ∑ i ∈ s, c i * partialSum (fun k => a i k - μ i) n := by
      unfold partialSum
      calc
        _ = ∑ k ∈ Finset.range n, ∑ i ∈ s, c i * (a i k - μ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
        _ = _ := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]
    rw [he]
    calc
      _ ≤ ∑ i ∈ s, |c i * partialSum (fun k => a i k - μ i) n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb i hi n) (abs_nonneg _)

end RiemannResearch.Analysis.InverseSquareAbelTail

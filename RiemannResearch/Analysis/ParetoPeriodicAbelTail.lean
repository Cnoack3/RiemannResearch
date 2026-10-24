/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InverseSquareAbelTail

/-!
# Complete Pareto tails of periodic sequences

Source: constructive-approximants certificate continuation, 24 October 2026.
For a physical tail beyond N, supply a k = f (N + 1 + k). The first weight
is 1/((N+1)(N+2)) and the complete tail mass is exactly 1/(N+1).
The signed mean and centered series are retained before any absolute bounds.
Finite signed assembly therefore retains every signed mixed mean term.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ParetoPeriodicAbelTail
open PeriodicWeightedMean

def weight (N k : ℕ) : ℝ :=
  1 / (((k + N + 1 : ℕ) : ℝ) * ((k + N + 2 : ℕ) : ℝ))

theorem weight_nonneg (N k : ℕ) : 0 ≤ weight N k := by
  unfold weight
  positivity

theorem weight_antitone (N : ℕ) : Antitone (weight N) := by
  intro i j hij
  unfold weight
  apply one_div_le_one_div_of_le (by positivity)
  have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  nlinarith

theorem weight_summable (N : ℕ) : Summable (weight N) := by
  apply (InverseSquareAbelTail.weight_summable N).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg N k)]
  unfold weight InverseSquareAbelTail.weight
  apply one_div_le_one_div_of_le (by positivity)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  nlinarith

theorem weight_eq_sub (N k : ℕ) :
    weight N k = 1 / ((k + N + 1 : ℕ) : ℝ) -
      1 / ((k + 1 + N + 1 : ℕ) : ℝ) := by
  unfold weight
  have h1 : (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ) := by positivity
  have h2 : ((k + 1 + N + 1 : ℕ) : ℝ) =
      ((k + N + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  have h3 : ((k + N + 2 : ℕ) : ℝ) =
      ((k + N + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [h2, h3]
  field_simp
  ring

theorem weight_mass (N : ℕ) :
    (∑' k, weight N k) = 1 / ((N + 1 : ℕ) : ℝ) := by
  let u : ℕ → ℝ := fun k => 1 / ((k + N + 1 : ℕ) : ℝ)
  have hfin (n : ℕ) : (∑ k ∈ Finset.range n, weight N k) = u 0 - u n := by
    simp_rw [weight_eq_sub]
    exact telescoping_weights u n
  have huinf : Filter.Tendsto
      (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro n
    exact_mod_cast (by omega : n ≤ n + N + 1)
  have hu : Filter.Tendsto u Filter.atTop (nhds 0) := huinf.const_div_atTop 1
  have hlim : Filter.Tendsto (fun n => ∑ k ∈ Finset.range n, weight N k)
      Filter.atTop (nhds (1 / ((N + 1 : ℕ) : ℝ))) := by
    simp_rw [hfin]
    simpa only [sub_zero, u, Nat.zero_add] using hu.const_sub (u 0)
  exact tendsto_nhds_unique (weight_summable N).tendsto_sum_tsum_nat hlim

theorem bounded_summable (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (ha : ∀ k, |a k| ≤ C) :
    Summable (fun k => a k * weight N k) := by
  apply ((weight_summable N).mul_left C).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg N k)]
  exact mul_le_mul_of_nonneg_right (ha k) (weight_nonneg N k)

/-- Exact signed identity, before taking any norm or componentwise bound. -/
theorem centered_identity (a : ℕ → ℝ) (N : ℕ) (μ : ℝ)
    (hs : Summable (fun k => a k * weight N k)) :
    (∑' k, a k * weight N k) = μ / ((N + 1 : ℕ) : ℝ) +
      ∑' k, (a k - μ) * weight N k := by
  have hw := weight_summable N
  simp_rw [sub_mul]
  rw [hs.tsum_sub (hw.mul_left μ), tsum_mul_left, weight_mass]
  ring

theorem centered_error_bound (a : ℕ → ℝ) (N : ℕ) (μ B : ℝ)
    (hs : Summable (fun k => a k * weight N k))
    (hb : ∀ n, |partialSum (fun k => a k - μ) n| ≤ B) :
    |(∑' k, a k * weight N k) - μ / ((N + 1 : ℕ) : ℝ)| ≤
      B / (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) := by
  have hw := weight_summable N
  have hc : Summable (fun k => (a k - μ) * weight N k) := by
    simpa only [sub_mul] using hs.sub (hw.mul_left μ)
  have hfin (n : ℕ) :
      |∑ k ∈ Finset.range n, (a k - μ) * weight N k| ≤ B * weight N 0 := by
    exact abel_bound _ _ n B (fun k _ => hb k)
      (weight_nonneg N n) (fun i _ => weight_antitone N (Nat.le_succ i))
  have hlim := le_of_tendsto' hc.tendsto_sum_tsum_nat.abs hfin
  have he : (∑' k, (a k - μ) * weight N k) =
      (∑' k, a k * weight N k) - μ / ((N + 1 : ℕ) : ℝ) := by
    have hid := centered_identity a N μ hs
    linarith only [hid]
  rw [he] at hlim
  simpa only [weight, Nat.zero_add, mul_one_div] using hlim

/-- A period-L nonnegative sequence bounded by b gives the complete tail
interval centered at its exact mean, with radius L*b/((N+1)(N+2)). -/
theorem nonnegative_periodic_error_bound
    (a : ℕ → ℝ) (N L : ℕ) (μ b : ℝ) (hL : 0 < L)
    (hpos : ∀ k, 0 ≤ a k) (hbound : ∀ k, a k ≤ b)
    (hper : ∀ k, a (k + L) = a k)
    (hmean : partialSum a L = (L : ℝ) * μ) :
    |(∑' k, a k * weight N k) - μ / ((N + 1 : ℕ) : ℝ)| ≤
      ((L : ℝ) * b) / (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hμ : 0 ≤ μ := by
    have hsum : 0 ≤ partialSum a L :=
      Finset.sum_nonneg (fun k _ => hpos k)
    rw [hmean] at hsum
    nlinarith only [hsum, hLp]
  have hmass : (L : ℝ) * μ ≤ (L : ℝ) * b := by
    rw [← hmean]
    calc
      partialSum a L ≤ ∑ k ∈ Finset.range L, b :=
        Finset.sum_le_sum (fun k _ => hbound k)
      _ = (L : ℝ) * b := by simp
  have hs := bounded_summable a N b (fun k => by
    simpa only [abs_of_nonneg (hpos k)] using hbound k)
  have hb := nonnegative_periodic_discrepancy a L μ hL hμ hpos hper hmean
  exact (centered_error_bound a N μ ((L : ℝ) * μ) hs hb).trans
    (div_le_div_of_nonneg_right hmass (by positivity))

/-- Signed assembly keeps the complete combined mean before estimating the
centered discrepancy; negative mixed coefficients are not discarded. -/
theorem finite_signed_error_bound {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (a : ι → ℕ → ℝ) (N : ℕ) (μ B C : ι → ℝ)
    (ha : ∀ i ∈ s, ∀ k, |a i k| ≤ C i)
    (hb : ∀ i ∈ s, ∀ n, |partialSum (fun k => a i k - μ i) n| ≤ B i) :
    |(∑' k, (∑ i ∈ s, c i * a i k) * weight N k) -
        (∑ i ∈ s, c i * μ i) / ((N + 1 : ℕ) : ℝ)| ≤
      (∑ i ∈ s, |c i| * B i) /
        (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) := by
  apply centered_error_bound _ N _ _
  · apply bounded_summable _ N (∑ i ∈ s, |c i| * C i)
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

/-- The complete period mean is unchanged at every physical tail origin. -/
theorem period_sum_shift (f : ℕ → ℝ) (L t : ℕ)
    (hper : ∀ k, f (k + L) = f k) :
    partialSum (fun k => f (k + t)) L = partialSum f L := by
  have hfirst : partialSum f (L + t) = partialSum f L + partialSum f t := by
    unfold partialSum
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simpa only [Nat.add_comm] using hper k
  have hsecond : partialSum f (t + L) =
      partialSum f t + partialSum (fun k => f (k + t)) L := by
    unfold partialSum
    rw [Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_comm t k]
  have he : partialSum f (L + t) = partialSum f (t + L) := by
    rw [Nat.add_comm L t]
  rw [hfirst, hsecond] at he
  linarith only [he]

/-- The usable physical-tail version requires only the unshifted period mean. -/
theorem physical_periodic_error_bound
    (f : ℕ → ℝ) (N L : ℕ) (μ b : ℝ) (hL : 0 < L)
    (hpos : ∀ k, 0 ≤ f k) (hbound : ∀ k, f k ≤ b)
    (hper : ∀ k, f (k + L) = f k)
    (hmean : partialSum f L = (L : ℝ) * μ) :
    |(∑' k, f (k + (N + 1)) * weight N k) - μ / ((N + 1 : ℕ) : ℝ)| ≤
      ((L : ℝ) * b) / (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) := by
  apply nonnegative_periodic_error_bound (fun k => f (k + (N + 1))) N L μ b hL
    (fun k => hpos _) (fun k => hbound _)
  · intro k
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hper (k + (N + 1))
  · rw [period_sum_shift f L (N + 1) hper, hmean]


end RiemannResearch.Analysis.ParetoPeriodicAbelTail

import RiemannResearch.RH.ParetoCovariance
import RiemannResearch.RH.DigammaQuarter
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Series
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Pareto residue moments

Source: `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §4.
The infinite sum is evaluated using the proved digamma partial-fraction
series and exact values at one quarter, one half, and three quarters.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem neg_unit_interval_mem_integerComplement {a : ℝ}
    (ha : -1 < a) (ha0 : a < 0) : (a : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hn' : (n : ℝ) = a := by
    simpa only [Complex.intCast_re, Complex.ofReal_re] using congrArg Complex.re hn
  have hlow : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
  have hhigh : n < (0 : ℤ) := by exact_mod_cast (show (n : ℝ) < 0 by linarith)
  omega

/-- Standard real reciprocal-difference series throughout the unit interval. -/
theorem hasSum_reciprocal_difference {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1))
      (-(Complex.digamma (a : ℂ)).re - Real.eulerMascheroniConstant) := by
  have hz : ((a - 1 : ℝ) : ℂ) ∈ Complex.integerComplement :=
    neg_unit_interval_mem_integerComplement (by linarith) (by linarith)
  have hneg : ∀ m : ℕ, ((a - 1 : ℝ) : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    exact hz ⟨-(m : ℤ), by
      push_cast
      simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hm.symm⟩
  have hd := Complex.digamma_apply_add_one ((a - 1 : ℝ) : ℂ) hneg
  have hsum := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have he : ((a - 1 : ℝ) : ℂ) + 1 = (a : ℂ) := by push_cast; ring
  rw [he] at hd
  have hrhs : Complex.digamma ((a - 1 : ℝ) : ℂ) +
      (Real.eulerMascheroniConstant : ℂ) + 1 / ((a - 1 : ℝ) : ℂ) =
        Complex.digamma (a : ℂ) + (Real.eulerMascheroniConstant : ℂ) := by
    rw [hd]
    ring
  rw [hrhs] at hsum
  have hc : HasSum (fun n : ℕ =>
      (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + a) : ℝ))
      ((Complex.digamma (a : ℂ)).re + Real.eulerMascheroniConstant) := by
    have h := Complex.hasSum_re hsum
    convert h using 1 <;> try rfl
    · ext n
      have he' : ((a - 1 : ℝ) : ℂ) + (n : ℂ) + 1 =
          (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
      rw [he']
      have he'' : ((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + a) : ℝ) : ℂ) =
          1 / ((n : ℂ) + 1) - 1 / (((n : ℝ) + a : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [← he'', Complex.ofReal_re]
  have h := hc.neg
  convert h using 1 <;> try rfl
  · ext n; ring
  · ring

private theorem hasSum_quarter_difference :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1/4) - 1 / ((n : ℝ) + 1))
      (3 * Real.log 2 + Real.pi / 2) := by
  have h := hasSum_reciprocal_difference (a := 1/4) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [RiemannResearch.RH.re_digamma_one_quarter] at h
  convert h using 1 <;> first | rfl | ring

private theorem hasSum_half_difference :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1/2) - 1 / ((n : ℝ) + 1))
      (2 * Real.log 2) := by
  have h := hasSum_reciprocal_difference (a := 1/2) (by norm_num) (by norm_num)
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ 2 by norm_num)).symm
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  have he : (Complex.digamma (1/2)).re = -2 * Real.log 2 -
      Real.eulerMascheroniConstant := by
    have hc : Complex.digamma (1/2) =
        ((-2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
      rw [Complex.digamma_one_half, hlog]
      push_cast
      ring
    simpa only [Complex.ofReal_re] using congrArg Complex.re hc
  rw [he] at h
  convert h using 1 <;> first | rfl | ring

private theorem hasSum_three_quarters_difference :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 3/4) - 1 / ((n : ℝ) + 1))
      (3 * Real.log 2 - Real.pi / 2) := by
  have h := hasSum_reciprocal_difference (a := 3/4) (by norm_num) (by norm_num)
  have he : (Complex.digamma (3/4)).re = -Real.eulerMascheroniConstant -
      3 * Real.log 2 + Real.pi / 2 := by
    have hc : Complex.digamma (3 / 4) =
        ((-Real.eulerMascheroniConstant - 3 * Real.log 2 + Real.pi / 2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat] using
          RiemannResearch.RH.digamma_three_quarters
    simpa only [Complex.ofReal_re] using congrArg Complex.re hc
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rw [he] at h
  convert h using 1 <;> first | rfl | ring

/-- Group an absolutely convergent series into four-term blocks. -/
theorem tsum_eq_of_four_blocks {f : ℕ → ℝ} {s : ℝ} (hf : Summable f)
    (hs : HasSum (fun n => f (4*n) + f (4*n+1) + f (4*n+2) + f (4*n+3)) s) :
    (∑' k, f k) = s := by
  have hpartial (N : ℕ) : (∑ k ∈ Finset.range (4*N), f k) =
      ∑ n ∈ Finset.range N, (f (4*n) + f (4*n+1) + f (4*n+2) + f (4*n+3)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      norm_num [Finset.sum_range_succ]
  have h4 : Tendsto (fun N : ℕ => 4*N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N (by norm_num)) tendsto_id
  have hlim := hf.hasSum.tendsto_sum_nat.comp h4
  simp only [Function.comp_def, hpartial] at hlim
  exact tendsto_nhds_unique hlim hs.tendsto_sum_nat

private theorem residue_four_block (n : ℕ) :
    positiveWeight (4*n) * (residue 4 (4*n) * residue 4 (4*n)) +
      positiveWeight (4*n+1) * (residue 4 (4*n+1) * residue 4 (4*n+1)) +
      positiveWeight (4*n+2) * (residue 4 (4*n+2) * residue 4 (4*n+2)) +
      positiveWeight (4*n+3) * (residue 4 (4*n+3) * residue 4 (4*n+3)) =
      (1 / ((n : ℝ)+1/4) - 1 / ((n : ℝ)+1) +
        3 * (1 / ((n : ℝ)+1/2) - 1 / ((n : ℝ)+1)) +
        5 * (1 / ((n : ℝ)+3/4) - 1 / ((n : ℝ)+1))) / 4 := by
  norm_num [residue, Nat.add_mod, Nat.mul_mod, positiveWeight]
  have h1 : (n : ℝ) + 1/4 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1/2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3/4 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h5 : 4*(n : ℝ)+1 ≠ 0 := by positivity
  have h6 : 4*(n : ℝ)+2 ≠ 0 := by positivity
  have h7 : 4*(n : ℝ)+3 ≠ 0 := by positivity
  have h8 : 4*(n : ℝ)+4 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Exact complete Pareto second moment, with the analytic series proved. -/
theorem paretoInner_residue_four :
    paretoInner (residue 4) (residue 4) = 6 * Real.log 2 - Real.pi / 2 := by
  have hr : ∀ k, |residue 4 k| ≤ (4 : ℝ) := fun k => residue_abs_le 4 k (by norm_num)
  have hf := weighted_summable_of_bounded (bounded_product hr hr)
  have hs := (hasSum_quarter_difference.add
    (hasSum_half_difference.mul_left 3)).add
      (hasSum_three_quarters_difference.mul_left 5)
  have hdiv := hs.mul_left (1/4)
  apply tsum_eq_of_four_blocks hf
  convert hdiv using 1 <;> try rfl
  · ext n
    rw [residue_four_block]
    ring
  · ring

private theorem residue_two_block (n : ℕ) :
    positiveWeight (4*n) * (residue 2 (4*n) * residue 2 (4*n)) +
      positiveWeight (4*n+1) * (residue 2 (4*n+1) * residue 2 (4*n+1)) +
      positiveWeight (4*n+2) * (residue 2 (4*n+2) * residue 2 (4*n+2)) +
      positiveWeight (4*n+3) * (residue 2 (4*n+3) * residue 2 (4*n+3)) =
      (1 / ((n : ℝ)+1/4) - 1 / ((n : ℝ)+1) -
        (1 / ((n : ℝ)+1/2) - 1 / ((n : ℝ)+1)) +
        (1 / ((n : ℝ)+3/4) - 1 / ((n : ℝ)+1))) / 4 := by
  norm_num [residue, Nat.add_mod, Nat.mul_mod, positiveWeight]
  have h1 : (n : ℝ) + 1/4 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1/2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 3/4 ≠ 0 := by positivity
  have h4 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h5 : 4*(n : ℝ)+1 ≠ 0 := by positivity
  have h6 : 4*(n : ℝ)+2 ≠ 0 := by positivity
  have h7 : 4*(n : ℝ)+3 ≠ 0 := by positivity
  have h8 : 4*(n : ℝ)+4 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Exact second moment of the binary residue. -/
theorem paretoInner_residue_two :
    paretoInner (residue 2) (residue 2) = Real.log 2 := by
  have hr : ∀ k, |residue 2 k| ≤ (2 : ℝ) := fun k => residue_abs_le 2 k (by norm_num)
  have hf := weighted_summable_of_bounded (bounded_product hr hr)
  have hs := (hasSum_quarter_difference.sub hasSum_half_difference).add
    hasSum_three_quarters_difference
  have hdiv := hs.mul_left (1/4)
  apply tsum_eq_of_four_blocks hf
  convert hdiv using 1 <;> try rfl
  · ext n
    rw [residue_two_block]
    ring
  · ring

/-- Exact first moment of the binary residue. -/
theorem paretoMean_residue_two : paretoMean (residue 2) = Real.log 2 := by
  rw [← paretoInner_residue_two]
  unfold paretoMean paretoInner
  apply tsum_congr
  intro k
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with hk | hk <;> simp [residue, hk]

end
end RiemannResearch.RH.Pareto

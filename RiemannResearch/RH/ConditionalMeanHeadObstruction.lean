/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroDualTail
import RiemannResearch.RH.ConditionalMeanRHBridge

/-!
# Exact-head obstruction in conditional-mean energy

The signed Mellin annihilation is kept intact. Cauchy--Schwarz is applied only
after isolating its exact tail. No existence of legal interpolants with the
required energy bound is asserted.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- The full conditional-mean squared norm, rather than the approximation error. -/
def conditionalMeanSquare (g : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, conditionalWeight k * (cesaro g (k + 1)) ^ 2

theorem conditionalMeanSquare_nonneg (g : ℕ → ℝ) : 0 ≤ conditionalMeanSquare g :=
  tsum_nonneg (fun k => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))

/-- Averaging preserves a constant exact positive head. -/
theorem mean_eq_one_of_head (F : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hhead : ∀ n, 0 < n → n ≤ N → F n = 1) : mean F N = 1 := by
  have hp : partialSum F N = (N : ℂ) := by
    unfold partialSum
    calc
      _ = ∑ k ∈ Finset.range N, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hhead (k + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      _ = _ := by simp
  rw [mean, hp, div_self (by exact_mod_cast ne_of_gt hN)]

theorem legal_conditionalMeanSquare_summable (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    Summable (fun k : ℕ => conditionalWeight k * (cesaro g (k + 1)) ^ 2) := by
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  have h := bounded_mean_energy_summable (fun n => (g n : ℂ)) B
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hB n)
  simpa only [mean_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- The transformed dual coefficients have actual total sum one. -/
theorem mellinSecond_hasSum_one (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    HasSum (fun k : ℕ => mellinSecond s (k + 1)) 1 := by
  have hseq (n : ℕ) (hn : 0 < n) : (hilbertSequence hilbertOne n : ℂ) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor, ne_of_gt hn]
  have hmean (k : ℕ) : mean (fun n => (hilbertSequence hilbertOne n : ℂ)) (k + 1) = 1 :=
    mean_eq_one_of_head _ _ (Nat.succ_pos _) (fun n hn _ => hseq n hn)
  have hp := cesaro_mellin_pairing hilbertOne s hs 1
    (fun n hn => by rw [hseq n hn]; simp)
  simp_rw [hmean, mul_one] at hp
  rw [paretoMellin_one s hs] at hp
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hone : (∑' k : ℕ, mellinSecond s (k + 1)) = 1 := by
    rw [hp]
    field_simp
  have hsum := (mellinSecond_norm_summable s (by linarith)).of_norm
  simpa only [hone] using hsum.hasSum

/-- Total coefficient mass one forces the actual dual-square constant to be at least one. -/
theorem one_le_conditionalMellinDualSquare (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    1 ≤ conditionalMellinDualSquare s := by
  have hone : Summable (fun k : ℕ => conditionalWeight k * ‖(1 : ℂ)‖ ^ 2) := by
    simpa only [norm_one, one_pow, mul_one, conditionalWeight] using
      hasSum_mixtureWeight.summable
  have hb := Analysis.WeightedPairing.pairing_norm_sq_le
    conditionalWeight conditionalWeight_pos
    (fun k => mellinSecond s (k + 1)) (fun _ => (1 : ℂ))
    (mellinSecond_dual_summable s hs) hone
  have hq : (∑' k : ℕ, conditionalWeight k) = 1 := hasSum_mixtureWeight.tsum_eq
  simpa only [mul_one, (mellinSecond_hasSum_one s hs).tsum_eq,
    norm_one, one_pow, hq, conditionalMellinDualSquare] using hb

/-- Prefix mass stays bounded away from zero for all sufficiently large heads. -/
theorem mellinSecond_prefix_eventually (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    ∀ᶠ N : ℕ in atTop, (1 / 4 : ℝ) ≤ ‖partialSum (mellinSecond s) N‖ ^ 2 := by
  have h := ((mellinSecond_hasSum_one s hs).tendsto_sum_nat.norm).eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < ‖(1 : ℂ)‖))
  filter_upwards [h] with N hN
  change (1 / 2 : ℝ) < ‖partialSum (mellinSecond s) N‖ at hN
  nlinarith

/-- The signed conditional-mean pairing vanishes for every genuine legal witness. -/
theorem legal_second_pairing_zero (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    (∑' k : ℕ, mellinSecond s (k + 1) * mean (fun n => (g n : ℂ)) (k + 1)) = 0 := by
  obtain ⟨f, hf, hfg⟩ := legalSeedSpan_exists_hilbert A hA hg
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  have hb (n : ℕ) (hn : 0 < n) : ‖(hilbertSequence f n : ℂ)‖ ≤ B := by
    rw [hfg]
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hB n
  have hp := cesaro_mellin_pairing f s hs B hb
  rw [hfg] at hp
  have hz' := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz
    ((hilbertLegalSubspace A).le_topologicalClosure hf)
  simpa only [hz', mul_zero] using hp

/-- Exact signed head/tail balance followed by a valid weighted tail estimate. -/
theorem exact_head_dual_obstruction (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A)
    (hhead : ∀ n, 0 < n → n ≤ N → g n = 1) :
    ‖partialSum (mellinSecond s) N‖ ^ 2 ≤ dualTail s N * conditionalMeanSquare g := by
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  let F : ℕ → ℂ := fun n => (g n : ℂ)
  have hb (n : ℕ) (hn : 0 < n) : ‖F n‖ ≤ B := by
    simpa only [F, Complex.norm_real, Real.norm_eq_abs] using hB n
  have hsum := bounded_second_pairing_summable s (by linarith) F B hb
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hpref : (∑ k ∈ Finset.range N, mellinSecond s (k + 1) * mean F (k + 1)) =
      partialSum (mellinSecond s) N := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := Finset.mem_range.mp hk
    rw [mean_eq_one_of_head F (k + 1) (Nat.succ_pos _) ?_, mul_one]
    intro n hn hnk
    simp only [F, hhead n hn (hnk.trans (by omega)), Complex.ofReal_one]
  rw [hpref, legal_second_pairing_zero A hA s hs hs1 hz hg] at hsplit
  have he : (∑' k : ℕ, mellinSecond s (k + N + 1) * mean F (k + N + 1)) =
      -partialSum (mellinSecond s) N := by linear_combination hsplit
  have henergy := bounded_mean_energy_summable F B hb
  have htail : Summable (fun k : ℕ => conditionalWeight (k + N) *
      ‖mean F (k + N + 1)‖ ^ 2) :=
    henergy.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbound := Analysis.WeightedPairing.pairing_norm_sq_le
    (fun k => conditionalWeight (k + N)) (fun k => conditionalWeight_pos _)
    (fun k => mellinSecond s (k + N + 1)) (fun k => mean F (k + N + 1))
    (dualTail_summable s hs N) htail
  rw [he, norm_neg] at hbound
  have hEsplit := henergy.sum_add_tsum_nat_add N
  have hEnonneg : 0 ≤ ∑ k ∈ Finset.range N, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))
  have ht : (∑' k : ℕ, conditionalWeight (k + N) * ‖mean F (k + N + 1)‖ ^ 2) ≤
      ∑' k : ℕ, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2 := by linarith
  have hall : (∑' k : ℕ, conditionalWeight k * ‖mean F (k + 1)‖ ^ 2) =
      conditionalMeanSquare g := by
    simp only [F, mean_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs, conditionalMeanSquare]
  rw [hall] at ht
  exact hbound.trans (mul_le_mul_of_nonneg_left ht (dualTail_nonneg s N))

/-- A zero gives a uniform quantitative obstruction for all sufficiently long exact heads. -/
theorem exact_head_scaled_obstruction_eventually (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ N : ℕ in atTop, ∀ g ∈ legalSeedSpan A,
      (∀ n, 0 < n → n ≤ N → g n = 1) →
      (1 / 4 : ℝ) ≤ (3 * ‖s * (s + 1)‖ ^ 2 / (2 * s.re - 1)) *
        (N : ℝ) ^ (1 - 2 * s.re) * conditionalMeanSquare g := by
  filter_upwards [mellinSecond_prefix_eventually s hs, eventually_ge_atTop 1] with N hp hN
  intro g hg hhead
  have h := hp.trans (exact_head_dual_obstruction A hA s hs hs1 hz N hg hhead)
  exact h.trans (mul_le_mul_of_nonneg_right (dualTail_le s hs N hN)
    (conditionalMeanSquare_nonneg g))

end RiemannResearch.RH.Pareto

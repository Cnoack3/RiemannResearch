/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinCesaroSummability

/-!
# The Cesaro--Mellin bridge on the whole weighted Hilbert space

Source: user-provided argument,
Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md, Section 5;
detailed proof recorded in AllHilbertMellinProof.md.

Finite weighted Cauchy--Schwarz gives an O(sqrt N) bound on the Cesaro
means of an arbitrary Hilbert vector. This supplies both absolute convergence
of the second-difference series and decay of the retained Abel boundary.
No boundedness premise on the physical sequence is used.

-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro
open RH.Pareto

/-- Finite weighted Cauchy--Schwarz, uniformly over every physical Hilbert vector. -/
theorem hilbert_prefix_norm_sq_le (f : ThresholdHilbert) (N : ℕ) :
    ‖partialSum (fun n => (hilbertSequence f n : ℂ)) N‖ ^ 2 ≤
      ‖f‖ ^ 2 * ((N : ℝ) + 1) ^ 2 * (N : ℝ) := by
  have hcs := WeightedPairing.finite_pairing_norm_sq_le paretoWeight paretoWeight_pos
    (fun _ => (1 : ℂ)) (fun k => (hilbertSequence f (k + 1) : ℂ)) (Finset.range N)
  have henergy :
      (∑ k ∈ Finset.range N,
        paretoWeight k * ‖(hilbertSequence f (k + 1) : ℂ)‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← positiveWeight_succ, hilbertSequence_weighted_square]
    rw [hilbert_norm_sq]
    exact sum_le_hasSum _ (fun k _ => sq_nonneg (f k))
      (hilbert_coordinate_square_summable f).hasSum
  have hweight :
      (∑ k ∈ Finset.range N, ‖(1 : ℂ)‖ ^ 2 / paretoWeight k) ≤
        (N : ℝ) * ((N : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, ((N : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k + 1 ≤ N := by have := Finset.mem_range.mp hk; omega
        have hkR : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hkN
        simp only [norm_one, one_pow, paretoWeight, one_div, inv_inv]
        have h1 : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by linarith
        have h2 : (k : ℝ) + 2 ≤ (N : ℝ) + 1 := by linarith
        simpa only [pow_two] using
          mul_le_mul h1 h2 (by positivity : 0 ≤ (k : ℝ) + 2)
            (by positivity : 0 ≤ (N : ℝ) + 1)
      _ = _ := by simp [mul_comm]
  have hweight0 :
      0 ≤ ∑ k ∈ Finset.range N, ‖(1 : ℂ)‖ ^ 2 / paretoWeight k :=
    Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (paretoWeight_pos k).le)
  have henergy0 :
      0 ≤ ∑ k ∈ Finset.range N,
        paretoWeight k * ‖(hilbertSequence f (k + 1) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ =>
      mul_nonneg (paretoWeight_pos k).le (sq_nonneg _))
  have hprod := mul_le_mul hweight henergy henergy0
    (by positivity : 0 ≤ (N : ℝ) * ((N : ℝ) + 1) ^ 2)
  have hs : ‖partialSum (fun n => (hilbertSequence f n : ℂ)) N‖ ^ 2 ≤
      ((N : ℝ) * ((N : ℝ) + 1) ^ 2) * ‖f‖ ^ 2 := by
    simpa only [one_mul, partialSum] using hcs.trans hprod
  nlinarith

/-- A deliberately simple O(N^(3/2)) prefix bound, valid also at N=0. -/
theorem hilbert_prefix_norm_le (f : ThresholdHilbert) (N : ℕ) :
    ‖partialSum (fun n => (hilbertSequence f n : ℂ)) N‖ ≤
      ‖f‖ * ((N : ℝ) + 1) * Real.sqrt (N : ℝ) := by
  have hs := hilbert_prefix_norm_sq_le f N
  have he : (‖f‖ * ((N : ℝ) + 1) * Real.sqrt (N : ℝ)) ^ 2 =
      ‖f‖ ^ 2 * ((N : ℝ) + 1) ^ 2 * (N : ℝ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hb : 0 ≤ ‖f‖ * ((N : ℝ) + 1) * Real.sqrt (N : ℝ) := by positivity
  nlinarith [norm_nonneg (partialSum (fun n => (hilbertSequence f n : ℂ)) N)]

/-- Every physical Hilbert vector has Cesaro means growing at most like sqrt(N). -/
theorem hilbert_mean_norm_le (f : ThresholdHilbert) (N : ℕ) (hN : 0 < N) :
    ‖mean (fun n => (hilbertSequence f n : ℂ)) N‖ ≤
      2 * ‖f‖ * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [mean, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hNR).2
  calc
    _ ≤ ‖f‖ * ((N : ℝ) + 1) * Real.sqrt (N : ℝ) := hilbert_prefix_norm_le f N
    _ ≤ 2 * ‖f‖ * Real.sqrt (N : ℝ) * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left
        (show (N : ℝ) + 1 ≤ 2 * (N : ℝ) by linarith)
        (mul_nonneg (norm_nonneg f) (Real.sqrt_nonneg (N : ℝ)))
      nlinarith
    _ = _ := by rw [Real.sqrt_eq_rpow]

/-- Quantitative boundary estimate for an arbitrary, possibly unbounded Hilbert vector. -/
theorem hilbert_terminal_pairing_norm_le (f : ThresholdHilbert) (s : ℂ)
    (hs : 0 < s.re) (N : ℕ) :
    ‖(N : ℂ) * mellinFirst s (N + 1) *
      mean (fun n => (hilbertSequence f n : ℂ)) N‖ ≤
      (‖s‖ * ‖f‖) * (((N + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - s.re)) := by
  let x : ℝ := ((N + 1 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hrewrite :
      (N : ℂ) * mellinFirst s (N + 1) *
        mean (fun n => (hilbertSequence f n : ℂ)) N =
      mellinFirst s (N + 1) *
        partialSum (fun n => (hilbertSequence f n : ℂ)) N := by
    rw [← nat_mul_mean]
    ring
  have hpref :
      ‖partialSum (fun n => (hilbertSequence f n : ℂ)) N‖ ≤
        ‖f‖ * x * Real.sqrt x := by
    have hsqrt : Real.sqrt (N : ℝ) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (by dsimp [x]; push_cast; linarith)
    have h := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (norm_nonneg f) hx.le)
    have hprefix := hilbert_prefix_norm_le f N
    have hxcast : x = (N : ℝ) + 1 := by simp [x]
    rw [← hxcast] at hprefix
    exact hprefix.trans h
  have hp1 : x ^ (-s.re - 1) * x = x ^ (-s.re) := by
    calc
      _ = x ^ ((-s.re - 1) + 1) := by rw [Real.rpow_add hx, Real.rpow_one]
      _ = _ := by congr 1 <;> ring
  have hp2 : x ^ (-s.re) * Real.sqrt x = x ^ ((1 / 2 : ℝ) - s.re) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    congr 1
    ring
  rw [hrewrite, norm_mul]
  calc
    _ ≤ (‖s‖ * x ^ (-s.re - 1)) * (‖f‖ * x * Real.sqrt x) := by
      apply mul_le_mul (mellinFirst_norm_le s hs (N + 1) (Nat.succ_pos N))
        hpref (norm_nonneg _)
      positivity
    _ = (‖s‖ * ‖f‖) * ((x ^ (-s.re - 1) * x) * Real.sqrt x) := by ring
    _ = _ := by rw [hp1, hp2]

/-- The retained Abel terminal term vanishes throughout the strict critical half-plane. -/
theorem hilbert_terminal_pairing_tendsto_zero (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) * mellinFirst s (N + 1) *
      mean (fun n => (hilbertSequence f n : ℂ)) N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hp := (tendsto_rpow_neg_atTop (by linarith : 0 < s.re - (1 / 2 : ℝ))).comp ht
  have hp' : Tendsto (fun N : ℕ =>
      ((N + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - s.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using hp
  apply squeeze_zero_norm
    (a := fun N => (‖s‖ * ‖f‖) *
      ((N + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - s.re))
  · intro N
    exact hilbert_terminal_pairing_norm_le f s (by linarith) N
  · simpa only [mul_zero] using hp'.const_mul (‖s‖ * ‖f‖)

/-- Actual summability is established before the second pairing's limit is identified. -/
theorem hilbert_second_pairing_summable (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun k : ℕ => mellinSecond s (k + 1) *
      mean (fun n => (hilbertSequence f n : ℂ)) (k + 1)) := by
  have hp : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-s.re - (1 / 2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr
      (by linarith : -s.re - (1 / 2 : ℝ) < -1)).comp_injective
        (fun _ _ h => Nat.add_right_cancel h)
  apply (hp.mul_left (2 * ‖s * (s + 1)‖ * ‖f‖)).of_norm_bounded
  intro k
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hpow :
      ((k + 1 : ℕ) : ℝ) ^ (-s.re - 1) *
        ((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) =
      ((k + 1 : ℕ) : ℝ) ^ (-s.re - (1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hk]
    congr 1
    ring
  rw [norm_mul]
  calc
    _ ≤ (‖s * (s + 1)‖ * ((k + 1 : ℕ) : ℝ) ^ (-s.re - 1)) *
        (2 * ‖f‖ * ((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul (mellinSecond_norm_le s (by linarith) _ (Nat.succ_pos k))
        (hilbert_mean_norm_le f _ (Nat.succ_pos k)) (norm_nonneg _)
      positivity
    _ = (2 * ‖s * (s + 1)‖ * ‖f‖) *
        (((k + 1 : ℕ) : ℝ) ^ (-s.re - 1) *
          ((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-- The full second-difference Mellin identity for every Hilbert vector. -/
theorem cesaro_mellin_pairing_hilbert (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    (∑' k : ℕ, mellinSecond s (k + 1) *
      mean (fun n => (hilbertSequence f n : ℂ)) (k + 1)) =
        s * paretoMellin f s := by
  let F : ℕ → ℂ := fun n => (hilbertSequence f n : ℂ)
  have hfirst := (hasSum_first_mellin_pairing f s hs).tendsto_sum_nat
  have hsecond := (hilbert_second_pairing_summable f s hs).hasSum.tendsto_sum_nat
  have hboundary := hilbert_terminal_pairing_tendsto_zero f s hs
  have he : (fun N => partialSum (fun n => mellinSecond s n * mean F n) N) =
      (fun N => partialSum (fun n => mellinFirst s n * F n) N -
        (N : ℂ) * mellinFirst s (N + 1) * mean F N) := by
    funext N
    have h := mellin_pairing_prefix s F N
    linear_combination -h
  change Tendsto (fun N => partialSum (fun n => mellinSecond s n * mean F n) N)
    atTop (𝓝 _) at hsecond
  rw [he] at hsecond
  exact tendsto_nhds_unique hsecond
    (by simpa only [sub_zero, partialSum, F] using hfirst.sub hboundary)

end RiemannResearch.Analysis.Cesaro

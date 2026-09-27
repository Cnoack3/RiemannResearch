/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorTruncationBounds
import RiemannResearch.RH.DampedMobiusSignedGram
import RiemannResearch.RH.ParetoDominatedConvergence

/-!
# General signed truncation and dominated-convergence criterion

Extends the half-damping argument from commit 3d085c93 to arbitrary
monotone prefix and decreasing density-tail profiles. A separate signed
residue-head bound is retained, so future cancellation can replace the
absolute coefficient mass estimate. Summability is an explicit analytic
profile condition; actual arithmetic finite energy is a conclusion.
-/

noncomputable section
open Filter Set RiemannResearch.Analysis
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The complete three-piece envelope, with a freely chosen signed residue
head bound. Choosing coefficient mass is optional. -/
def arithmeticHyperbolaProfile (R : ℕ → ℕ → ℝ) (P T : ℕ → ℝ)
    (N y : ℕ) : ℝ :=
  R N y + (∑ k ∈ Finset.range (N / y), P (N / (k + 1))) +
    (N / y : ℕ) * P y + 2 * (N : ℝ) * T y

theorem arithmeticFloorHilbertPartial_profile_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (R : ℕ → ℕ → ℝ) (P T : ℕ → ℝ)
    (hPmono : Monotone P)
    (hP : ∀ t, |positiveArithmeticPrefix w t| ≤ P t)
    (hTmono : AntitoneOn T (Set.Ici 1))
    (hTnonneg : ∀ t, 0 < t → 0 ≤ T t)
    (hT : ∀ t, 0 < t →
      |C - positiveArithmeticPrefix (fun d => w d / (d : ℝ)) t| ≤ T t)
    (hR : ∀ M N y, |∑ d ∈ Finset.range (y + 1),
      (arithmeticCutoffWeight w M d / (d : ℝ)) * residue d N| ≤ R N y)
    (M N y : ℕ) (hy : 0 < y) (hyN : y ≤ N) :
    |hilbertSequence (arithmeticFloorHilbertPartial w M) N| ≤
      arithmeticHyperbolaProfile R P T N y := by
  let v := arithmeticCutoffWeight w M
  let c := positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M
  have hp (t : ℕ) : |positiveArithmeticPrefix v t| ≤ P t :=
    arithmeticCutoff_prefix_profile_bound w P hPmono hP M t
  have ht := arithmeticCutoff_density_tail_profile_bound
    w C T hTmono hTnonneg hT M y hy
  have hm : |∑ k ∈ Finset.range (N / y), positiveArithmeticPrefix v (N / (k + 1))| ≤
      ∑ k ∈ Finset.range (N / y), P (N / (k + 1)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hp _))
  have he : |(N / y : ℕ) * positiveArithmeticPrefix v y| ≤ (N / y : ℕ) * P y := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N / y : ℕ))]
    exact mul_le_mul_of_nonneg_left (hp y) (by positivity)
  have hd : |(N : ℝ) * (c - ∑ d ∈ Finset.range (y + 1), v d / (d : ℝ))| ≤
      2 * (N : ℝ) * T y := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    have h := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    simpa only [mul_assoc, mul_left_comm] using h
  rw [arithmeticFloorHilbertPartial_sequence_cutoff]
  change |arithmeticFloorPrefix v N - (N : ℝ) * c| ≤ _
  rw [arithmeticFloorPrefix_centered_hyperbola v (arithmeticCutoffWeight_zero w hw0 M) c hy hyN]
  have hh := hR M N y
  change |∑ d ∈ Finset.range (y + 1), (v d / (d : ℝ)) * residue d N| ≤ _ at hh
  have h1 := abs_add_le
    (-(∑ d ∈ Finset.range (y + 1), (v d / (d : ℝ)) * residue d N))
    (∑ k ∈ Finset.range (N / y), positiveArithmeticPrefix v (N / (k + 1)))
  have h2 := abs_sub_le
    (-(∑ d ∈ Finset.range (y + 1), (v d / (d : ℝ)) * residue d N) +
      (∑ k ∈ Finset.range (N / y), positiveArithmeticPrefix v (N / (k + 1))))
    0 ((N / y : ℕ) * positiveArithmeticPrefix v y)
  have h3 := abs_sub_le
    (-(∑ d ∈ Finset.range (y + 1), (v d / (d : ℝ)) * residue d N) +
      (∑ k ∈ Finset.range (N / y), positiveArithmeticPrefix v (N / (k + 1))) -
      (N / y : ℕ) * positiveArithmeticPrefix v y)
    0 ((N : ℝ) * (c - ∑ d ∈ Finset.range (y + 1), v d / (d : ℝ)))
  simp only [sub_zero, zero_sub, abs_neg] at h1 h2 h3
  unfold arithmeticHyperbolaProfile
  linarith

/-- Truncation and dominated convergence for arbitrary signed arithmetic
profiles. Neither finite energy nor existence of a Hilbert limit is assumed.
The residue head may use cancellation; coefficient mass is one provider. -/
theorem arithmeticFloorHilbertPartial_tendsto_of_profiles
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ)
    (hdensity : HasSum (fun m : ℕ => w (m + 1) / ((m + 1 : ℕ) : ℝ)) C)
    (R : ℕ → ℕ → ℝ) (P T : ℕ → ℝ)
    (hPmono : Monotone P)
    (hP : ∀ t, |positiveArithmeticPrefix w t| ≤ P t)
    (hTmono : AntitoneOn T (Set.Ici 1))
    (hTnonneg : ∀ t, 0 < t → 0 ≤ T t)
    (hT : ∀ t, 0 < t →
      |C - positiveArithmeticPrefix (fun d => w d / (d : ℝ)) t| ≤ T t)
    (hR : ∀ M N y, |∑ d ∈ Finset.range (y + 1),
      (arithmeticCutoffWeight w M d / (d : ℝ)) * residue d N| ≤ R N y)
    (Y : ℕ → ℕ) (hY : ∀ᶠ N : ℕ in atTop, 0 < Y N ∧ Y N ≤ N)
    (hs : Summable (fun N => positiveWeight N *
      (arithmeticHyperbolaProfile R P T N (Y N)) ^ 2)) :
    ∃ f : ThresholdHilbert,
      (∀ n, hilbertSequence f n = arithmeticFloorPrefix w n - (n : ℝ) * C) ∧
      Tendsto (arithmeticFloorHilbertPartial w) atTop (𝓝 f) := by
  have hlim (n : ℕ) : Tendsto (fun M => hilbertSequence (arithmeticFloorHilbertPartial w M) n)
      atTop (𝓝 (arithmeticFloorPrefix w n - (n : ℝ) * C)) := by
    have h := (tendsto_const_nhds (x := arithmeticFloorPrefix w n) (f := (atTop : Filter ℕ))).sub
      (hdensity.tendsto_sum_nat.const_mul (n : ℝ))
    apply h.congr'
    filter_upwards [eventually_ge_atTop n] with M hM
    exact (arithmeticFloorHilbertPartial_sequence_of_le w M n hM).symm
  obtain ⟨f, hf, hconv⟩ := pareto_exists_tendsto_of_eventual_dominated_coordinates
    (arithmeticFloorHilbertPartial w) (fun n => arithmeticFloorPrefix w n - (n : ℝ) * C)
    (fun N => arithmeticHyperbolaProfile R P T N (Y N))
    (by simp [arithmeticFloorPrefix]) hs hlim (by
      filter_upwards [hY] with N hN
      intro M
      exact arithmeticFloorHilbertPartial_profile_bound w hw0 C R P T
        hPmono hP hTmono hTnonneg hT hR M N (Y N) hN.1 hN.2)
  exact ⟨f, congrFun hf, hconv⟩

end RiemannResearch.RH.Pareto

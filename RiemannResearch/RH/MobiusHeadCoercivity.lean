/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteDivisorCoercivity
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.CRTLegalCoordinates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Genuine Mobius differences and normalized residue head coercivity

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 2--3.
The complete signed Mobius difference is identified with the finite divisor
convolution. Actual normalized-residue coefficients, including every high
conductor contribution to the slope, satisfy the improved finite-head bound.
These estimates do not bound the signed canonical short-head response.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.FiniteDivisorCoercivity

private theorem quotient_divisor_involution {n a : ℕ} (hn : 0 < n)
    (hd : a ∣ n) : n / (n / a) = a := by
  have hprod : (n / a) * a = n := Nat.div_mul_cancel hd
  have hqpos : 0 < (n / a : ℕ) := Nat.pos_of_ne_zero (by
    intro hq
    apply hn.ne'
    calc
      n = (n / a) * a := (Nat.div_mul_cancel hd).symm
      _ = 0 := by rw [hq, zero_mul])
  have hqd : n / a ∣ n := ⟨a, hprod.symm⟩
  apply Nat.eq_of_mul_eq_mul_left hqpos
  calc
    (n / a) * (n / (n / a)) = n := by
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hqd
    _ = (n / a) * a := hprod.symm

private theorem sum_divisors_swap (n : ℕ) (hn : 0 < n) (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ n.divisors, F (n / a) a) =
      ∑ a ∈ n.divisors, F a (n / a) := by
  classical
  refine Finset.sum_bij (fun a _ => n / a) ?_ ?_ ?_ ?_
  · intro a ha
    have hd := Nat.dvd_of_mem_divisors ha
    exact Nat.mem_divisors.mpr
      ⟨⟨a, (Nat.div_mul_cancel hd).symm⟩, hn.ne'⟩
  · intro a ha b hb he
    have ha' := quotient_divisor_involution hn (Nat.dvd_of_mem_divisors ha)
    have hb' := quotient_divisor_involution hn (Nat.dvd_of_mem_divisors hb)
    rw [← ha', ← hb', he]
  · intro a ha
    have hd := Nat.dvd_of_mem_divisors ha
    refine ⟨n / a, Nat.mem_divisors.mpr
      ⟨⟨a, (Nat.div_mul_cancel hd).symm⟩, hn.ne'⟩, ?_⟩
    exact quotient_divisor_involution hn hd
  · intro a ha
    rw [quotient_divisor_involution hn (Nat.dvd_of_mem_divisors ha)]

/-- The normalized genuine Mobius difference is the finite dilation convolution,
including the zero coordinate and every signed divisor term. -/
theorem mobiusDifference_div_eq_dilation (H n : ℕ) (f : ℕ → ℝ) (hnH : n ≤ H) :
    mobiusDifference n f / (n : ℝ) =
      mobiusDilation H (normalizedDifference f) n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [mobiusDifference, mobiusDilation,
      RiemannResearch.Analysis.FiniteDivisorCoercivity.dilation, normalizedDifference]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hsub : n.divisors ⊆ Finset.Icc 1 H := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
      (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors ha)).trans hnH⟩
  unfold mobiusDifference mobiusDilation
  rw [sum_divisors_swap n hn
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * (f b - f (b - 1)))]
  rw [Finset.sum_div]
  calc
    _ = ∑ a ∈ n.divisors,
        ((ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) *
          RiemannResearch.Analysis.FiniteDivisorCoercivity.dilation a
            (normalizedDifference f) n := by
      apply Finset.sum_congr rfl
      intro a ha
      have hd := Nat.dvd_of_mem_divisors ha
      have haR : (a : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors ha))
      have hqpos : 0 < (n / a : ℕ) := Nat.pos_of_ne_zero (by
        intro hq
        apply hn.ne'
        calc
          n = (n / a) * a := (Nat.div_mul_cancel hd).symm
          _ = 0 := by rw [hq, zero_mul])
      have hqR : ((n / a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hqpos.ne'
      have hp : (n : ℝ) = ((n / a : ℕ) : ℝ) * (a : ℝ) := by
        exact_mod_cast (Nat.div_mul_cancel hd).symm
      simp only [RiemannResearch.Analysis.FiniteDivisorCoercivity.dilation,
        if_pos hd, normalizedDifference]
      rw [hp]
      field_simp [haR, hqR]
    _ = _ := Finset.sum_subset hsub (by
      intro a ha hnot
      have hnd : ¬ a ∣ n := by
        intro hd
        exact hnot (Nat.mem_divisors.mpr ⟨hd, hn0⟩)
      simp [RiemannResearch.Analysis.FiniteDivisorCoercivity.dilation, hnd])

/-- Coefficient energy in the genuine Mobius coordinates, with the improved
finite-head factor (2-1/H)^2 in place of 4. -/
theorem mobiusDifference_head_energy_le (H : ℕ) (hH : 1 ≤ H)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    energy H (fun n => mobiusDifference n f / (n : ℝ)) ≤
      (headDifferenceFactor H * mobiusMass H) ^ 2 *
        energy H (fun n => f n / (n : ℝ)) := by
  have he : energy H (fun n => mobiusDifference n f / (n : ℝ)) =
      energy H (mobiusDilation H (normalizedDifference f)) := by
    dsimp only [energy]
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun x : ℝ => x ^ 2)
      (mobiusDifference_div_eq_dilation H n f
        (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
  rw [he]
  calc
    _ ≤ mobiusMass H ^ 2 * energy H (normalizedDifference f) :=
      mobius_dilation_energy_le H (normalizedDifference f)
    _ ≤ mobiusMass H ^ 2 * (headDifferenceFactor H ^ 2 *
        energy H (fun n => f n / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (normalized_difference_energy_le H hH f hf0) (sq_nonneg _)
    _ = _ := by ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.Analysis.FiniteDivisorCoercivity
open RiemannResearch.RH.Pareto

/-- Exact leading-slope and low-conductor accounting, retaining every conductor
in the synthesis even when it lies beyond the head. -/
theorem normalizedResidueSynthesis_charge_energy_exact
    (H : ℕ) (hH : 1 ≤ H) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    energy H (fun n =>
      mobiusDifference n (normalizedResidueSynthesis s c) / (n : ℝ)) =
      (∑ d ∈ s, c d / (d : ℝ)) ^ 2 +
        ∑ d ∈ s.filter (fun d => d ≤ H), (c d / (d : ℝ)) ^ 2 := by
  classical
  let f := normalizedResidueSynthesis s c
  let I := s.filter (fun d => d ≤ H)
  have hsub : I ⊆ Finset.range (H + 1) := by
    intro d hd
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hd).2)
  have h0 : 0 ∉ I := by
    intro h
    have := hs 0 (Finset.mem_filter.mp h).1
    omega
  have h1 : 1 ∉ I := by
    intro h
    have := hs 1 (Finset.mem_filter.mp h).1
    omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.range (H + 1)) :
      (mobiusDifference n f / (n : ℝ)) ^ 2 =
        (if n = 1 then f 1 ^ 2 else 0) +
        (if n ∈ I then (c n / (n : ℝ)) ^ 2 else 0) := by
    by_cases hn0 : n = 0
    · subst n
      simp [h0]
    by_cases hn1 : n = 1
    · subst n
      simp [f, mobiusDifference, normalizedResidueSynthesis_zero, h1]
    have hn2 : 1 < n := by omega
    have hnH : n ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    rw [normalizedResidueSynthesis_mobiusDifference s c n hn2]
    by_cases hns : n ∈ s
    · simp [I, hns, hnH, hn1, neg_div]
    · simp [I, hns, hn1]
  have hfirst :
      (∑ n ∈ Finset.range (H + 1), if n = 1 then f 1 ^ 2 else 0) = f 1 ^ 2 := by
    simp [show 1 < H + 1 by omega]
  have hfilter : (Finset.range (H + 1)).filter (fun n => n ∈ I) = I := by
    ext n
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hn => hsub hn)
  have hsecond :
      (∑ n ∈ Finset.range (H + 1),
        if n ∈ I then (c n / (n : ℝ)) ^ 2 else 0) =
      ∑ n ∈ I, (c n / (n : ℝ)) ^ 2 := by
    rw [← Finset.sum_filter, hfilter]
  calc
    _ = (∑ n ∈ Finset.range (H + 1),
        if n = 1 then f 1 ^ 2 else 0) +
        ∑ n ∈ Finset.range (H + 1),
          if n ∈ I then (c n / (n : ℝ)) ^ 2 else 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hpoint
    _ = f 1 ^ 2 + ∑ n ∈ I, (c n / (n : ℝ)) ^ 2 := by
      rw [hfirst, hsecond]
    _ = _ := by
      rw [show f 1 = ∑ d ∈ s, c d / (d : ℝ) from
        normalizedResidueSynthesis_one s c hs]

/-- The exact arithmetic coefficient/slope provider. High conductors remain
in the reciprocal slope and the actual full synthesis. -/
theorem normalizedResidueSynthesis_head_coercivity
    (H : ℕ) (hH : 1 ≤ H) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    (∑ d ∈ s, c d / (d : ℝ)) ^ 2 +
        ∑ d ∈ s.filter (fun d => d ≤ H), (c d / (d : ℝ)) ^ 2 ≤
      (headDifferenceFactor H * mobiusMass H) ^ 2 *
        energy H (fun n => normalizedResidueSynthesis s c n / (n : ℝ)) := by
  rw [← normalizedResidueSynthesis_charge_energy_exact H hH s c hs]
  exact mobiusDifference_head_energy_le H hH (normalizedResidueSynthesis s c)
    (normalizedResidueSynthesis_zero s c)


/-- When the cutoff contains the whole dictionary, the slope square is kept. -/
theorem normalizedResidueSynthesis_full_coercivity
    (H : ℕ) (hH : 1 ≤ H) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) :
    (∑ d ∈ s, c d / (d : ℝ)) ^ 2 +
        (∑ d ∈ s, (c d / (d : ℝ)) ^ 2) ≤
      (headDifferenceFactor H * mobiusMass H) ^ 2 *
        energy H (fun n => normalizedResidueSynthesis s c n / (n : ℝ)) := by
  have hfilter : s.filter (fun d => d ≤ H) = s := by
    exact Finset.filter_true_of_mem (fun d hd => (hs d hd).2)
  simpa only [hfilter] using normalizedResidueSynthesis_head_coercivity
    H hH s c (fun d hd => (hs d hd).1)


end RiemannResearch.RH.CRTBlock

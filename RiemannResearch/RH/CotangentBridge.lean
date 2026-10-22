/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResidueSmallGram
import RiemannResearch.RH.ParetoReflectionVariance
import Mathlib.Tactic.LinearCombination

/-!
# Actual cotangent-difference identity for the complete residue Gram

This uses genuine progression weights and the already proved digamma reflection.
The reflection identity is DLMF 5.5.4 (https://dlmf.nist.gov/5.5),
used for the proof strategy and exact statement.
The final contraction to `cotangentV a b` is separate: it requires a finite
cotangent multiplication/regrouping lemma. No RH hypothesis enters this file.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def periodCotangent (Q : ℕ) (r : ℕ) : ℝ :=
  Real.cos (Real.pi * (r : ℝ) / (Q : ℝ)) /
    Real.sin (Real.pi * (r : ℝ) / (Q : ℝ))

theorem re_digamma_reflection_real {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Complex.digamma (x : ℂ)).re -
      (Complex.digamma ((1 - x : ℝ) : ℂ)).re =
        -Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) := by
  have hs : Real.sin (Real.pi * x) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by nlinarith [Real.pi_pos]))
  have harg : (Real.pi : ℂ) * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by
    push_cast
    rfl
  have hsc : Complex.sin ((Real.pi : ℂ) * (x : ℂ)) ≠ 0 := by
    rw [harg, ← Complex.ofReal_sin]
    exact_mod_cast hs
  have h := Complex.digamma_reflection_of_pos_re (x : ℂ)
    (by simpa using hx) (by simpa using hx1) hsc
  rw [harg, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; rfl] at h
  have he : -(Real.pi : ℂ) * (Real.cos (Real.pi * x) : ℂ) /
      (Real.sin (Real.pi * x) : ℂ) =
      ((-Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he] at h
  simpa only [Complex.sub_re, Complex.ofReal_re] using congrArg Complex.re h

/-- Interior reflection weights; both endpoints remain excluded explicitly. -/
theorem progressionWeight_add_reflected (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r + 1 < Q) :
    progressionWeight Q r + progressionWeight Q (Q - 1 - r) =
      Real.pi / (Q : ℝ) * (periodCotangent Q r - periodCotangent Q (r+1)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrtR : (r : ℝ) + 1 < Q := by exact_mod_cast hrQ
  have hx0 : 0 < (r : ℝ) / Q := div_pos hrR hQr
  have hx1 : (r : ℝ) / Q < 1 := (div_lt_one hQr).mpr (by linarith)
  have hy0 : 0 < ((r : ℝ) + 1) / Q := by positivity
  have hy1 : ((r : ℝ) + 1) / Q < 1 := (div_lt_one hQr).mpr hrtR
  have hx := re_digamma_reflection_real hx0 hx1
  have hy := re_digamma_reflection_real hy0 hy1
  rw [progressionWeight_eq_digamma Q r hQ hr (by omega),
    progressionWeight_eq_digamma Q (Q-1-r) hQ (by omega) (by omega)]
  have he1 : ((Q - 1 - r : ℕ) : ℝ) / Q = 1 - ((r : ℝ) + 1) / Q := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  have he2 : (((Q - 1 - r : ℕ) : ℝ) + 1) / Q = 1 - (r : ℝ) / Q := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [he1, he2]
  unfold periodCotangent
  push_cast
  have hxarg : Real.pi * ((r : ℝ) / Q) = Real.pi * (r : ℝ) / Q := by ring
  have hyarg : Real.pi * (((r : ℝ)+1) / Q) = Real.pi * ((r : ℝ)+1) / Q := by ring
  rw [hxarg] at hx
  rw [hyarg] at hy
  push_cast at hx hy
  linear_combination (1 / (Q : ℝ)) * hy - (1 / (Q : ℝ)) * hx

/-- Any symmetric period profile vanishing at both reflected endpoint sites
has an exact cotangent-difference evaluation in the original Pareto measure. -/
theorem paretoMean_eq_cotangent_difference (Q : ℕ) (hQ : 0 < Q)
    (h : ℕ → ℝ) {B : ℝ} (hb : ∀ k, |h k| ≤ B)
    (hp : ∀ k, h (k+Q) = h k) (hz : h 0 = 0)
    (href : ∀ k, k < Q → h (Q-1-k) = h k) :
    paretoMean h = Real.pi / (2 * (Q : ℝ)) *
      ∑ r : Fin Q, h r.val *
        (periodCotangent Q r.val - periodCotangent Q (r.val+1)) := by
  rw [periodic_paretoMean_zero_residues Q hQ h hb hp]
  have hlast : h (Q-1) = 0 := by simpa [hz] using href 0 hQ
  have hrev (r : Fin Q) : h r.rev.val = h r.val := by
    simpa [Fin.val_rev, Nat.sub_sub, Nat.add_comm] using href r.val r.isLt
  have he : (∑ r : Fin Q, residueMass Q r.rev * h r.val) =
      ∑ r : Fin Q, residueMass Q r * h r.val := by
    have hh := Equiv.sum_comp Fin.revPerm (fun r : Fin Q => residueMass Q r * h r.val)
    change (∑ r : Fin Q, residueMass Q r.rev * h r.rev.val) =
      ∑ r : Fin Q, residueMass Q r * h r.val at hh
    simpa only [hrev] using hh
  have hpair : (∑ r : Fin Q,
      (residueMass Q r + residueMass Q r.rev) * h r.val) =
      Real.pi / (Q : ℝ) * ∑ r : Fin Q, h r.val *
        (periodCotangent Q r.val - periodCotangent Q (r.val+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr0 : r.val = 0
    · simp [hr0, hz]
    by_cases hrlast : r.val = Q-1
    · simp [hrlast, hlast]
    have hr : 0 < r.val := by omega
    have hrQ : r.val+1 < Q := by omega
    have hrevval : r.rev.val = Q-1-r.val := by
      simp [Fin.val_rev, Nat.sub_sub, Nat.add_comm]
    have hrev0 : r.rev.val ≠ 0 := by rw [hrevval]; omega
    rw [residueMass, residueMass, if_neg hr0, if_neg hrev0, hrevval,
      progressionWeight_add_reflected Q r.val hQ hr hrQ]
    ring
  simp_rw [add_mul] at hpair
  rw [Finset.sum_add_distrib, he] at hpair
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  field_simp at hpair ⊢
  nlinarith

def centeredResidueProduct (a b k : ℕ) : ℝ :=
  residue a k * residue b k - ((b : ℝ)-1)/2 * residue a k -
    ((a : ℝ)-1)/2 * residue b k

theorem centeredResidueProduct_zero (a b : ℕ) :
    centeredResidueProduct a b 0 = 0 := by simp [centeredResidueProduct, residue]

theorem centeredResidueProduct_reflection (Q a b k : ℕ)
    (ha : 0 < a) (hb : 0 < b) (haQ : a ∣ Q) (hbQ : b ∣ Q) (hk : k < Q) :
    centeredResidueProduct a b (Q-1-k) = centeredResidueProduct a b k := by
  have h1 := residue_reflection_sum ha haQ hk
  have h2 := residue_reflection_sum hb hbQ hk
  rw [Nat.cast_sub (by omega)] at h1 h2
  push_cast at h1 h2
  unfold centeredResidueProduct
  have he1 : residue a (Q-1-k) = (a : ℝ)-1-residue a k := by linarith
  have he2 : residue b (Q-1-k) = (b : ℝ)-1-residue b k := by linarith
  rw [he1, he2]
  ring

def residueDifferenceCotangentCore (Q a b : ℕ) : ℝ :=
  1 / (2 * (Q : ℝ)) * ∑ r : Fin Q, centeredResidueProduct a b r.val *
    (periodCotangent Q r.val - periodCotangent Q (r.val+1))

/-- Complete actual residue Gram; no unproved analytic matrix identification
is a hypothesis. `Q` may be any positive common period. -/
theorem paretoInner_residue_eq_differenceCotangentCore (Q a b : ℕ)
    (hQ : 0 < Q) (ha : 0 < a) (hb : 0 < b) (haQ : a ∣ Q) (hbQ : b ∣ Q) :
    paretoInner (residue a) (residue b) =
      Real.pi * residueDifferenceCotangentCore Q a b +
        (((b : ℝ)-1) * Real.log a + ((a : ℝ)-1) * Real.log b) / 2 := by
  have hba : ∀ k, |residue a k| ≤ (a : ℝ) := fun k => residue_abs_le a k ha
  have hbb : ∀ k, |residue b k| ≤ (b : ℝ) := fun k => residue_abs_le b k hb
  have hb1 := bounded_product hba hbb
  have hb2 := bounded_const_mul hba (((b : ℝ)-1)/2)
  have hb3 := bounded_const_mul hbb (((a : ℝ)-1)/2)
  have hbound := bounded_sub (bounded_sub hb1 hb2) hb3
  have hp : ∀ k, centeredResidueProduct a b (k+Q) = centeredResidueProduct a b k := by
    intro k
    simp only [centeredResidueProduct, residue_period_of_dvd haQ, residue_period_of_dvd hbQ]
  have hmean := paretoMean_eq_cotangent_difference Q hQ (centeredResidueProduct a b)
    hbound hp (centeredResidueProduct_zero a b)
    (fun k hk => centeredResidueProduct_reflection Q a b k ha hb haQ hbQ hk)
  have hmul (c : ℝ) (f : ℕ → ℝ) : paretoMean (fun k => c * f k) = c * paretoMean f := by
    unfold paretoMean
    simp_rw [mul_left_comm (positiveWeight _) c]
    exact tsum_mul_left
  have hdecomp : paretoMean (centeredResidueProduct a b) =
      paretoInner (residue a) (residue b) - ((b : ℝ)-1)/2 * Real.log a -
        ((a : ℝ)-1)/2 * Real.log b := by
    unfold centeredResidueProduct
    rw [paretoMean_sub (bounded_sub hb1 hb2) hb3, paretoMean_sub hb1 hb2,
      hmul, hmul, paretoMean_residue a ha, paretoMean_residue b hb]
    rfl
  rw [hdecomp] at hmean
  unfold residueDifferenceCotangentCore
  rw [show Real.pi / (2 * (Q : ℝ)) = Real.pi * (1 / (2 * (Q : ℝ))) by ring] at hmean
  linear_combination hmean

end RiemannResearch.RH.Pareto

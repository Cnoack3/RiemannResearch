/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorWaveletDensity

/-!
# Finite divisor / wavelet cutoffs and gcd coordinates

Source: Prime Tensor CRT RH Research Project (2 November 2026), Agenda A.
The triangular argument extends the existing full-span density proof to
finite divisor-closed cutoffs; the physical coordinates are gcd invariant.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert QDivisibilityDensity

/-- Every divisor of a positive cutoff is in its finite wavelet span. -/
theorem qDivisor_mem_divisorWavelet_cutoff (M : ℕ) (hM : 0 < M) :
    ∀ r : ℕ, 0 < r → r ∣ M →
      qDivisor r ∈ Submodule.span ℝ
        (divisorWavelet '' (↑M.divisors : Set ℕ)) := by
  let W := Submodule.span ℝ (divisorWavelet '' (↑M.divisors : Set ℕ))
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr hrM
    have hrmem : r ∈ M.divisors :=
      Nat.mem_divisors.mpr ⟨hrM, ne_of_gt hM⟩
    have hW : divisorWavelet r ∈ W :=
      Submodule.subset_span ⟨r, hrmem, rfl⟩
    have hsmall :
        (∑ k ∈ r.divisors.erase r,
          ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) •
            qDivisor k) ∈ W := by
      apply W.sum_mem
      intro k hk
      have hkdiv : k ∈ r.divisors := (Finset.mem_erase.mp hk).2
      have hkne : k ≠ r := (Finset.mem_erase.mp hk).1
      have hkpos : 0 < k := Nat.pos_of_mem_divisors hkdiv
      have hkr : k ∣ r := Nat.dvd_of_mem_divisors hkdiv
      have hkle : k ≤ r := Nat.le_of_dvd hr hkr
      have hkM : k ∣ M := dvd_trans hkr hrM
      exact W.smul_mem _ (ih k (lt_of_le_of_ne hkle hkne) hkpos hkM)
    have hscaled : (r : ℝ) ^ 2 • qDivisor r ∈ W := by
      have he := divisorWavelet_triangular r hr
      have he' : (r : ℝ) ^ 2 • qDivisor r = divisorWavelet r -
          (∑ k ∈ r.divisors.erase r,
            ((ArithmeticFunction.moebius (r / k) : ℝ) * (k : ℝ) ^ 2) •
              qDivisor k) := by
        exact eq_sub_of_add_eq' he
      rw [he']
      exact W.sub_mem hW hsmall
    have hr0 : (r : ℝ) ^ 2 ≠ 0 := by positivity
    have hinv := W.smul_mem (((r : ℝ) ^ 2)⁻¹) hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hr0, one_smul] using hinv

/-- The finite wavelet cutoff has exactly the finite divisibility span. -/
theorem divisorWavelet_cutoff_span_eq (M : ℕ) (hM : 0 < M) :
    Submodule.span ℝ (divisorWavelet '' (↑M.divisors : Set ℕ)) =
      Submodule.span ℝ (qDivisor '' (↑M.divisors : Set ℕ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨r, hr, rfl⟩
    have hrM : r ∣ M := Nat.dvd_of_mem_divisors hr
    unfold divisorWavelet
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨k, ?_, rfl⟩
    exact Nat.mem_divisors.mpr
      ⟨dvd_trans (Nat.dvd_of_mem_divisors hk) hrM, ne_of_gt hM⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨r, hr, rfl⟩
    exact qDivisor_mem_divisorWavelet_cutoff M hM r
      (Nat.pos_of_mem_divisors hr) (Nat.dvd_of_mem_divisors hr)

/-- Divisibility by a divisor of `M` is determined by the gcd with `M`.
The positive physical-coordinate hypotheses avoid the definition's
special zero coordinate. -/
theorem positiveDivisor_gcd_cutoff (M d n : ℕ)
    (hM : 0 < M) (hn : 0 < n) (hdM : d ∣ M) :
    positiveDivisor d (Nat.gcd n M) = positiveDivisor d n := by
  have hg : Nat.gcd n M ≠ 0 := by
    intro h
    have hzero : M = 0 := by
      simpa [h] using Nat.gcd_dvd_right n M
    exact (ne_of_gt hM) hzero
  have hd : d ∣ Nat.gcd n M ↔ d ∣ n :=
    ⟨fun h => dvd_trans h (Nat.gcd_dvd_left n M),
      fun h => Nat.dvd_gcd h hdM⟩
  simp only [positiveDivisor, hg, ne_of_gt hn, if_false, hd]

/-- The actual Q-Hilbert divisor vector has gcd-cell-constant coordinates. -/
theorem qSequence_qDivisor_gcd_cutoff (M d n : ℕ)
    (hM : 0 < M) (hn : 0 < n) (hdM : d ∣ M) :
    qSequence (qDivisor d) (Nat.gcd n M) = qSequence (qDivisor d) n := by
  simpa only [qSequence_qDivisor] using
    positiveDivisor_gcd_cutoff M d n hM hn hdM

/-- Every vector in the finite divisibility cutoff is constant on gcd cells. -/
theorem qSequence_gcd_of_mem_divisor_cutoff (M : ℕ) (hM : 0 < M)
    (f : QHilbert)
    (hf : f ∈ Submodule.span ℝ (qDivisor '' (↑M.divisors : Set ℕ)))
    (n : ℕ) (hn : 0 < n) :
    qSequence f (Nat.gcd n M) = qSequence f n := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨d, hd, rfl⟩
      exact qSequence_qDivisor_gcd_cutoff M d n hM hn
        (Nat.dvd_of_mem_divisors hd)
  | zero =>
      change qSequenceLinear (0 : QHilbert) (Nat.gcd n M) =
        qSequenceLinear (0 : QHilbert) n
      simp
  | add x y hx hy ihx ihy =>
      change qSequenceLinear (x + y) (Nat.gcd n M) =
        qSequenceLinear (x + y) n
      simp only [map_add, Pi.add_apply]
      exact congrArg₂ (· + ·) ihx ihy
  | smul c x hx ih =>
      change qSequenceLinear (c • x) (Nat.gcd n M) =
        qSequenceLinear (c • x) n
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact congrArg (fun z : ℝ => c * z) ih

/-- Therefore the finite wavelet cutoff also consists of gcd-cell functions. -/
theorem qSequence_gcd_of_mem_wavelet_cutoff (M : ℕ) (hM : 0 < M)
    (f : QHilbert)
    (hf : f ∈ Submodule.span ℝ (divisorWavelet '' (↑M.divisors : Set ℕ)))
    (n : ℕ) (hn : 0 < n) :
    qSequence f (Nat.gcd n M) = qSequence f n := by
  apply qSequence_gcd_of_mem_divisor_cutoff M hM f
  · rwa [← divisorWavelet_cutoff_span_eq M hM]
  · exact hn

end RiemannResearch.RH.QDivisorHilbert

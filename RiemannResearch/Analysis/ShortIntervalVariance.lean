/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Exact short-interval variance and signed additive shifts

Source: user-provided Montgomery handoff, Section 6; arithmetic interpretation
in Montgomery--Soundararajan, Primes in short intervals (2004),
https://arxiv.org/abs/math/0409258, and Goldston--Montgomery (1987).
The identities hold for every sequence over a commutative ring. In the range
notation x+1 and j+1 run through 1..N and 1..H, and h+1 is the positive gap.
Every endpoint is retained. No short-interval asymptotic is assumed or proved.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.ShortIntervalVariance

theorem square_sum_range {R : Type*} [CommRing R] (a : ℕ → R) (H : ℕ) :
    (∑ j ∈ Finset.range H, a j)^2 =
      ∑ j ∈ Finset.range H, (a j)^2 +
        2 * ∑ k ∈ Finset.range H, ∑ j ∈ Finset.range k, a j * a k := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ← Finset.sum_mul]
    rw [add_sq, ih]
    ring

theorem triangle_by_gap {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) (H : ℕ) :
    ∑ k ∈ Finset.range H, ∑ j ∈ Finset.range k, f j k =
      ∑ h ∈ Finset.range H, ∑ j ∈ Finset.range (H - (h+1)), f j (j+h+1) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.1 - x.2 - 1, x.2⟩)
    (fun y => ⟨y.2 + y.1 + 1, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k,j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨h,j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨k,j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have h : j + (k-j-1) + 1 = k := by omega
    simp [h]
  · rintro ⟨h,j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    have hh : j+h+1-j-1 = h := by omega
    simp [hh]
  · rintro ⟨k,j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have h : j + (k-j-1) + 1 = k := by omega
    simp [h]

theorem variance_decomposition {R : Type*} [CommRing R] (a : ℕ → R) (N H : ℕ) :
    (∑ x ∈ Finset.range N, (∑ j ∈ Finset.range H, a (x+j+2))^2) =
      (∑ j ∈ Finset.range H, ∑ x ∈ Finset.range N, a (x+j+2)^2) +
      2 * ∑ h ∈ Finset.range H, ∑ j ∈ Finset.range (H-(h+1)),
        ∑ x ∈ Finset.range N, a (x+j+2) * a (x+j+2+(h+1)) := by
  simp_rw [square_sum_range, triangle_by_gap]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  · exact Finset.sum_comm
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    congr 2
    omega


open scoped ArithmeticFunction

/-- The exact arithmetic sequence for the centered prime count. -/
noncomputable def centeredMangoldt (n : ℕ) : ℝ := Λ n - 1

noncomputable def centeredVariance (N H : ℕ) : ℝ :=
  ∑ x ∈ Finset.range N, (∑ j ∈ Finset.range H, centeredMangoldt (x+j+2))^2

noncomputable def centeredDiagonal (N H : ℕ) : ℝ :=
  ∑ j ∈ Finset.range H, ∑ x ∈ Finset.range N, centeredMangoldt (x+j+2)^2

noncomputable def centeredOffDiagonal (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ Finset.range H, ∑ j ∈ Finset.range (H-(h+1)),
    ∑ x ∈ Finset.range N,
      centeredMangoldt (x+j+2) * centeredMangoldt (x+j+2+(h+1))

theorem centeredVariance_exact (N H : ℕ) :
    centeredVariance N H = centeredDiagonal N H + centeredOffDiagonal N H :=
  variance_decomposition centeredMangoldt N H

/-- The signed error budget; the off-diagonal main term has a minus sign. -/
theorem centeredVariance_error_identity (N H : ℕ) :
    centeredVariance N H - (H : ℝ)*N*(Real.log N-Real.log H) =
      (centeredDiagonal N H-(H : ℝ)*N*Real.log N) +
      (centeredOffDiagonal N H+(H : ℝ)*N*Real.log H) := by
  rw [centeredVariance_exact]
  ring

/-- A conditional quantitative reduction, not a provider for either error bound. -/
theorem centeredVariance_error_le (N H : ℕ) (eD eC : ℝ)
    (hD : |centeredDiagonal N H-(H : ℝ)*N*Real.log N| ≤ eD)
    (hC : |centeredOffDiagonal N H+(H : ℝ)*N*Real.log H| ≤ eC) :
    |centeredVariance N H-(H : ℝ)*N*(Real.log N-Real.log H)| ≤ eD+eC := by
  rw [centeredVariance_error_identity]
  exact (abs_add_le _ _).trans (add_le_add hD hC)
end RiemannResearch.Analysis.ShortIntervalVariance

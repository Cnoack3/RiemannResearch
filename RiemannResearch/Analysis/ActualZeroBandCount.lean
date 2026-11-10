/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # Unconditional zero multiplicity in a boundary height band

The unit-window zero-count provider is summed over a covering by at most
Δ + 1 unit intervals. Every zero and every multiplicity copy is retained.
-/

noncomputable section
open Zeta23
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroBandCount
open ActualZeroOrdinate MontgomeryLocalMass

theorem ncount_self (a : ℝ) : Ncount a a = 0 := by
  have he : zerosIn a a = ∅ := by
    ext z
    simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_,hl,hu⟩
    exact (not_lt_of_ge hu) hl
  simp [Ncount, he]

theorem integer_window_bound (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ x : ℝ, 0 ≤ x → (Ncount x (x+1) : ℝ) ≤ C*Real.log (x+3))
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (Ncount a (a+n) : ℝ) ≤ C*n*Real.log (a+n+3) := by
  induction n with
  | zero => simp [ncount_self]
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hsplit : Ncount a (a+(n+1:ℕ)) =
        Ncount a (a+n) + Ncount (a+n) (a+n+1) := by
      have hh := Ncount_add (a:=a) (b:=a+n) (c:=a+n+1) (by linarith) (by linarith)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hh
    rw [hsplit, Nat.cast_add]
    have hlocal := hc (a+n) (by linarith)
    have hlog : Real.log (a+n+3) ≤ Real.log (a+(n+1:ℕ)+3) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    calc
      _ ≤ C*n*Real.log (a+n+3) + C*Real.log (a+n+3) := add_le_add ih hlocal
      _ = C*(n+1:ℕ)*Real.log (a+n+3) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)

theorem exists_band_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T Δ : ℝ, 9 ≤ T → 0 ≤ Δ → Δ ≤ T →
      (Ncount (T - Δ) T : ℝ) ≤ C*(Δ+1)*Real.log T := by
  obtain ⟨A,hA,hlocal⟩ := local_zero_count
  refine ⟨2*A, by positivity, ?_⟩
  intro T Δ hT hΔ hΔT
  let n := Nat.ceil Δ
  have hn1 : Δ ≤ (n : ℝ) := Nat.le_ceil Δ
  have hn2 : (n : ℝ) ≤ Δ+1 := (Nat.ceil_lt_add_one hΔ).le
  have ha : 0 ≤ T - Δ := by linarith
  have hi := integer_window_bound A (by linarith) (fun x hx => by
    simpa only [abs_of_nonneg hx] using hlocal x) (T - Δ) ha n
  have hm : (Ncount (T - Δ) T : ℝ) ≤ Ncount (T - Δ) (T - Δ+n) := by
    exact_mod_cast (Ncount_mono (le_refl (T - Δ)) (by linarith : T ≤ T - Δ+n))
  have hlog1 : Real.log (T - Δ+n+3) ≤ Real.log (T+4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log (T+4) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by linarith : T ≠ 0) (by linarith : T ≠ 0)]; ring
  have hl : 0 ≤ Real.log (T - Δ+n+3) := by
    apply Real.log_nonneg
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  calc
    _ ≤ A*n*Real.log (T - Δ+n+3) := hm.trans hi
    _ ≤ A*(Δ+1)*(2*Real.log T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hn2 (by linarith)
      · exact hlog1.trans hlog2
      · exact hl
      · positivity
    _ = _ := by ring

theorem copy_band_card_le (T a : ℝ) :
    (((Finset.univ : Finset (Copies T)).filter
      (fun i => a < copyOrdinate T i)).card : ℝ) ≤ (Ncount a T : ℝ) := by
  classical
  let s := (Finset.univ : Finset (Copies T)).filter (fun i => a < copyOrdinate T i)
  let f : {i // i ∈ s} → WindowCopies a T := fun i =>
    ⟨⟨i.val.1.val, by
      rw [Set.Finite.mem_toFinset]
      exact ⟨(mem_cutoff.mp i.val.1.property).1,
        (Finset.mem_filter.mp i.property).2, (mem_cutoff.mp i.val.1.property).2.2⟩⟩,
      i.val.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨⟨ρ,hρ⟩,k⟩,hi⟩ ⟨⟨⟨σ,hσ⟩,l⟩,hj⟩ h
    have hv : ρ = σ := congrArg (fun w => w.1.val) h
    subst σ
    have hk : k = l := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst l
    rfl
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe, card_windowCopies] at hh
  exact_mod_cast hh

theorem coefficient_error_le_count (T Δ : ℝ) (w : Copies T → ℂ)
    (hw : ∀ i, ‖w i - 1‖ ≤ 1)
    (hinner : ∀ i, copyOrdinate T i ≤ T - Δ → w i = 1) :
    (∑ i, ‖w i - 1‖^2) ≤ (Ncount (T - Δ) T : ℝ) := by
  classical
  calc
    _ ≤ ∑ i : Copies T, if T - Δ < copyOrdinate T i then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hb : T - Δ < copyOrdinate T i
      · simp only [if_pos hb]
        simpa using pow_le_pow_left₀ (norm_nonneg (w i - 1)) (hw i) 2
      · simp only [if_neg hb, hinner i (le_of_not_gt hb), sub_self, norm_zero,
          zero_pow (by decide : (2:ℕ) ≠ 0)]
        exact le_rfl
    _ = (((Finset.univ : Finset (Copies T)).filter
        (fun i => T - Δ < copyOrdinate T i)).card : ℝ) := Finset.sum_boole _ _
    _ ≤ _ := copy_band_card_le T (T - Δ)

end RiemannResearch.Analysis.ActualZeroBandCount

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Screened floor carries in the full primorial legal dictionary

Source: Christian Noack's CRT carry report, 19 October 2026, sections 3 and 5.
The application uses the existing `primorialStage`: every divisor greater
than one of the primorial is included. In the new-prime block the old
conductor `d` may be composite. No asymptotic exhaustion estimate is asserted.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTPrimorialCarry

open ZetaTwoHilbert QSquarefreePrimorialCofinality
open Pareto.SquarefreeStageExhaustion
open RiemannResearch.Analysis.ScreenedCarry

theorem residue_mem_primorialStage (n d : ℕ) (hd : 1 < d)
    (hdvd : d ∣ primorialPeriod n) : qResidue d ∈ primorialStage n :=
  Submodule.subset_span ⟨d, hd, hdvd, rfl⟩

/-- The actual old primorial space together with the new prime direction. -/
def primeBase (n p : ℕ) : Submodule ℝ QHilbert :=
  primorialStage n ⊔ Submodule.span ℝ {qResidue p}

instance primeBase_finiteDimensional (n p : ℕ) :
    FiniteDimensional ℝ (primeBase n p) := by
  unfold primeBase
  infer_instance

theorem prime_mem_primeBase (n p : ℕ) : qResidue p ∈ primeBase n p := by
  have hle : Submodule.span ℝ {qResidue p} ≤ primeBase n p := le_sup_right
  exact hle (Submodule.subset_span (by simp))

theorem divisor_mem_primeBase (n p d : ℕ) (hd : 1 < d)
    (hdvd : d ∣ primorialPeriod n) : qResidue d ∈ primeBase n p := by
  have hle : primorialStage n ≤ primeBase n p := le_sup_left
  exact hle (residue_mem_primorialStage n d hd hdvd)

/-- All old divisors, including composite ones, give actual screened carries. -/
theorem primeBase_screen_carry (n p d : ℕ) (a b t : ℤ)
    (hp : 0 < p) (hd : 1 < d) (hdvd : d ∣ primorialPeriod n)
    (hcrt : (a : ℝ) * (d : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (d : ℝ)) :
    screen (primeBase n p) (QCRTCarry.qCarry p d a b) =
      -screen (primeBase n p) (qResidue (p * d)) := by
  rw [QCRTCarry.qCarry_eq_linear p d a b t hp (by omega) hcrt]
  exact screen_carry (primeBase n p) (a : ℝ) (b : ℝ)
    (qResidue p) (qResidue d) (qResidue (p * d))
    (prime_mem_primeBase n p) (divisor_mem_primeBase n p d hd hdvd)

/-- Carries already inside a primorial have zero innovation. -/
theorem primorial_screen_carry_zero (n p q : ℕ) (a b t : ℤ)
    (hp : 1 < p) (hq : 1 < q)
    (hpvd : p ∣ primorialPeriod n) (hqvd : q ∣ primorialPeriod n)
    (hpqvd : p * q ∣ primorialPeriod n)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    screen (primorialStage n) (QCRTCarry.qCarry p q a b) = 0 := by
  rw [QCRTCarry.screen_qCarry p q a b t (by omega) (by omega) hcrt
    (primorialStage n)
    (residue_mem_primorialStage n p hp hpvd)
    (residue_mem_primorialStage n q hq hqvd)]
  rw [screen_of_mem _ (residue_mem_primorialStage n (p * q)
    (by nlinarith) hpqvd), neg_zero]

/-- The complete carry block and the complete composite block enlarge the
same old space. The indexing set contains every nontrivial old divisor. -/
theorem full_prime_block_span_eq (n p : ℕ) (a b t : ℕ → ℤ) (hp : 0 < p)
    (hcrt : ∀ d, 1 < d → d ∣ primorialPeriod n →
      (a d : ℝ) * (d : ℝ) + (b d : ℝ) * (p : ℝ) =
        1 + (t d : ℝ) * (p : ℝ) * (d : ℝ)) :
    primeBase n p ⊔ Submodule.span ℝ
      {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧
        x = QCRTCarry.qCarry p d (a d) (b d)} =
    primeBase n p ⊔ Submodule.span ℝ
      {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧
        x = qResidue (p * d)} := by
  let V := primeBase n p
  have hgp : qResidue p ∈ V := prime_mem_primeBase n p
  apply le_antisymm
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro x ⟨d, hd, hdvd, rfl⟩
    rw [QCRTCarry.qCarry_eq_linear p d (a d) (b d) (t d)
      hp (by omega) (hcrt d hd hdvd)]
    let W := primeBase n p ⊔ Submodule.span ℝ
      {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧ x = qResidue (p * d)}
    have hV : V ≤ W := le_sup_left
    have hnew : qResidue (p * d) ∈ W := by
      have hle : Submodule.span ℝ
          {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧
            x = qResidue (p * d)} ≤ W := le_sup_right
      exact hle (Submodule.subset_span ⟨d, hd, hdvd, rfl⟩)
    exact W.sub_mem (hV (V.add_mem (V.smul_mem _ hgp)
      (V.smul_mem _ (divisor_mem_primeBase n p d hd hdvd)))) hnew
  · refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
    rintro x ⟨d, hd, hdvd, rfl⟩
    let W := primeBase n p ⊔ Submodule.span ℝ
      {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧
        x = QCRTCarry.qCarry p d (a d) (b d)}
    have hV : V ≤ W := le_sup_left
    have hnew : QCRTCarry.qCarry p d (a d) (b d) ∈ W := by
      have hle : Submodule.span ℝ
          {x | ∃ d : ℕ, 1 < d ∧ d ∣ primorialPeriod n ∧
            x = QCRTCarry.qCarry p d (a d) (b d)} ≤ W := le_sup_right
      exact hle (Submodule.subset_span ⟨d, hd, hdvd, rfl⟩)
    have he : qResidue (p * d) =
        (a d : ℝ) • qResidue p + (b d : ℝ) • qResidue d -
          QCRTCarry.qCarry p d (a d) (b d) := by
      rw [QCRTCarry.qCarry_eq_linear p d (a d) (b d) (t d)
        hp (by omega) (hcrt d hd hdvd)]
      abel
    rw [he]
    exact W.sub_mem (hV (V.add_mem (V.smul_mem _ hgp)
      (V.smul_mem _ (divisor_mem_primeBase n p d hd hdvd)))) hnew

end RiemannResearch.RH.QCRTPrimorialCarry

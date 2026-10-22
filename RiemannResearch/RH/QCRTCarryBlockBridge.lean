/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.QCarryScreenedBlock
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Direct floor encodings in the existing complete carry-block theory

Source: Christian Noack's CRT-carry report, 19 October 2026, sections 3 and 5.
This assembly identifies the directly encoded floor sequence with the
existing `pairVector` and transports the full divisor-stage and trace results.
It preserves both independently developed constructions without substituting
a formal linear combination for an unproved floor realization.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCarryBlockBridge

open ZetaTwoHilbert ZetaTwoProbability QCRTCarry QCarryScreenedBlock

theorem qCarry_eq_pairVector (p q : ℕ) (a b t : ℤ)
    (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    qCarry p q a b = pairVector p q (a : ℝ) (b : ℝ) :=
  qCarry_eq_linear p q a b t hp hq hcrt

theorem screen_agrees (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (x : QHilbert) :
    QCarryScreenedBlock.screen V x =
      RiemannResearch.Analysis.ScreenedCarry.screen V x := rfl

/-- The entire directly encoded family agrees, not just isolated columns. -/
theorem qCarry_family_eq_fullBlock (L p : ℕ)
    (a b t : BlockIndex L → ℤ) (hp : 0 < p)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ)) :
    (fun d : BlockIndex L => qCarry p d.val (a d) (b d)) =
      fullBlock L p (fun d => (a d : ℝ)) (fun d => (b d : ℝ)) := by
  funext d
  have hd : 1 < d.val := (Finset.mem_filter.mp d.property).2
  exact qCarry_eq_pairVector p d.val (a d) (b d) (t d) hp (by omega) (hcrt d)

/-- Every new divisor direction is obtained by actual floor carries. -/
theorem literal_full_prime_block_stage (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (a b t : BlockIndex L → ℤ)
    (hcrt : ∀ d, (a d : ℝ) * (d.val : ℝ) + (b d : ℝ) * (p : ℝ) =
      1 + (t d : ℝ) * (p : ℝ) * (d.val : ℝ)) :
    extendedOldStage L p ⊔ Submodule.span ℝ
      (Set.range (fun d : BlockIndex L => qCarry p d.val (a d) (b d))) =
        QSquarefreeLatticePackets.divisorStage (p * L) := by
  rw [qCarry_family_eq_fullBlock L p a b t hp.pos hcrt]
  exact full_prime_block_stage L p hL hp _ _

/-- The existing complete trace estimate applies to literal floor vectors. -/
theorem literal_complete_trace_bound {ι : Type*} [Fintype ι]
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (p : ℕ) (d : ι → ℕ) (a b t : ι → ℤ)
    (hpV : qResidue p ∈ V) (hdV : ∀ i, qResidue (d i) ∈ V)
    (hp2 : 2 ≤ p) (hd2 : ∀ i, 2 ≤ d i)
    (hcrt : ∀ i, (a i : ℝ) * (d i : ℝ) + (b i : ℝ) * (p : ℝ) =
      1 + (t i : ℝ) * (p : ℝ) * (d i : ℝ)) :
    (∑ i, ‖RiemannResearch.Analysis.ScreenedCarry.screen V
      (qCarry p (d i) (a i) (b i))‖ ^ 2) ≤
      (2 / (zetaTwo * (p : ℝ))) * ∑ i, 1 / (d i : ℝ) := by
  have hi : ∀ i, qCarry p (d i) (a i) (b i) =
      pairVector p (d i) (a i : ℝ) (b i : ℝ) := fun i =>
    qCarry_eq_pairVector p (d i) (a i) (b i) (t i) (by omega)
      (by have := hd2 i; omega) (hcrt i)
  simp_rw [hi]
  change (∑ i, ‖QCarryScreenedBlock.screen V
      (pairVector p (d i) (a i : ℝ) (b i : ℝ))‖ ^ 2) ≤ _
  exact complete_trace_bound V p d (fun i => (a i : ℝ)) (fun i => (b i : ℝ))
    hpV hdV hp2 hd2

end RiemannResearch.RH.QCRTCarryBlockBridge

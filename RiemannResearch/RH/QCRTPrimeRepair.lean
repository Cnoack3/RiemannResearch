/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFreshDilationObstruction
import RiemannResearch.RH.QCRTGramMinimizer
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QFloorDilation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Tactic.NormNum

/-!
# A prime repair that changes the old divisor charge

Source: the user's exact-head energy handoff, Section 9.B, 28 October 2026,
and the finite-charge obstruction established in QFreshDilationObstruction.
The construction is developed in this continuation using the existing
missing-prime value theorem and compensated-residue head identity.

For a prime p not dividing L, an old exact head through p-1 forces f(p)=2.
The floor-dilation subtraction repairs that coordinate. Adding its dilation
to g_p-(L/p)g_L gives a nonzero zero-head direction through p; optimizing
along it gives an explicit legal candidate and the full signed energy.

This is one finite repair. Iteration across all head coordinates and a
uniform complete-Q energy estimate remain open, including the costs
at intervening composite coordinates.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTPrimeRepair
open ZetaTwoHilbert ZetaTwoProbability QFloorDilation QSquarefreeLatticePackets
open QFreshDilationObstruction

def repairBase (f : QHilbert) (p : ℕ) (hp : 0 < p) : QHilbert :=
  f - floorDilation p hp f

def repairDirection (f : QHilbert) (p L : ℕ) (hp : 0 < p) : QHilbert :=
  floorDilation p hp f + compensatedResidue p L

def primeRepair (f : QHilbert) (p L : ℕ) (hp : 0 < p) : QHilbert :=
  repairBase f p hp -
    (inner ℝ (repairBase f p hp) (repairDirection f p L hp) /
      ‖repairDirection f p L hp‖ ^ 2) • repairDirection f p L hp

theorem repairDirection_charge (f : QHilbert) (p L : ℕ) (hp : 0 < p)
    (hL : 0 < L) (hnot : ¬p ∣ L) :
    cutFunctional L (repairDirection f p L hp) = 1 / (p : ℝ) := by
  rw [repairDirection, map_add, cutFunctional_floorDilation L p hL hp hnot,
    cutFunctional_compensatedResidue L p hL hp hnot, zero_add]

theorem repairDirection_ne_zero (f : QHilbert) (p L : ℕ) (hp : 0 < p)
    (hL : 0 < L) (hnot : ¬p ∣ L) : repairDirection f p L hp ≠ 0 := by
  intro hz
  have he := repairDirection_charge f p L hp hL hnot
  rw [hz, map_zero] at he
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  exact (one_div_ne_zero hpR) he.symm

private theorem dilation_head (f : QHilbert) (p n : ℕ) (hp : 0 < p)
    (hnp : n < p) : qSequence (floorDilation p hp f) n = 0 := by
  rw [floorDilation_sequence]
  simp only [Nat.div_eq_of_lt hnp, qSequence_zero]

theorem repairBase_head (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hnot : ¬p ∣ L) (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n < p → qSequence f n = 1)
    (n : ℕ) (hn : 0 < n) (hnp : n ≤ p) :
    qSequence (repairBase f p hp.pos) n = 1 := by
  change qSequenceLinear (f - floorDilation p hp.pos f) n = 1
  simp only [map_sub, Pi.sub_apply]
  change qSequence f n - qSequence (floorDilation p hp.pos f) n = 1
  by_cases he : n = p
  · subst n
    rw [QCRTGramMinimizer.missing_prime_value L p hL hp hnot f hf hh,
      floorDilation_sequence]
    dsimp only
    rw [Nat.div_self hp.pos, hh 1 (by omega) hp.one_lt]
    norm_num
  · rw [hh n hn (by omega), dilation_head f p n hp.pos (by omega), sub_zero]

theorem repairDirection_head (L p : ℕ) (hp : 0 < p) (hpL : p < L)
    (f : QHilbert) (hf1 : qSequence f 1 = 1)
    (n : ℕ) (hn : 0 < n) (hnp : n ≤ p) :
    qSequence (repairDirection f p L hp) n = 0 := by
  change qSequenceLinear (floorDilation p hp f + compensatedResidue p L) n = 0
  simp only [map_add, Pi.add_apply]
  change qSequence (floorDilation p hp f) n + qSequence (compensatedResidue p L) n = 0
  by_cases he : n = p
  · subst n
    rw [floorDilation_sequence]
    dsimp only
    rw [Nat.div_self hp, hf1,
      QSquarefreeHeadStep.compensatedResidue_next p p L hp le_rfl hpL]
    norm_num
  · rw [dilation_head f p n hp (by omega),
      compensatedResidue_head p L n hp (by omega) (by omega) (by omega)]
    ring

theorem primeRepair_head (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hpL : p < L) (hnot : ¬p ∣ L) (f : QHilbert) (hf : f ∈ divisorStage L)
    (hh : ∀ n, 0 < n → n < p → qSequence f n = 1)
    (n : ℕ) (hn : 0 < n) (hnp : n ≤ p) :
    qSequence (primeRepair f p L hp.pos) n = 1 := by
  change qSequenceLinear (_ - _ • _) n = 1
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (repairBase f p hp.pos) n - _ *
    qSequence (repairDirection f p L hp.pos) n = 1
  rw [repairBase_head L p hL hp hnot f hf hh n hn hnp,
    repairDirection_head L p hp.pos hpL f (hh 1 (by omega) hp.one_lt) n hn hnp]
  ring

theorem primeRepair_mem_stage (L p : ℕ) (hL : 0 < L) (hp : 0 < p)
    (f : QHilbert) (hf : f ∈ divisorStage L) :
    primeRepair f p L hp ∈ divisorStage (p * L) := by
  have hbase : f ∈ divisorStage (p * L) :=
    divisorStage_mono (dvd_mul_left L p) hf
  have hu := floorDilation_mem_divisorStage L p hL hp f hf
  have hres : compensatedResidue p L ∈ divisorStage (p * L) := by
    exact (divisorStage (p * L)).sub_mem
      (Submodule.subset_span ⟨p, dvd_mul_right p L, rfl⟩)
      ((divisorStage (p * L)).smul_mem _
        (Submodule.subset_span ⟨L, dvd_mul_left L p, rfl⟩))
  exact (divisorStage (p * L)).sub_mem
    ((divisorStage (p * L)).sub_mem hbase hu)
    ((divisorStage (p * L)).smul_mem _
      ((divisorStage (p * L)).add_mem hu hres))

theorem primeRepair_legal (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hLs : Squarefree L) (hnot : ¬p ∣ L) (f : QHilbert) (hf : f ∈ divisorStage L) :
    primeRepair f p L hp.pos ∈ qSquarefreeCRTSpan := by
  exact divisorStage_le_squarefreeSpan _ (Nat.mul_pos hp.pos hL)
    (Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hnot, hp.squarefree, hLs⟩)
    (primeRepair_mem_stage L p hL hp.pos f hf)

/-- Complete signed energy of the charge-changing prime repair. -/
theorem primeRepair_energy (f : QHilbert) (p L : ℕ) (hp : 0 < p)
    (hL : 0 < L) (hnot : ¬p ∣ L) :
    ‖primeRepair f p L hp‖ ^ 2 =
      ‖f‖ ^ 2 - 2 * inner ℝ f (floorDilation p hp f) +
        ‖floorDilation p hp f‖ ^ 2 -
        (inner ℝ (repairBase f p hp) (repairDirection f p L hp)) ^ 2 /
          ‖repairDirection f p L hp‖ ^ 2 := by
  have hD : ‖repairDirection f p L hp‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (repairDirection_ne_zero f p L hp hL hnot))
  rw [primeRepair, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  have he : ‖repairBase f p hp‖ ^ 2 =
      ‖f‖ ^ 2 - 2 * inner ℝ f (floorDilation p hp f) +
        ‖floorDilation p hp f‖ ^ 2 := norm_sub_sq_real f (floorDilation p hp f)
  rw [he]
  field_simp [hD]
  ring

end RiemannResearch.RH.QCRTPrimeRepair

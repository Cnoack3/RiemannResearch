/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import RiemannResearch.Analysis.FiniteCellSampling
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual prime-phase bins and their unique finite CRT code

Source: the user-directed prime-phase proposal, 21 October 2026.
The construction uses Mathlib finite CRT. It is unconditional
finite arithmetic. Joint phase-cell frequencies remain explicit hypotheses.
The fractional-part convention uses half-open cells, including phase zero.
-/
noncomputable section
open scoped BigOperators Topology Function
open Filter

namespace RiemannResearch.Analysis.PrimePhaseCRTCells

open FiniteCellSampling

def phaseFraction (p : ℕ) (t : ℝ) : ℝ :=
  Int.fract (Real.log p / (2 * Real.pi) * t)

def phaseBinNat (p : ℕ) (t : ℝ) : ℕ :=
  ⌊(p : ℝ) * phaseFraction p t⌋₊

theorem phaseBinNat_lt (p : ℕ) (hp : 0 < p) (t : ℝ) :
    phaseBinNat p t < p := by
  apply (Nat.floor_lt' (ne_of_gt hp)).mpr
  have h := Int.fract_lt_one (Real.log p / (2 * Real.pi) * t)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  change (p : ℝ) * phaseFraction p t < (p : ℝ)
  unfold phaseFraction
  nlinarith

def phaseBin (p : ℕ) (hp : 0 < p) (t : ℝ) : Fin p :=
  ⟨phaseBinNat p t, phaseBinNat_lt p hp t⟩

def primeProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

theorem primeProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < primeProduct P := by
  exact Finset.prod_pos (fun p hp => (hP p hp).pos)

theorem prime_pairwise (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.Pairwise (↑P : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq

def phaseCode (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    Fin (primeProduct P) :=
  ⟨Nat.chineseRemainderOfFinset (fun p => phaseBinNat p t) id P
      (fun p hp => (hP p hp).ne_zero) (prime_pairwise P hP),
    Nat.chineseRemainderOfFinset_lt_prod (fun p => phaseBinNat p t) id
      (fun p hp => (hP p hp).ne_zero) (prime_pairwise P hP)⟩

theorem phaseCode_modEq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (p : ℕ) (hp : p ∈ P) :
    (phaseCode P hP t).val ≡ phaseBinNat p t [MOD p] :=
  (Nat.chineseRemainderOfFinset (fun p => phaseBinNat p t) id P
    (fun p hp => (hP p hp).ne_zero) (prime_pairwise P hP)).property p hp

theorem phaseCode_unique (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (r : Fin (primeProduct P))
    (hr : ∀ p ∈ P, r.val ≡ phaseBinNat p t [MOD p]) :
    r = phaseCode P hP t := by
  have hlist : P.toList.Pairwise (Nat.Coprime on (id : ℕ → ℕ)) := by
    apply List.Nodup.pairwise_of_forall_ne P.nodup_toList
    intro p hp q hq hpq
    exact prime_pairwise P hP (Finset.mem_toList.mp hp)
      (Finset.mem_toList.mp hq) hpq
  have hmod : r.val ≡ (phaseCode P hP t).val [MOD primeProduct P] := by
    have h := (Nat.modEq_list_map_prod_iff hlist).2
      (fun p hp => (hr p (Finset.mem_toList.mp hp)).trans
        (phaseCode_modEq P hP t p (Finset.mem_toList.mp hp)).symm)
    simpa [primeProduct] using h
  exact Fin.ext (hmod.eq_of_lt_of_lt r.isLt (phaseCode P hP t).isLt)

theorem phaseCode_eq_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (r : Fin (primeProduct P)) :
    phaseCode P hP t = r ↔
      ∀ p ∈ P, phaseBinNat p t = r.val % p := by
  constructor
  · intro he p hp
    have hm := phaseCode_modEq P hP t p hp
    rw [he] at hm
    have hb := phaseBinNat_lt p (hP p hp).pos t
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb] using hm.symm
  · intro h
    symm
    apply phaseCode_unique P hP t r
    intro p hp
    change r.val % p = phaseBinNat p t % p
    rw [Nat.mod_eq_of_lt (phaseBinNat_lt p (hP p hp).pos t)]
    exact (h p hp).symm

/-- Exact joint half-open cell frequency, indexed by its CRT residue. -/
def jointCellFrequency {κ : Type*} (s : Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (r : Fin (primeProduct P)) : ℝ :=
  (∑ j ∈ s, if ∀ p ∈ P, phaseBinNat p (times j) = r.val % p
    then (1 : ℝ) else 0) / (s.card : ℝ)

theorem phaseCode_cellFrequency {κ : Type*}
    (s : Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : Fin (primeProduct P)) :
    cellFrequency s (fun j => phaseCode P hP (times j)) r =
      jointCellFrequency s times P r := by
  unfold cellFrequency jointCellFrequency
  simp only [phaseCode_eq_iff]

theorem phaseCode_frequency_tendsto {κ : Type*}
    (s : ℕ → Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hcell : ∀ r, Tendsto (fun n => jointCellFrequency (s n) times P r)
      atTop (𝓝 (1 / (primeProduct P : ℝ)))) (r : Fin (primeProduct P)) :
    Tendsto (fun n => cellFrequency (s n)
      (fun j => phaseCode P hP (times j)) r)
      atTop (𝓝 (1 / (primeProduct P : ℝ))) := by
  simpa only [phaseCode_cellFrequency] using hcell r

/-- Rotating a positive-block index recovers its physical residue. -/
theorem finRotate_val_mod (L : ℕ) (a : Fin L) :
    (finRotate L a).val = (a.val + 1) % L := by
  cases L with
  | zero => exact a.elim0
  | succ n =>
    by_cases h : a = Fin.last n
    · simp [h]
    · have hne : a.val ≠ n := by
        intro he
        apply h
        exact Fin.ext he
      have hlt : a.val + 1 < n + 1 := by
        have := a.isLt
        omega
      simp [h, Fin.val_add_one, Nat.mod_eq_of_lt hlt]

/-- Raw residue zero represents the positive integer L, so the Q-law index
is the inverse rotation of the raw CRT residue. -/
def positivePhaseCode (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    Fin (primeProduct P) :=
  (finRotate (primeProduct P)).symm (phaseCode P hP t)

/-- The positive physical representative and the raw CRT code agree modulo L. -/
theorem positivePhaseCode_modEq (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) :
    (positivePhaseCode P hP t).val + 1 ≡ (phaseCode P hP t).val
      [MOD primeProduct P] := by
  have h := congrArg Fin.val
    ((finRotate (primeProduct P)).apply_symm_apply (phaseCode P hP t))
  rw [finRotate_val_mod] at h
  change ((positivePhaseCode P hP t).val + 1) % primeProduct P =
    (phaseCode P hP t).val % primeProduct P
  rw [Nat.mod_eq_of_lt (phaseCode P hP t).isLt]
  exact h

/-- The Q-law representative has exactly the requested prime bin residues. -/
theorem positivePhaseCode_prime_mod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (p : ℕ) (hp : p ∈ P) :
    ((positivePhaseCode P hP t).val + 1) % p = phaseBinNat p t := by
  have hd : p ∣ primeProduct P := Finset.dvd_prod_of_mem id hp
  have hm := (Nat.ModEq.of_dvd hd (positivePhaseCode_modEq P hP t)).trans
    (phaseCode_modEq P hP t p hp)
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (phaseBinNat_lt p (hP p hp).pos t)]
    using hm

/-- Rotating the CRT labels transfers joint cell frequencies to the indices
used by the positive block formula for the complete Q inner product. -/
theorem positivePhaseCode_frequency_tendsto {κ : Type*}
    (s : ℕ → Finset κ) (times : κ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hcell : ∀ r, Tendsto (fun n => jointCellFrequency (s n) times P r)
      atTop (𝓝 (1 / (primeProduct P : ℝ)))) (a : Fin (primeProduct P)) :
    Tendsto (fun n => cellFrequency (s n)
      (fun j => positivePhaseCode P hP (times j)) a)
      atTop (𝓝 (1 / (primeProduct P : ℝ))) := by
  simpa only [positivePhaseCode, cellFrequency_equiv, Equiv.symm_symm] using
    phaseCode_frequency_tendsto s times P hP hcell (finRotate (primeProduct P) a)

end RiemannResearch.Analysis.PrimePhaseCRTCells

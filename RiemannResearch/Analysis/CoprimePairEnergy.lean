/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact energy identities for pairs with a shared coordinate

Source: direct finite square completion for the user-directed rational-tail
investigation, 21 October 2026.

The identities retain every square. Their application to coprime residual jumps
requires a separate accounting of the selected sites in the full energy.
-/

noncomputable section
namespace RiemannResearch.Analysis.CoprimePairEnergy

open scoped BigOperators

def pairConductance (a b : ℝ) : ℝ := a * b / (a + b)

def conductanceSum {ι : Type*} (s : Finset ι) (a b : ι → ℝ) : ℝ :=
  ∑ q ∈ s, pairConductance (a q) (b q)

def effectiveEnergy (w A : ℝ) : ℝ := w * A / (w + A)

theorem pairConductance_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ pairConductance a b :=
  div_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)

theorem pairConductance_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < pairConductance a b :=
  div_pos (mul_pos ha hb) (add_pos ha hb)

theorem conductanceSum_nonneg {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ q ∈ s, 0 ≤ a q) (hb : ∀ q ∈ s, 0 ≤ b q) :
    0 ≤ conductanceSum s a b := by
  exact Finset.sum_nonneg fun q hq => pairConductance_nonneg (ha q hq) (hb q hq)

theorem pair_square_identity (a b u v : ℝ) (hab : a + b ≠ 0) :
    a * u ^ 2 + b * v ^ 2 - pairConductance a b * (u - v) ^ 2 =
      (a * u + b * v) ^ 2 / (a + b) := by
  unfold pairConductance
  field_simp [hab]
  ring

theorem shared_square_identity (w A x : ℝ) (hwA : w + A ≠ 0) :
    w * x ^ 2 + A * (1 - x) ^ 2 - effectiveEnergy w A =
      ((w + A) * x - A) ^ 2 / (w + A) := by
  unfold effectiveEnergy
  field_simp [hwA]
  ring

/-- Exact finite-sum completion of squares for pairs coupled through `x`. -/
theorem shared_pair_energy_gap {ι : Type*} (s : Finset ι)
    (a b u v : ι → ℝ) (w x : ℝ)
    (hab : ∀ q ∈ s, a q + b q ≠ 0)
    (hrel : ∀ q ∈ s, x + u q - v q = 1)
    (hwA : w + conductanceSum s a b ≠ 0) :
    w * x ^ 2 + (∑ q ∈ s, (a q * u q ^ 2 + b q * v q ^ 2)) -
        effectiveEnergy w (conductanceSum s a b) =
      ((w + conductanceSum s a b) * x - conductanceSum s a b) ^ 2 /
          (w + conductanceSum s a b) +
        ∑ q ∈ s, (a q * u q + b q * v q) ^ 2 / (a q + b q) := by
  have hpairs :
      (∑ q ∈ s, (a q * u q ^ 2 + b q * v q ^ 2)) =
        conductanceSum s a b * (1 - x) ^ 2 +
          ∑ q ∈ s, (a q * u q + b q * v q) ^ 2 / (a q + b q) := by
    calc
      (∑ q ∈ s, (a q * u q ^ 2 + b q * v q ^ 2)) =
          ∑ q ∈ s, (pairConductance (a q) (b q) * (1 - x) ^ 2 +
            (a q * u q + b q * v q) ^ 2 / (a q + b q)) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hj := pair_square_identity (a q) (b q) (u q) (v q) (hab q hq)
        have hdiff : u q - v q = 1 - x := by linarith [hrel q hq]
        rw [hdiff] at hj
        linarith
      _ = conductanceSum s a b * (1 - x) ^ 2 +
          ∑ q ∈ s, (a q * u q + b q * v q) ^ 2 / (a q + b q) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        rfl
  have hshared := shared_square_identity w (conductanceSum s a b) x hwA
  rw [hpairs]
  linarith

/-- The common-coordinate energy bound, with strictly positive weights. -/
theorem shared_pair_energy_lower {ι : Type*} (s : Finset ι)
    (a b u v : ι → ℝ) (w x : ℝ)
    (hw : 0 < w) (ha : ∀ q ∈ s, 0 < a q) (hb : ∀ q ∈ s, 0 < b q)
    (hrel : ∀ q ∈ s, x + u q - v q = 1) :
    effectiveEnergy w (conductanceSum s a b) ≤
      w * x ^ 2 + ∑ q ∈ s, (a q * u q ^ 2 + b q * v q ^ 2) := by
  have hA := conductanceSum_nonneg s a b
    (fun q hq => le_of_lt (ha q hq)) (fun q hq => le_of_lt (hb q hq))
  have hwA : 0 < w + conductanceSum s a b := add_pos_of_pos_of_nonneg hw hA
  have hgap := shared_pair_energy_gap s a b u v w x
    (fun q hq => ne_of_gt (add_pos (ha q hq) (hb q hq))) hrel (ne_of_gt hwA)
  have hshared : 0 ≤
      ((w + conductanceSum s a b) * x - conductanceSum s a b) ^ 2 /
        (w + conductanceSum s a b) :=
    div_nonneg (sq_nonneg _) (le_of_lt hwA)
  have hpairs : 0 ≤ ∑ q ∈ s,
      (a q * u q + b q * v q) ^ 2 / (a q + b q) := by
    apply Finset.sum_nonneg
    intro q hq
    exact div_nonneg (sq_nonneg _) (le_of_lt (add_pos (ha q hq) (hb q hq)))
  linarith

/-- Exact improvement when the total selected conductance increases. -/
theorem effectiveEnergy_sub (w A B : ℝ)
    (hwA : w + A ≠ 0) (hwB : w + B ≠ 0) :
    effectiveEnergy w A - effectiveEnergy w B =
      w ^ 2 * (A - B) / ((w + A) * (w + B)) := by
  unfold effectiveEnergy
  field_simp [hwA, hwB]
  ring

theorem effectiveEnergy_strict_mono {w A B : ℝ}
    (hw : 0 < w) (hB : 0 ≤ B) (hBA : B < A) :
    effectiveEnergy w B < effectiveEnergy w A := by
  have hA : 0 ≤ A := le_trans hB (le_of_lt hBA)
  have hwA : 0 < w + A := add_pos_of_pos_of_nonneg hw hA
  have hwB : 0 < w + B := add_pos_of_pos_of_nonneg hw hB
  apply sub_pos.mp
  rw [effectiveEnergy_sub w A B (ne_of_gt hwA) (ne_of_gt hwB)]
  exact div_pos (mul_pos (sq_pos_of_pos hw) (sub_pos.mpr hBA)) (mul_pos hwA hwB)

/-- A second positive pair makes the total conductance strictly larger. -/
theorem pairConductance_lt_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (q : ι) (hq : q ∈ s)
    (ha : ∀ p ∈ s, 0 < a p) (hb : ∀ p ∈ s, 0 < b p)
    (hother : ∃ p ∈ s, p ≠ q) :
    pairConductance (a q) (b q) < conductanceSum s a b := by
  classical
  obtain ⟨p, hp, hpq⟩ := hother
  have hp' : p ∈ s.erase q := by simp only [Finset.mem_erase]; exact ⟨hpq, hp⟩
  have hpos : 0 < ∑ i ∈ s.erase q, pairConductance (a i) (b i) := by
    apply Finset.sum_pos'
    · intro i hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      exact le_of_lt (pairConductance_pos (ha i his) (hb i his))
    · exact ⟨p, hp', pairConductance_pos (ha p hp) (hb p hp)⟩
  have hsum := Finset.add_sum_erase s (fun i => pairConductance (a i) (b i)) hq
  unfold conductanceSum
  linarith

/-- With a second selected pair, the bound improves every selected single pair. -/
theorem shared_bound_strictly_improves_single {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (w : ℝ) (q : ι) (hq : q ∈ s)
    (hw : 0 < w) (ha : ∀ p ∈ s, 0 < a p) (hb : ∀ p ∈ s, 0 < b p)
    (hother : ∃ p ∈ s, p ≠ q) :
    effectiveEnergy w (pairConductance (a q) (b q)) <
      effectiveEnergy w (conductanceSum s a b) := by
  exact effectiveEnergy_strict_mono hw
    (le_of_lt (pairConductance_pos (ha q hq) (hb q hq)))
    (pairConductance_lt_sum s a b q hq ha hb hother)

end RiemannResearch.Analysis.CoprimePairEnergy

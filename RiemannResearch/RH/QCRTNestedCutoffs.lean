/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTFiniteCollocation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact canonical updates at nested CRT cutoffs


Source: continuation of the user's CRT collocation construction. These are
exact identities for the complete-Q canonical vectors; they do not posit
orthogonality of successive leakage increments. The visible target increment
has a telescoping norm, but its uncontrolled leakage increment remains.
-/
noncomputable section
namespace RiemannResearch.RH.QCRTNestedCutoffs
open ZetaTwoHilbert QDivisibilityDensity QCRTFiniteCollocation

/-- Divisibility of cutoffs nests their actual legal divisor spans. -/
theorem trialSpace_mono_of_dvd (L M : ℕ) (hM : 0 < M) (hLM : L ∣ M) :
    trialSpace L ≤ trialSpace M := by
  apply Submodule.span_le.mpr
  rintro g ⟨d, hd, rfl⟩
  exact residue_mem_trial M d hM ((Nat.dvd_of_mem_divisors hd).trans hLM)

/-- Divisibility of cutoffs also nests their gcd-cell spaces. -/
theorem cellSpace_mono_of_dvd (L M : ℕ) (hM : 0 < M) (hLM : L ∣ M) :
    cellSpace L ≤ cellSpace M := by
  apply Submodule.span_le.mpr
  rintro g ⟨d, hd, rfl⟩
  exact divisor_mem_cell M d hM ((Nat.dvd_of_mem_divisors hd).trans hLM)

/-- The actual signed canonical leakage vector. -/
def leakageVector (L : ℕ) (hL : 2 ≤ L) : QHilbert :=
  (canonical L hL : QHilbert) - target L

theorem leakageVector_norm_sq (L : ℕ) (hL : 2 ≤ L) :
    ‖leakageVector L hL‖^2 = leakage L hL := rfl

theorem leakageVector_inner_cell (L : ℕ) (hL : 2 ≤ L)
    (v : QHilbert) (hv : v ∈ cellSpace L) :
    inner ℝ (leakageVector L hL) v = 0 := by
  rw [leakageVector, inner_sub_left,
    ← conditional_inner L (canonical L hL) v hv,
    canonical_conditional L hL, sub_self]

/-- The old leakage is also orthogonal to multiples of every larger nested cutoff.
This uses legal-span nesting, not an assumed martingale property. -/
theorem leakageVector_inner_larger_divisor (L M : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (hLM : L ∣ M) :
    inner ℝ (leakageVector L hL) (qDivisor M) = 0 := by
  have hLp : 0 < L := by omega
  have htrial := trialSpace_mono_of_dvd L M hM hLM (canonical L hL).property
  rw [leakageVector, inner_sub_left, trial_inner_multiples M hM _ htrial]
  rw [target, inner_sub_left, qOne_inner_qDivisor M hM,
    qDivisor_inner_qDivisor L M hLp hM, Nat.lcm_eq_right hLM]
  ring

/-- The new canonical vector agrees with the old target off the old zero cell.
The exact old zero-cell value is 1-(L/M)^2. -/
theorem canonical_condition_earlier (L M : ℕ) (hL : 0 < L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    conditionalProjection L (canonical M hM) =
      qOne - ((L : ℝ)^2/(M : ℝ)^2) • qDivisor L := by
  apply conditional_eq_of_match L (canonical M hM)
    (qOne - ((L : ℝ)^2/(M : ℝ)^2) • qDivisor L)
  · exact (cellSpace L).sub_mem (qOne_mem_cell L hL)
      ((cellSpace L).smul_mem _ (divisor_mem_cell L L hL (dvd_refl L)))
  intro d hdmem
  have hdL := Nat.dvd_of_mem_divisors hdmem
  have hdp := Nat.pos_of_mem_divisors hdmem
  rw [canonical_divisor_moment M hM d hdp (hdL.trans hLM),
    inner_sub_left, real_inner_smul_left, qOne_inner_qDivisor d hdp,
    qDivisor_inner_qDivisor L d hL hdp, Nat.lcm_eq_left hdL]
  have hLR : (L : ℝ) ≠ 0 := by positivity
  have hMR : (M : ℝ) ≠ 0 := by positivity
  field_simp [hLR, hMR]

/-- The change visible to the old cells is supported only on their multiples cell. -/
theorem canonical_increment_condition_earlier (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    conditionalProjection L ((canonical M hM : QHilbert) - canonical L hL) =
      (1 - (L : ℝ)^2/(M : ℝ)^2) • qDivisor L := by
  rw [map_sub, canonical_condition_earlier L M (by omega) hM hLM,
    canonical_conditional L hL, target]
  rw [sub_smul, one_smul]
  abel

/-- Old leakage is orthogonal to the newer target because both vanish on
multiples of the old cutoff, while its Q mean is zero. -/
theorem leakageVector_inner_larger_target (L M : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (hLM : L ∣ M) :
    inner ℝ (leakageVector L hL) (target M) = 0 := by
  rw [target, inner_sub_right,
    leakageVector_inner_cell L hL qOne (qOne_mem_cell L (by omega)),
    leakageVector_inner_larger_divisor L M hL hM hLM, sub_self]

/-- New leakage is orthogonal to the older target by cell-space nesting. -/
theorem leakageVector_inner_smaller_target (L M : ℕ) (hL : 0 < L)
    (hM : 2 ≤ M) (hLM : L ∣ M) :
    inner ℝ (leakageVector M hM) (target L) = 0 := by
  exact leakageVector_inner_cell M hM (target L)
    (cellSpace_mono_of_dvd L M (by omega) hLM (target_mem_cell L hL))

/-- The visible target increments have exact telescoping energies. -/
theorem target_increment_norm_sq (L M : ℕ) (hL : 0 < L) (hM : 0 < M)
    (hLM : L ∣ M) :
    ‖target M - target L‖^2 = 1/(L : ℝ)^2 - 1/(M : ℝ)^2 := by
  have he : target M - target L = qDivisor L - qDivisor M := by
    unfold target
    abel
  rw [he, norm_sub_sq_real, qDivisor_norm_sq L hL, qDivisor_norm_sq M hM,
    qDivisor_inner_qDivisor L M hL hM, Nat.lcm_eq_right hLM]
  ring

/-- Orthogonal decomposition of an actual canonical increment into the visible
target increment and the full, retained leakage increment. -/
theorem canonical_increment_norm_sq (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    ‖(canonical M hM : QHilbert) - canonical L hL‖^2 =
      (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
        ‖leakageVector M hM - leakageVector L hL‖^2 := by
  have hLself := leakageVector_inner_cell L hL (target L) (target_mem_cell L (by omega))
  have hMself := leakageVector_inner_cell M hM (target M) (target_mem_cell M (by omega))
  have hLlarge := leakageVector_inner_larger_target L M hL (by omega) hLM
  have hMsmall := leakageVector_inner_smaller_target L M (by omega) hM hLM
  have ho : inner ℝ (leakageVector M hM - leakageVector L hL)
      (target M - target L) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      hMself, hMsmall, hLlarge, hLself]
    ring
  have he : (canonical M hM : QHilbert) - canonical L hL =
      (target M - target L) + (leakageVector M hM - leakageVector L hL) := by
    unfold leakageVector
    abel
  have ho' : inner ℝ (target M - target L)
      (leakageVector M hM - leakageVector L hL) = 0 :=
    (real_inner_comm (target M - target L)
      (leakageVector M hM - leakageVector L hL)).symm.trans ho
  rw [he, norm_add_sq_real, ho',
    target_increment_norm_sq L M (by omega) (by omega) hLM]
  ring

/-- Expanded update: the leakage cross term is explicitly retained.
There is no claim that the canonical leakage vectors are mutually orthogonal. -/
theorem canonical_increment_norm_sq_expanded (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    ‖(canonical M hM : QHilbert) - canonical L hL‖^2 =
      1/(L : ℝ)^2 - 1/(M : ℝ)^2 + leakage M hM + leakage L hL -
        2 * inner ℝ (leakageVector M hM) (leakageVector L hL) := by
  rw [canonical_increment_norm_sq L M hL hM hLM, norm_sub_sq_real,
    leakageVector_norm_sq, leakageVector_norm_sq]
  ring

/-- The old visible target energy is preserved in the nested cross pairing;
all remaining correlation is exactly leakage correlation. -/
theorem canonical_inner_nested (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    inner ℝ (canonical M hM : QHilbert) (canonical L hL : QHilbert) =
      1 - 1/(L : ℝ)^2 +
        inner ℝ (leakageVector M hM) (leakageVector L hL) := by
  have he := canonical_increment_norm_sq_expanded L M hL hM hLM
  rw [norm_sub_sq_real, canonical_norm M hM, canonical_norm L hL] at he
  linarith

end RiemannResearch.RH.QCRTNestedCutoffs

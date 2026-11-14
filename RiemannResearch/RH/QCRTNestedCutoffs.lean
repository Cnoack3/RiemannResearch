/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.NormNum
import RiemannResearch.Analysis.OrthogonalRefinementEnergy
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.Analysis.FiniteAccretiveCollocation
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
open scoped BigOperators
namespace RiemannResearch.RH.QCRTNestedCutoffs
open ZetaTwoHilbert QDivisibilityDensity QCRTFiniteCollocation QPhysicalDifference
open ZetaTwoProbability

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

/-- Exact change of canonical energy, including its signed leakage correlation.
This algebraic identity does not require nested conductors. -/
theorem canonical_norm_growth_exact (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) :
    ‖(canonical M hM : QHilbert)‖^2 - ‖(canonical L hL : QHilbert)‖^2 =
      (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
      ‖leakageVector M hM - leakageVector L hL‖^2 +
      2 * inner ℝ (leakageVector L hL)
        (leakageVector M hM - leakageVector L hL) := by
  rw [canonical_norm M hM, canonical_norm L hL, norm_sub_sq_real,
    inner_sub_right, real_inner_self_eq_norm_sq,
    leakageVector_norm_sq, leakageVector_norm_sq,
    real_inner_comm (leakageVector L hL) (leakageVector M hM)]
  ring

/-- The proposed multiplicative budget is precisely this signed inequality.
Neither side of the equivalence is asserted unconditionally. -/
theorem canonical_update_budget_iff (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (b : ℝ) :
    ‖(canonical M hM : QHilbert)‖^2 ≤ (1+b)*‖(canonical L hL : QHilbert)‖^2 ↔
      (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
      ‖leakageVector M hM - leakageVector L hL‖^2 +
      2 * inner ℝ (leakageVector L hL)
        (leakageVector M hM - leakageVector L hL) ≤
      b * ‖(canonical L hL : QHilbert)‖^2 := by
  have h := canonical_norm_growth_exact L M hL hM
  constructor <;> intro hh <;> nlinarith

/-- The full new-cell source of the canonical update. -/
def updateSource (L M : ℕ) (hL : 2 ≤ L) : QHilbert :=
  target M - conditionalProjection M (canonical L hL)

/-- The actual finer-cell right-hand side of the canonical update. -/
theorem canonical_increment_conditional (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) :
    conditionalProjection M ((canonical M hM : QHilbert) - canonical L hL) =
      updateSource L M hL := by
  rw [map_sub, canonical_conditional, updateSource]

/-- The new target and the old leakage revealed by the finer partition. -/
theorem updateSource_eq (L M : ℕ) (hL : 2 ≤ L) (hM : 0 < M) (hLM : L ∣ M) :
    updateSource L M hL = (target M - target L) -
      conditionalProjection M (leakageVector L hL) := by
  have ht : conditionalProjection M (target L) = target L :=
    Submodule.starProjection_eq_self_iff.mpr
      (cellSpace_mono_of_dvd L M hM hLM (target_mem_cell L (by omega)))
  rw [updateSource, leakageVector, map_sub, ht]
  abel

/-- The visible source energy retains the complete newly revealed leakage. -/
theorem updateSource_norm_sq (L M : ℕ) (hL : 2 ≤ L) (hM : 0 < M) (hLM : L ∣ M) :
    ‖updateSource L M hL‖^2 = (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
      ‖conditionalProjection M (leakageVector L hL)‖^2 := by
  have hv : target M - target L ∈ cellSpace M := (cellSpace M).sub_mem
    (target_mem_cell M hM)
    (cellSpace_mono_of_dvd L M hM hLM (target_mem_cell L (by omega)))
  have ho : inner ℝ (conditionalProjection M (leakageVector L hL))
      (target M - target L) = 0 := by
    rw [conditional_inner M _ _ hv, inner_sub_right,
      leakageVector_inner_larger_target L M hL hM hLM,
      leakageVector_inner_cell L hL (target L) (target_mem_cell L (by omega))]
    ring
  have ho' : inner ℝ (target M - target L)
      (conditionalProjection M (leakageVector L hL)) = 0 :=
    (real_inner_comm _ _).trans ho
  rw [updateSource_eq L M hL hM hLM, norm_sub_sq_real, ho',
    target_increment_norm_sq L M (by omega) hM hLM]
  ring

/-- Exact divisor moments of the target increment, including its LCM boundary. -/
theorem target_increment_divisor_moment (L M d : ℕ) (hL : 0 < L) (hM : 0 < M)
    (hd : 0 < d) (hdM : d ∣ M) :
    inner ℝ (target M - target L) (qDivisor d) =
      1/(Nat.lcm L d : ℝ)^2 - 1/(M : ℝ)^2 := by
  rw [inner_sub_left, target, target, inner_sub_left, inner_sub_left,
    qOne_inner_qDivisor d hd, qDivisor_inner_qDivisor M d hM hd,
    qDivisor_inner_qDivisor L d hL hd, Nat.lcm_eq_left hdM]
  ring

/-- Full signed divisor source; no old-leakage moment is omitted. -/
theorem signed_divisor_update_source (L M d : ℕ) (hL : 2 ≤ L) (hM : 0 < M)
    (hd : 0 < d) (hdM : d ∣ M) :
    inner ℝ (target M - canonical L hL) (qDivisor d) =
      1/(Nat.lcm L d : ℝ)^2 - 1/(M : ℝ)^2 -
        inner ℝ (leakageVector L hL) (qDivisor d) := by
  have he : target M - (canonical L hL : QHilbert) =
      (target M - target L) - leakageVector L hL := by
    unfold leakageVector
    abel
  rw [he, inner_sub_left, target_increment_divisor_moment L M d (by omega) hM hd hdM]

/-- The mean of the full signed source is exactly the target energy increment. -/
theorem canonical_target_source_mean (L M : ℕ) (hL : 2 ≤ L) (hM : 0 < M) :
    inner ℝ (target M - canonical L hL) qOne =
      1/(L : ℝ)^2 - 1/(M : ℝ)^2 := by
  rw [inner_sub_left, canonical_mean, target, inner_sub_left,
    real_inner_self_eq_norm_sq, qOne_norm_sq,
    real_inner_comm qOne (qDivisor M), qOne_inner_qDivisor M hM]
  ring

/-- The source for the accretive difference-test system. -/
theorem signed_difference_update_source (L M d : ℕ) (hL : 2 ≤ L) (hM : 0 < M)
    (hd : 2 ≤ d) (hdM : d ∣ M) :
    inner ℝ (target M - canonical L hL) (differenceCLM (qResidue d)) =
      (1/(d : ℝ)) * (1/(L : ℝ)^2 - 1/(M : ℝ)^2) -
      (1/(Nat.lcm L d : ℝ)^2 - 1/(M : ℝ)^2) +
      inner ℝ (leakageVector L hL) (qDivisor d) := by
  rw [difference_residue d hd, inner_sub_right, inner_smul_right,
    canonical_target_source_mean L M hL hM,
    signed_divisor_update_source L M d hL hM (by omega) hdM]
  ring

/-- Old divisor columns have an explicit target-only source. -/
theorem signed_difference_update_source_old (L M d : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (hLM : L ∣ M) (hd : 2 ≤ d) (hdL : d ∣ L) :
    inner ℝ (target M - canonical L hL) (differenceCLM (qResidue d)) =
      (1/(d : ℝ)-1) * (1/(L : ℝ)^2 - 1/(M : ℝ)^2) := by
  rw [signed_difference_update_source L M d hL hM hd (hdL.trans hLM),
    Nat.lcm_eq_left hdL,
    leakageVector_inner_cell L hL (qDivisor d)
      (divisor_mem_cell L d (by omega) hdL)]
  ring

/-- For a newly admitted divisor with lcm(L,d)=M, its signed leakage remains.
At a prime-power admission M=pL this applies to every new divisor. -/
theorem signed_difference_update_source_new (L M d : ℕ) (hL : 2 ≤ L)
    (hM : 0 < M) (hd : 2 ≤ d) (hdM : d ∣ M) (hnew : Nat.lcm L d = M) :
    inner ℝ (target M - canonical L hL) (differenceCLM (qResidue d)) =
      (1/(d : ℝ)) * (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
      inner ℝ (leakageVector L hL) (qDivisor d) := by
  rw [signed_difference_update_source L M d hL hM hd hdM, hnew]
  ring

/-- The actual canonical increment solves the difference-test source equations. -/
theorem canonical_increment_difference_test (L M d : ℕ) (hL : 2 ≤ L)
    (hM : 2 ≤ M) (hdM : d ∣ M) :
    inner ℝ ((canonical M hM : QHilbert) - canonical L hL)
        (differenceCLM (qResidue d)) =
      inner ℝ (target M - canonical L hL) (differenceCLM (qResidue d)) := by
  rw [inner_sub_left, inner_sub_left,
    ← conditional_inner M (canonical M hM) _
      (difference_mem_cell M (by omega) _
        (residue_mem_trial M d (by omega) hdM)),
    canonical_conditional M hM]

/-- Exact contraction-defect identity for the actual update. This is not an
unweighted complete-Q norm bound: the shifted energy remains. -/
theorem canonical_increment_difference_energy (L M : ℕ)
    (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M) :
    ‖differenceCLM ((canonical M hM : QHilbert) - canonical L hL) -
        updateSource L M hL‖^2 +
      (‖(canonical M hM : QHilbert) - canonical L hL‖^2 -
        ‖physicalShift ((canonical M hM : QHilbert) - canonical L hL)‖^2) =
      (1/(L : ℝ)^2 - 1/(M : ℝ)^2) +
        ‖conditionalProjection M (leakageVector L hL)‖^2 := by
  have hf : (canonical M hM : QHilbert) - canonical L hL ∈ trialSpace M :=
    (trialSpace M).sub_mem (canonical M hM).property
      (trialSpace_mono_of_dvd L M (by omega) hLM (canonical L hL).property)
  have he :
      ‖differenceCLM ((canonical M hM : QHilbert) - canonical L hL) -
          updateSource L M hL‖^2 +
        (‖(canonical M hM : QHilbert) - canonical L hL‖^2 -
          ‖physicalShift ((canonical M hM : QHilbert) - canonical L hL)‖^2) =
        ‖updateSource L M hL‖^2 := by
    apply RiemannResearch.Analysis.FiniteAccretiveCollocation.matched_energy shiftCLM
    change inner ℝ ((canonical M hM : QHilbert) - canonical L hL)
        (differenceCLM ((canonical M hM : QHilbert) - canonical L hL)) = _
    rw [← conditional_inner M _ _ (difference_mem_cell M (by omega) _ hf),
      canonical_increment_conditional L M hL hM]
    rfl
  rw [he, updateSource_norm_sq L M hL (by omega) hLM]

/-- An unconditional raw divisor-source bound. Normalizing qDivisor d removes
the apparent inverse-square gain, so this is not an update-energy estimate. -/
theorem leakage_divisor_moment_sq_le (L d : ℕ) (hL : 2 ≤ L) (hd : 0 < d) :
    (inner ℝ (leakageVector L hL) (qDivisor d))^2 ≤
      leakage L hL / (d : ℝ)^2 := by
  have hb : |inner ℝ (leakageVector L hL) (qDivisor d)| ≤
      ‖leakageVector L hL‖ * ‖qDivisor d‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ) (leakageVector L hL) (qDivisor d)
  have hs : (inner ℝ (leakageVector L hL) (qDivisor d))^2 ≤
      (‖leakageVector L hL‖ * ‖qDivisor d‖)^2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using hb
  simpa only [mul_pow, leakageVector_norm_sq, qDivisor_norm_sq d hd, mul_one_div] using hs


/-!
## Finite raw-source bounds at prime-power admissions

Source: CanonicalPrimePowerUpdatesResearch20261107.md, Section 2, from the
user-provided canonical CRT argument. These bounds concern unnormalized rows;
the signed source and its exact row rescaling are retained explicitly.
-/

/-- The raw new difference-test row is bounded before any row normalization. -/
theorem signed_difference_update_source_new_sq_le
    (L M d : ℕ) (hL : 2 ≤ L) (hM : 0 < M) (hd : 2 ≤ d)
    (hdM : d ∣ M) (hnew : Nat.lcm L d = M) :
    (inner ℝ (target M - canonical L hL) (differenceCLM (qResidue d))) ^ 2 ≤
      2 * ((1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) ^ 2 + leakage L hL) /
        (d : ℝ) ^ 2 := by
  rw [signed_difference_update_source_new L M d hL hM hd hdM hnew]
  have hb := leakage_divisor_moment_sq_le L d hL (by omega)
  calc
    _ ≤ 2 * ((1 / (d : ℝ)) * (1 / (L : ℝ)^2 - 1 / (M : ℝ)^2))^2 +
        2 * (inner ℝ (leakageVector L hL) (qDivisor d))^2 := by
      nlinarith [sq_nonneg ((1 / (d : ℝ)) *
        (1 / (L : ℝ)^2 - 1 / (M : ℝ)^2) -
        inner ℝ (leakageVector L hL) (qDivisor d))]
    _ ≤ 2 * ((1 / (d : ℝ)) * (1 / (L : ℝ)^2 - 1 / (M : ℝ)^2))^2 +
        2 * (leakage L hL / (d : ℝ)^2) := by linarith
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, inv_pow]; ring

/-- Finite-divisor summation of the raw rows. The empty divisor set at R=0 is
allowed; no division by a source energy or a capacity occurs. -/
theorem signed_difference_update_source_new_sum_sq_le
    (L M a R : ℕ) (hL : 2 ≤ L) (hM : 0 < M) (ha : 2 ≤ a)
    (hnew : ∀ e ∈ R.divisors, Nat.lcm L (a * e) = M) :
    (∑ e ∈ R.divisors,
      (inner ℝ (target M - canonical L hL)
        (differenceCLM (qResidue (a * e)))) ^ 2) ≤
      (2 * zetaTwo / (a : ℝ) ^ 2) *
        ((1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) ^ 2 + leakage L hL) := by
  have hleak : 0 ≤ leakage L hL := by
    rw [← leakageVector_norm_sq]
    positivity
  have hsum : (∑ e ∈ R.divisors, 1 / (e : ℝ)^2) ≤ zetaTwo := by
    rw [zetaTwo_eq_nat_sum]
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).sum_le_tsum
      R.divisors (fun _ _ => by positivity)
  let C : ℝ := 2 / (a : ℝ)^2 *
    ((1 / (L : ℝ)^2 - 1 / (M : ℝ)^2)^2 + leakage L hL)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ e ∈ R.divisors, C * (1 / (e : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro e he
      have hep := Nat.pos_of_mem_divisors he
      have hde : 2 ≤ a * e := by nlinarith
      have hdM : a * e ∣ M := by
        rw [← hnew e he]
        exact Nat.dvd_lcm_right L (a * e)
      have hb := signed_difference_update_source_new_sq_le
        L M (a * e) hL hM hde hdM (hnew e he)
      calc
        _ ≤ _ := hb
        _ = C * (1 / (e : ℝ)^2) := by
          dsimp [C]
          push_cast
          simp only [div_eq_mul_inv, mul_pow, mul_inv_rev]
          ring
    _ = C * ∑ e ∈ R.divisors, 1 / (e : ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ C * zetaTwo := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by dsimp [C]; ring

/-- Exact positive-leakage source at a prime-power-shaped admission.
Primality is unnecessary: p≥2 and Coprime p R suffice. -/
theorem signed_difference_update_source_prime_power
    (p k R e : ℕ) (hp : 2 ≤ p) (hR : 0 < R)
    (hL : 2 ≤ p^k * R) (hcop : Nat.Coprime p R) (he : e ∈ R.divisors) :
    inner ℝ (target (p^(k+1) * R) - canonical (p^k * R) hL)
      (differenceCLM (qResidue (p^(k+1) * e))) =
      (1 / ((p^(k+1) * e : ℕ) : ℝ)) *
        (1 / ((p^k * R : ℕ) : ℝ)^2 - 1 / ((p^(k+1) * R : ℕ) : ℝ)^2) +
      inner ℝ (leakageVector (p^k * R) hL) (qDivisor (p^(k+1) * e)) := by
  have hp0 : 0 < p := by omega
  have heR := Nat.dvd_of_mem_divisors he
  have hep := Nat.pos_of_mem_divisors he
  have hpow : 2 ≤ p^(k+1) := by
    rw [pow_succ]
    have hh := pow_pos hp0 k
    nlinarith
  have hlcm : Nat.lcm (p^k * R) (p^(k+1) * e) = p^(k+1) * R := by
    apply Nat.dvd_antisymm
    · apply Nat.lcm_dvd
      · exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (Nat.le_succ k)) (dvd_refl R)
      · exact Nat.mul_dvd_mul_left (p^(k+1)) heR
    · apply (hcop.pow_left (k+1)).mul_dvd_of_dvd_of_dvd
      · exact (dvd_mul_right (p^(k+1)) e).trans (Nat.dvd_lcm_right _ _)
      · exact (dvd_mul_left R (p^k)).trans (Nat.dvd_lcm_left _ _)
  exact signed_difference_update_source_new (p^k * R) (p^(k+1) * R)
    (p^(k+1) * e) hL (Nat.mul_pos (pow_pos hp0 _) hR)
    (by nlinarith) (Nat.mul_dvd_mul_left _ heR) hlcm

/-- PAPER-001: the complete finite raw-source bound at a prime-power admission.
This does not estimate the inverse collocation response or its signed energy. -/
theorem signed_difference_update_source_prime_power_sum_sq_le
    (p k R : ℕ) (hp : 2 ≤ p) (hR : 0 < R)
    (hL : 2 ≤ p^k * R) (hcop : Nat.Coprime p R) :
    (∑ e ∈ R.divisors,
      (inner ℝ (target (p^(k+1) * R) - canonical (p^k * R) hL)
        (differenceCLM (qResidue (p^(k+1) * e)))) ^ 2) ≤
      (2 * zetaTwo / (p : ℝ)^(2 * (k+1))) *
        ((1 / ((p^k * R : ℕ) : ℝ)^2 - 1 / ((p^(k+1) * R : ℕ) : ℝ)^2)^2 +
          leakage (p^k * R) hL) := by
  have hp0 : 0 < p := by omega
  have hpow : 2 ≤ p^(k+1) := by
    rw [pow_succ]
    have hh := pow_pos hp0 k
    nlinarith
  have hnew : ∀ e ∈ R.divisors,
      Nat.lcm (p^k * R) (p^(k+1) * e) = p^(k+1) * R := by
    intro e he
    have heR := Nat.dvd_of_mem_divisors he
    apply Nat.dvd_antisymm
    · apply Nat.lcm_dvd
      · exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (Nat.le_succ k)) (dvd_refl R)
      · exact Nat.mul_dvd_mul_left (p^(k+1)) heR
    · apply (hcop.pow_left (k+1)).mul_dvd_of_dvd_of_dvd
      · exact (dvd_mul_right (p^(k+1)) e).trans (Nat.dvd_lcm_right _ _)
      · exact (dvd_mul_left R (p^k)).trans (Nat.dvd_lcm_left _ _)
  have hb := signed_difference_update_source_new_sum_sq_le
    (p^k * R) (p^(k+1) * R) (p^(k+1)) R hL
    (Nat.mul_pos (pow_pos hp0 _) hR) hpow hnew
  simpa only [Nat.cast_pow, ← pow_mul, Nat.mul_comm (k+1) 2] using hb

/-- Exact row rescaling exposes why the raw inverse-square depth factor does
not itself give a normalized-response estimate. The leakage sign stays positive. -/
theorem signed_difference_update_source_new_scaled
    (L M d : ℕ) (hL : 2 ≤ L) (hM : 0 < M) (hd : 2 ≤ d)
    (hdM : d ∣ M) (hnew : Nat.lcm L d = M) :
    (d : ℝ) * inner ℝ (target M - canonical L hL)
      (differenceCLM (qResidue d)) =
      (1 / (L : ℝ)^2 - 1 / (M : ℝ)^2) +
        (d : ℝ) * inner ℝ (leakageVector L hL) (qDivisor d) := by
  rw [signed_difference_update_source_new L M d hL hM hd hdM hnew]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring


/-!
## Revealed old leakage and the exact hidden response

Source: continuation of CanonicalPrimePowerUpdatesResearch20261107,
Sections 2, 5 and 7. The revealed component and the hidden response retain their exact signs.
-/

/-- The part of the old canonical leakage visible to the new test space. -/
def visibleLeakage (L M : ℕ) (hL : 2 ≤ L) : QHilbert :=
  conditionalProjection M (leakageVector L hL)

/-- The old leakage that remains outside the new test space. -/
def hiddenOldLeakage (L M : ℕ) (hL : 2 ≤ L) : QHilbert :=
  leakageVector L hL - visibleLeakage L M hL

/-- The new leakage minus the old leakage remaining outside the new tests. -/
def hiddenLeakageUpdate (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) : QHilbert :=
  leakageVector M hM - hiddenOldLeakage L M hL

theorem visibleLeakage_mem_cell (L M : ℕ) (hL : 2 ≤ L) :
    visibleLeakage L M hL ∈ cellSpace M :=
  (cellSpace M).starProjection_apply_mem (leakageVector L hL)

theorem leakage_inner_visibleLeakage (L M : ℕ) (hL : 2 ≤ L) :
    inner ℝ (leakageVector L hL) (visibleLeakage L M hL) =
      ‖visibleLeakage L M hL‖ ^ 2 := by
  have h := conditional_inner M (leakageVector L hL)
    (visibleLeakage L M hL) (visibleLeakage_mem_cell L M hL)
  change inner ℝ (visibleLeakage L M hL) (visibleLeakage L M hL) =
    inner ℝ (leakageVector L hL) (visibleLeakage L M hL) at h
  rw [real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem hiddenOldLeakage_inner_cell (L M : ℕ) (hL : 2 ≤ L)
    (v : QHilbert) (hv : v ∈ cellSpace M) :
    inner ℝ (hiddenOldLeakage L M hL) v = 0 := by
  rw [hiddenOldLeakage, visibleLeakage, inner_sub_left,
    conditional_inner M (leakageVector L hL) v hv, sub_self]

theorem hiddenLeakageUpdate_inner_cell (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (v : QHilbert) (hv : v ∈ cellSpace M) :
    inner ℝ (hiddenLeakageUpdate L M hL hM) v = 0 := by
  rw [hiddenLeakageUpdate, inner_sub_left,
    leakageVector_inner_cell M hM v hv,
    hiddenOldLeakage_inner_cell L M hL v hv, sub_self]

/-- Exact Pythagorean splitting of the leakage increment. -/
theorem leakage_increment_refinement_norm_sq
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) :
    ‖leakageVector M hM - leakageVector L hL‖ ^ 2 =
      ‖visibleLeakage L M hL‖ ^ 2 + ‖hiddenLeakageUpdate L M hL hM‖ ^ 2 := by
  exact InnerProductSpace.increment_norm_sq_refinement
    (leakageVector L hL) (leakageVector M hM) (visibleLeakage L M hL)
    (leakage_inner_visibleLeakage L M hL)
    (leakageVector_inner_cell M hM _ (visibleLeakage_mem_cell L M hL))

/-- The retained signed correlation loses the full newly revealed old energy. -/
theorem leakage_increment_refinement_correlation
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) :
    inner ℝ (leakageVector L hL)
      (leakageVector M hM - leakageVector L hL) =
      inner ℝ (hiddenOldLeakage L M hL) (hiddenLeakageUpdate L M hL hM) -
        ‖visibleLeakage L M hL‖ ^ 2 := by
  exact InnerProductSpace.correlation_refinement
    (leakageVector L hL) (leakageVector M hM) (visibleLeakage L M hL)
    (leakage_inner_visibleLeakage L M hL)
    (leakageVector_inner_cell M hM _ (visibleLeakage_mem_cell L M hL))

/-- Full canonical energy change, retaining the sign of the revealed old part.
This algebraic energy formula does not itself require nested cutoffs. -/
theorem canonical_energy_refinement
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 - ‖(canonical L hL : QHilbert)‖ ^ 2 =
      (1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) -
        ‖visibleLeakage L M hL‖ ^ 2 + ‖hiddenLeakageUpdate L M hL hM‖ ^ 2 +
        2 * inner ℝ (hiddenOldLeakage L M hL) (hiddenLeakageUpdate L M hL hM) := by
  have h := InnerProductSpace.norm_sq_sub_norm_sq_refinement
    (leakageVector L hL) (leakageVector M hM) (visibleLeakage L M hL)
    (leakage_inner_visibleLeakage L M hL)
  change ‖leakageVector M hM‖ ^ 2 - ‖leakageVector L hL‖ ^ 2 =
    -‖visibleLeakage L M hL‖ ^ 2 + ‖hiddenLeakageUpdate L M hL hM‖ ^ 2 +
      2 * inner ℝ (hiddenOldLeakage L M hL) (hiddenLeakageUpdate L M hL hM) at h
  rw [leakageVector_norm_sq, leakageVector_norm_sq] at h
  rw [canonical_norm M hM, canonical_norm L hL]
  linarith

/-- Exact reformulation of a proposed multiplicative budget. The inequality
on the hidden response remains an open canonical-specific obligation. -/
theorem canonical_refinement_budget_iff
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (α : ℝ) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 ≤
      (1 + α) * ‖(canonical L hL : QHilbert)‖ ^ 2 ↔
    ‖hiddenLeakageUpdate L M hL hM‖ ^ 2 +
      2 * inner ℝ (hiddenOldLeakage L M hL) (hiddenLeakageUpdate L M hL hM) ≤
      ‖visibleLeakage L M hL‖ ^ 2 + α * ‖(canonical L hL : QHilbert)‖ ^ 2 -
        (1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) := by
  have h := canonical_energy_refinement L M hL hM
  constructor <;> intro hb <;> nlinarith

/-- Three orthogonal pieces of the actual nested canonical increment. -/
theorem canonical_increment_refinement_norm_sq
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M) :
    ‖(canonical M hM : QHilbert) - canonical L hL‖ ^ 2 =
      (1 / (L : ℝ) ^ 2 - 1 / (M : ℝ) ^ 2) +
        ‖visibleLeakage L M hL‖ ^ 2 + ‖hiddenLeakageUpdate L M hL hM‖ ^ 2 := by
  rw [canonical_increment_norm_sq L M hL hM hLM,
    leakage_increment_refinement_norm_sq L M hL hM]
  ring

/-- The hidden response is exactly the unobserved part of the actual update. -/
theorem hiddenLeakageUpdate_eq_unobserved_increment
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M) :
    hiddenLeakageUpdate L M hL hM =
      ((canonical M hM : QHilbert) - canonical L hL) -
        conditionalProjection M ((canonical M hM : QHilbert) - canonical L hL) := by
  have hp : conditionalProjection M (target L) = target L :=
    (cellSpace M).starProjection_eq_self_iff.mpr
      (cellSpace_mono_of_dvd L M (by omega) hLM (target_mem_cell L (by omega)))
  simp only [hiddenLeakageUpdate, hiddenOldLeakage, visibleLeakage,
    leakageVector, map_sub, canonical_conditional, hp]
  abel

end RiemannResearch.RH.QCRTNestedCutoffs

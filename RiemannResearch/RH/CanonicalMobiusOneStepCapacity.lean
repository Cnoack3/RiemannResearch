/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCapacityIncrement
import RiemannResearch.RH.CanonicalMobiusTailIndependence
import RiemannResearch.Analysis.FiniteGramOneStepCapacity

/-!
# Exact single-conductor signed-capacity recursion

Source: the Pareto affine-exhaustion handoff asks for precise capacity gains.
This module identifies the actual complete-tail Schur denominator and signed
source, with no inverse or independence provider. When the new conductor is
larger than every old conductor, strict positivity of the denominator follows
from finite-tail injectivity and canonical triangularity. The source may still
vanish, so this does not assert divergent cumulative gain or RH.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι]

def oneStepConductors (k : ι → ℕ) (m : ℕ) : ι ⊕ Unit → ℕ :=
  Sum.elim k (fun _ => m)

omit [Fintype ι] in
theorem oneStepConductors_pos (k : ι → ℕ) (m : ℕ)
    (hk : ∀ i, 0 < k i) (hm : 0 < m) : ∀ j, 0 < oneStepConductors k m j := by
  intro j
  cases j with
  | inl i => exact hk i
  | inr j => exact hm

/-- Old-span screening coefficients of the actual newly introduced tail. -/
def oneStepScreening (N : ℕ) (k : ι → ℕ) (m : ℕ) : ι → ℝ :=
  screeningCoeff (tailFamily N k) (hilbertTailShift (canonicalMobiusHilbert m) N)

/-- Actual full-tail Schur denominator. -/
def oneStepSchur (N : ℕ) (k : ι → ℕ) (m : ℕ) : ℝ :=
  ‖screenedVector (tailFamily N k) (hilbertTailShift (canonicalMobiusHilbert m) N)‖ ^ 2

/-- Signed source surviving full old-span screening. -/
def oneStepDefect (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) (m : ℕ) : ℝ :=
  1 - inner ℝ (hilbertTailShift (canonicalMobiusHilbert m) N) (capacityNormal N k hk)

theorem oneStepSchur_expansion (N : ℕ) (k : ι → ℕ) (m : ℕ) :
    oneStepSchur N k m = canonicalMobiusTailCovariance N m m -
      ∑ i, oneStepScreening N k m i * canonicalMobiusTailCovariance N (k i) m := by
  rw [oneStepSchur, screenedVector_energy, ← real_inner_self_eq_norm_sq]
  rfl

theorem oneStepDefect_expansion (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (m : ℕ) :
    oneStepDefect N k hk m = 1 -
      ∑ i, normal N k hk i * canonicalMobiusTailCovariance N (k i) m := by
  unfold oneStepDefect capacityNormal
  rw [real_inner_comm, inner_synthesis_left]
  rfl

theorem oneStepDefect_eq_one_sub_sum (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (m : ℕ) :
    oneStepDefect N k hk m = 1 - ∑ i, oneStepScreening N k m i := by
  unfold oneStepDefect capacityNormal
  rw [screeningCoeff_source _ _ _ (normal_equations N k hk)]
  rfl

/-- Exact capacity increment for one new conductor, including degenerate
or repeated-conductor steps. The denominator and numerator are actual
complete-tail quantities, not externally supplied approximations. -/
theorem capacity_oneStep_increment (N : ℕ) (k : ι → ℕ) (m : ℕ)
    (hk : ∀ i, 0 < k i) (hm : 0 < m) :
    capacity N (oneStepConductors k m) (oneStepConductors_pos k m hk hm) -
      capacity N k hk = (oneStepDefect N k hk m) ^ 2 / oneStepSchur N k m := by
  have hfamily : tailFamily N (oneStepConductors k m) =
      Sum.elim (tailFamily N k)
        (fun _ : Unit => hilbertTailShift (canonicalMobiusHilbert m) N) := by
    funext j
    cases j <;> rfl
  have hu := normal_equations N (oneStepConductors k m)
    (oneStepConductors_pos k m hk hm)
  rw [hfamily] at hu
  exact one_step_normal_mass_increment (tailFamily N k)
    (hilbertTailShift (canonicalMobiusHilbert m) N) (normal N k hk)
    (normal N (oneStepConductors k m) (oneStepConductors_pos k m hk hm))
    (normal_equations N k hk) hu

/-- Strict positivity of the true Schur denominator when a higher conductor
is added. This is a theorem about the actual canonical family. -/
theorem oneStepSchur_succ_pos (N M : ℕ) (k : ι → ℕ)
    (hkM : ∀ i, k i ≤ M) : 0 < oneStepSchur N k (M + 1) := by
  have hf : combination k (oneStepScreening N k (M + 1)) ∈ finiteSpace M := by
    unfold combination
    rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
      (hkM i) (canonicalMobiusHilbert_mem_finiteSpace (k i))
  have h := canonicalMobiusHilbert_succ_tail_residual_energy_pos M N
    (combination k (oneStepScreening N k (M + 1))) hf
  rw [combination_tail] at h
  exact h

/-- A positive new Schur direction increases capacity precisely when its
signed source defect survives. Denominator positivity alone is insufficient. -/
theorem capacity_oneStep_strict_iff (N M : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (hkM : ∀ i, k i ≤ M) :
    capacity N k hk <
      capacity N (oneStepConductors k (M + 1))
        (oneStepConductors_pos k (M + 1) hk (by omega)) ↔
      oneStepDefect N k hk (M + 1) ≠ 0 := by
  rw [← sub_pos, capacity_oneStep_increment N k (M + 1) hk (by omega)]
  have hσ := oneStepSchur_succ_pos N M k hkM
  rw [div_pos_iff_of_pos_right hσ, sq_pos_iff]

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularRayleigh
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.Analysis.EscapingRieszDirections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Target capture by the triangular inverse-Gram direction

Source: the direction investigated in Section 11 of
BalazardTriangularResearch20261019.md. Balazard arXiv:1812.04309 supports
the triangular-dual background; the scalar projection and escape argument
are independently developed elementary Hilbert geometry.

The imported Rayleigh module retains the exact optimal ray error and
target-projection gap. For dictionaries retaining their earlier atoms
with escaping conductors, the ray gain tends to zero.
No RH, target closure, or conjectural arithmetic estimate is assumed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem directionFit_inner_atom (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) (i : ι) :
    inner ℝ (qResidue (d i)) (directionFit d) = direction d i := by
  rw [directionFit, qGram_synthesis]
  change ((residueGramMatrix d).mulVec
    ((residueGramMatrix d)⁻¹.mulVec (direction d))) i = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (qGram_posDef d hd hinj).det_pos)),
    Matrix.one_mulVec]
theorem rayleighGain_eq_normalized_inner_sq (d : ι → ℕ) (hd : ∀ i, 1 < d i)
    (hinj : Function.Injective d) :
    rayleighGain d =
      (inner ℝ qOne (‖directionFit d‖⁻¹ • directionFit d)) ^ 2 := by
  rw [real_inner_smul_right, qOne_directionFit_inner d hd hinj]
  unfold rayleighGain
  rw [← directionFit_norm_sq d hd hinj]
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  ring
variable {κ : ℕ → Type*} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
theorem directionFit_norm_tendsto_atTop (d : (n : ℕ) → κ n → ℕ)
    (hd : ∀ n i, 1 < d n i) (hinj : ∀ n, Function.Injective (d n))
    (select : (n : ℕ) → κ n)
    (he : Tendsto (fun n => d n (select n)) atTop atTop) :
    Tendsto (fun n => ‖directionFit (d n)‖) atTop atTop := by
  apply RiemannResearch.Analysis.norm_tendsto_atTop_of_vanishing_test_pairing
    (fun n => directionFit (d n)) (fun n => qResidue (d n (select n)))
  · simpa only [norm_zero] using (qResidue_tendsto_zero _ he).norm
  · have ht := direction_tendsto_one _ he
    apply ht.congr'
    exact Eventually.of_forall fun n => by
      change 1 - 1 / (d n (select n) : ℝ) =
        inner ℝ (directionFit (d n)) (qResidue (d n (select n)))
      rw [real_inner_comm (qResidue (d n (select n))) (directionFit (d n)),
        directionFit_inner_atom (d n) (hd n) (hinj n)]
      rfl
theorem rayleighGain_tendsto_zero (d : (n : ℕ) → κ n → ℕ)
    (hd : ∀ n i, 1 < d n i) (hinj : ∀ n, Function.Injective (d n))
    (he : Tendsto (fun n => ‖directionFit (d n)‖) atTop atTop)
    (hkeep : ∀ m i, ∀ᶠ n in atTop, ∃ j, d n j = d m i) :
    Tendsto (fun n => rayleighGain (d n)) atTop (𝓝 0) := by
  let v : (Σ n, κ n) → QHilbert := fun p => qResidue (d p.1 p.2)
  have hu (n : ℕ) : directionFit (d n) ∈
      (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    apply (Submodule.span ℝ (Set.range v)).le_topologicalClosure
    unfold directionFit qSynthesis
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n, i⟩, rfl⟩)
  have ha (p : Σ n, κ n) : ∀ᶠ n in atTop,
      inner ℝ (v p) (directionFit (d n)) = 1 - 1 / (d p.1 p.2 : ℝ) := by
    filter_upwards [hkeep p.1 p.2] with n hn
    obtain ⟨j, hj⟩ := hn
    simpa only [v, hj, direction] using directionFit_inner_atom (d n) (hd n) (hinj n) j
  have ht := RiemannResearch.Analysis.normalized_riesz_weak_zero v
    (fun n => directionFit (d n)) hu he (fun p => 1 - 1 / (d p.1 p.2 : ℝ)) ha qOne
  simpa only [← rayleighGain_eq_normalized_inner_sq _ (hd _) (hinj _),
    zero_pow (by decide : 2 ≠ 0)]
    using ht.pow 2

end RiemannResearch.RH.QTriangularCharge

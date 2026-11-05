/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeResidueMoments
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.QSquarefreeDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# One-sided power moments of squarefree annihilators

A single conductor identity transfers prime remainder balance to the physical signed charge.
The quantitative comparison applies for every exponent in (0,1].
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSignedTailRigidity
open ZetaTwoHilbert

/-- This needs orthogonality to just the one conductor in question. -/
theorem residue_charge_hasSum_zero (u : QHilbert) (d : ℕ) (hd : 0 < d)
    (horth : inner ℝ u (qResidue d) = 0) :
    HasSum (fun n : ℕ => signedCoefficient u n * ((n % d : ℕ) : ℝ)) 0 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs : HasSum (fun n : ℕ =>
      positiveQWeight n * qSequence u n * qSequence (qResidue d) n)
      (inner ℝ u (qResidue d)) := by
    simpa only [qInner_weighted] using (qSequence_product_summable u (qResidue d)).hasSum
  have h := hs.mul_right (d : ℝ)
  rw [horth, zero_mul] at h
  apply h.congr_fun
  intro n
  simp only [qSequence_qResidue, signedCoefficient, ArithmeticCumulative.residueFraction]
  field_simp [hdR]

/-- Either sign of a physical squarefree annihilator may be chosen. -/
theorem squarefree_absolute_moment_of_one_sided (u : QHilbert)
    (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ) (a ε : ℝ)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hε : |ε| = 1)
    (hpos : Summable (fun n : ℕ => max (ε * signedCoefficient u n) 0 * (n : ℝ) ^ a)) :
    Summable (fun n : ℕ => |signedCoefficient u n| * (n : ℝ) ^ a) ∧
      (∑' n : ℕ, |signedCoefficient u n| * (n : ℝ) ^ a) ≤
        (4 / a) * ∑' n : ℕ, max (ε * signedCoefficient u n) 0 * (n : ℝ) ^ a := by
  have hz (p : ℕ) (hp : p.Prime) :
      HasSum (fun n : ℕ => (ε * signedCoefficient u n) * ((n % p : ℕ) : ℝ)) 0 := by
    have hmem := QSquarefreeDimension.qResidue_mem_of_squarefree hp.two_le hp.squarefree
    have horth : inner ℝ u (qResidue p) = 0 := by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal hmem hu
    simpa only [mul_assoc, mul_zero] using
      (residue_charge_hasSum_zero u p hp.pos horth).mul_left ε
  simpa only [abs_mul, hε, one_mul] using
    RiemannResearch.Analysis.absolute_moment_of_one_sided_prime_orthogonality
      (fun n => ε * signedCoefficient u n) a ha ha₁ hz hpos

end RiemannResearch.RH.QSignedTailRigidity

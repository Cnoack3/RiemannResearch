/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResampling
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import RiemannResearch.RH.QPrimeResamplingFormula
import RiemannResearch.RH.PrimeResamplingCore
import RiemannResearch.RH.PrimeResamplingGeometric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual dyadic resampling and a legal-projection commutator

The full geometric conditional average of the genuine conductor-two atom
is exactly three eighths of the constant vector. Consequently this prime
resampling does not commute with projection onto the legal span of that
atom. No finite probability model substitutes for the actual Q law.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert PrimeResampling ArithmeticCumulative

theorem qResidue_two_replaceValuation (n k : ℕ) (hn : n ≠ 0) :
    qSequence (qResidue 2) (replaceValuation 2 n k) =
      if k = 0 then (1 / 2 : ℝ) else 0 := by
  rw [qSequence_qResidue]
  cases k with
  | zero =>
      have hnot := prime_not_dvd_primeCore 2 n (by norm_num) hn
      have hmod : primeCore 2 n % 2 = 1 := by
        have hlt := Nat.mod_lt (primeCore 2 n) (by norm_num : 0 < 2)
        have hne : primeCore 2 n % 2 ≠ 0 := by
          intro he
          exact hnot (Nat.dvd_of_mod_eq_zero he)
        omega
      simp [replaceValuation, residueFraction, hmod]
  | succ k =>
      simp [replaceValuation, residueFraction, pow_succ, Nat.mul_mod]

/-- Exact full-geometric dyadic conditional mean of the actual residue atom. -/
theorem C_two_qResidue_two : C 2 (qResidue 2) = (3 / 8 : ℝ) • qOne := by
  apply qSequence_injective
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · rw [qSequence_C 2 n (by norm_num) hn]
    simp_rw [qResidue_two_replaceValuation n _ hn]
    have he : (∑' k : ℕ, geometricMass 2 k *
        (if k = 0 then (1 / 2 : ℝ) else 0)) = (3 / 8 : ℝ) := by
      rw [tsum_eq_single 0]
      · norm_num [geometricMass, geometricParameter]
      · intro k hk
        simp [hk]
    rw [he]
    change (3 / 8 : ℝ) = qSequenceLinear ((3 / 8 : ℝ) • qOne) n
    rw [map_smul]
    change (3 / 8 : ℝ) = (3 / 8 : ℝ) * qSequence qOne n
    simp [qSequence_qOne, qOneSequence, hn]

/-- Every odd-prime resampling fixes the dyadic residue atom. -/
theorem qResidue_two_mem_primeInvariant (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    qResidue 2 ∈ primeInvariant p := by
  intro n
  simp only [qSequence_qResidue, residueFraction]
  rw [Nat.mul_mod, hp.mod_two_eq_one_iff_ne_two.mpr hp2, one_mul, Nat.mod_mod]

@[simp] theorem C_odd_qResidue_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    C p (qResidue 2) = qResidue 2 :=
  (C_eq_self_iff p _).mpr (qResidue_two_mem_primeInvariant p hp hp2)

/-- The smallest nontrivial legal residue span. -/
def dyadicLegalSpace : Submodule ℝ QHilbert :=
  Submodule.span ℝ ({qResidue 2} : Set QHilbert)

instance : FiniteDimensional ℝ dyadicLegalSpace := inferInstanceAs
  (FiniteDimensional ℝ (Submodule.span ℝ ({qResidue 2} : Set QHilbert)))

theorem dyadicLegalSpace_zero_at_two (f : QHilbert) (hf : f ∈ dyadicLegalSpace) :
    qSequence f 2 = 0 := by
  rcases Submodule.mem_span_singleton.mp hf with ⟨a, rfl⟩
  change qSequenceLinear (a • qResidue 2) 2 = 0
  rw [map_smul]
  change a * qSequence (qResidue 2) 2 = 0
  rw [qSequence_qResidue]
  norm_num [residueFraction]

/-- Exact signed commutator at the actual conductor-two atom, retaining the
orthogonal constant-vector residual of the legal projection. -/
theorem C_two_dyadic_projection_commutator_exact :
    C 2 (dyadicLegalSpace.starProjection (qResidue 2)) -
        dyadicLegalSpace.starProjection (C 2 (qResidue 2)) =
      (3 / 8 : ℝ) • (qOne - dyadicLegalSpace.starProjection qOne) := by
  have hg : qResidue 2 ∈ dyadicLegalSpace := Submodule.subset_span (by simp)
  rw [Submodule.starProjection_eq_self_iff.mpr hg, C_two_qResidue_two,
    map_smul, smul_sub]

/-- Actual resampling and actual legal projection fail to commute, already
on the conductor-two legal atom. -/
theorem C_two_dyadic_projection_noncommute :
    C 2 (dyadicLegalSpace.starProjection (qResidue 2)) ≠
      dyadicLegalSpace.starProjection (C 2 (qResidue 2)) := by
  have hg : qResidue 2 ∈ dyadicLegalSpace := Submodule.subset_span (by simp)
  have hp : dyadicLegalSpace.starProjection (qResidue 2) = qResidue 2 :=
    Submodule.starProjection_eq_self_iff.mpr hg
  intro he
  rw [hp, C_two_qResidue_two] at he
  have hsite := congrArg (fun f : QHilbert => qSequence f 2) he
  rw [dyadicLegalSpace_zero_at_two _ (dyadicLegalSpace.starProjection_apply_mem _)] at hsite
  change qSequenceLinear ((3 / 8 : ℝ) • qOne) 2 = 0 at hsite
  rw [map_smul] at hsite
  change (3 / 8 : ℝ) * qSequence qOne 2 = 0 at hsite
  rw [qSequence_qOne] at hsite
  norm_num [qOneSequence] at hsite

end RiemannResearch.RH.QPrimeResampling

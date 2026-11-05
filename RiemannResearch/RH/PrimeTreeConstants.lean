/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.RH.QConductorLimits
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Constants in the physical prime span and its fractional parts

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.3. The four physical coordinates have squared dual norm `74 ζ(2)`.
The signed projection remainder and the nonlinear constant classification
refer to the actual inverse-square physical space.
-/

noncomputable section
open Filter
open scoped BigOperators Topology RealInnerProductSpace
namespace RiemannResearch.RH.ZetaTwoHilbert
open ArithmeticCumulative ZetaTwoProbability QDivisibilityDensity

def primeAtomSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ {x | ∃ p : ℕ, p.Prime ∧ x = qResidue p}

def primeSixWitness : QHilbert :=
  (2 : ℝ) • qSiteRiesz 1 - qSiteRiesz 3 - qSiteRiesz 5 + qSiteRiesz 6

def primeSix : QHilbert →L[ℝ] ℝ := innerSL ℝ primeSixWitness

theorem primeSix_apply (x : QHilbert) : primeSix x =
    2 * qSequence x 1 - qSequence x 3 - qSequence x 5 + qSequence x 6 := by
  change inner ℝ primeSixWitness x = _
  simp only [primeSixWitness, inner_add_left, inner_sub_left, real_inner_smul_left,
    qSiteRiesz_inner 1 (by decide), qSiteRiesz_inner 3 (by decide),
    qSiteRiesz_inner 5 (by decide), qSiteRiesz_inner 6 (by decide)]

theorem primeSixWitness_norm_sq : ‖primeSixWitness‖ ^ 2 = 74 * zetaTwo := by
  rw [← real_inner_self_eq_norm_sq]
  change primeSix primeSixWitness = _
  rw [primeSix_apply]
  have hseq (n : ℕ) : qSequence primeSixWitness n =
      2 * qSequence (qSiteRiesz 1) n - qSequence (qSiteRiesz 3) n -
        qSequence (qSiteRiesz 5) n + qSequence (qSiteRiesz 6) n := by
    change qSequenceLinear ((2 : ℝ) • qSiteRiesz 1 - qSiteRiesz 3 - qSiteRiesz 5 + qSiteRiesz 6) n = _
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> rfl
  simp only [hseq, qSequence_qSiteRiesz 1 (by decide), qSequence_qSiteRiesz 3 (by decide),
    qSequence_qSiteRiesz 5 (by decide), qSequence_qSiteRiesz 6 (by decide)]
  norm_num [positiveQWeight] <;> ring

theorem primeSix_qResidue (p : ℕ) (hp : p.Prime) : primeSix (qResidue p) = 0 := by
  rw [primeSix_apply]
  simp only [qSequence_qResidue, residueFraction]
  by_cases h : p ≤ 6
  · interval_cases p <;> norm_num at hp <;> norm_num
  · have h1 : 1 < p := by omega
    have h3 : 3 < p := by omega
    have h5 : 5 < p := by omega
    have h6 : 6 < p := by omega
    simp only [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h5,
      Nat.mod_eq_of_lt h6, Nat.cast_one, Nat.cast_ofNat]
    ring

theorem primeSix_closedSpan (x : QHilbert) (hx : x ∈ primeAtomSpan.topologicalClosure) :
    primeSix x = 0 := by
  have hsub : primeAtomSpan ≤ LinearMap.ker primeSix.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact primeSix_qResidue p hp
  exact (closure_minimal hsub primeSix.isClosed_ker) hx

private theorem primeSix_one : primeSix qOne = 1 := by
  rw [primeSix_apply]
  simp only [qSequence_qOne]
  norm_num [qOneSequence]

/-- The squared-distance obstruction with the entire orthogonal remainder. -/
theorem one_primeSpan_error_exact (x : QHilbert) (hx : x ∈ primeAtomSpan.topologicalClosure) :
    ‖qOne - x‖ ^ 2 = 1 / (74 * zetaTwo) +
      ‖qOne - x - (1 / (74 * zetaTwo)) • primeSixWitness‖ ^ 2 := by
  have h0 : (74 * zetaTwo : ℝ) ≠ 0 := by positivity [zetaTwo_pos]
  have hi : inner ℝ (qOne - x) primeSixWitness = 1 := by
    rw [real_inner_comm]
    change primeSix (qOne - x) = _
    simp only [map_sub, primeSix_one, primeSix_closedSpan x hx, sub_zero]
  rw [norm_sub_sq_real (qOne - x) (_ • _), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right, hi, primeSixWitness_norm_sq]
  field_simp [h0, zetaTwo_pos.ne'] <;> ring

/-- Physical vectors obtained by taking a single fractional part after forming
an arbitrary finite real linear combination of the prime atoms. -/
def primeFractionalParts : Set QHilbert :=
  {x | ∃ u ∈ primeAtomSpan, ∀ n, qSequence x n = Int.fract (qSequence u n)}

private theorem primeSix_fractionalParts {x : QHilbert} (hx : x ∈ primeFractionalParts) :
    primeSix x ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨u, hu, h⟩ := hx
  have hz := primeSix_closedSpan u (primeAtomSpan.le_topologicalClosure hu)
  rw [primeSix_apply] at hz ⊢
  refine ⟨-(2 * ⌊qSequence u 1⌋ - ⌊qSequence u 3⌋ - ⌊qSequence u 5⌋ + ⌊qSequence u 6⌋), ?_⟩
  simp only [h, Int.fract, Int.cast_neg, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  linarith

private theorem primeFractionalParts_reflected (p : ℕ) (hp : p.Prime) :
    qReflected p ∈ primeFractionalParts := by
  refine ⟨-(qResidue p), primeAtomSpan.neg_mem (Submodule.subset_span ⟨p, hp, rfl⟩), ?_⟩
  intro n
  have hneg : qSequence (-(qResidue p)) n = -residueFraction p n := by
    change qSequenceLinear (-(qResidue p)) n = _
    rw [map_neg]
    exact congrArg Neg.neg (congrFun (qSequence_qResidue p) n)
  rw [hneg, qReflected_sequence]
  by_cases hn : n = 0
  · simp [hn, qOneSequence, residueFraction, positiveDivisor]
  by_cases hd : p ∣ n
  · simp [qOneSequence, positiveDivisor, residueFraction, hn, hd, Nat.mod_eq_zero_of_dvd hd]
  · have hzero : n % p ≠ 0 := fun he => hd (Nat.dvd_of_mod_eq_zero he)
    have hr0 : 0 < residueFraction p n := by
      unfold residueFraction
      exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hzero) (by exact_mod_cast hp.pos)
    have hr1 : residueFraction p n < 1 := by
      unfold residueFraction
      exact (div_lt_one (by exact_mod_cast hp.pos : 0 < (p : ℝ))).mpr (by exact_mod_cast Nat.mod_lt n hp.pos)
    simp only [qOneSequence, if_neg hn, positiveDivisor, hd, and_false, if_false, sub_zero]
    symm
    apply Int.fract_eq_iff.mpr
    refine ⟨by linarith, by linarith, -1, ?_⟩
    push_cast
    ring

/-- All constant limits of the fractional prime span under Q. -/
theorem constant_mem_primeFractionalParts_closure_iff (c : ℝ) :
    c • qOne ∈ closure primeFractionalParts ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro hc
    have hclosed := Real.isClosed_range_intCast.preimage primeSix.continuous
    have hz : primeSix (c • qOne) ∈ Set.range ((↑) : ℤ → ℝ) :=
      (closure_minimal (fun _ hx => primeSix_fractionalParts hx) hclosed) hc
    rw [map_smul, smul_eq_mul, primeSix_one, mul_one] at hz
    obtain ⟨z, hz⟩ := hz
    have hclosed1 := (isClosed_Icc (a := (0 : ℝ)) (b := 1)).preimage
      (innerSL ℝ (qSiteRiesz 1)).continuous
    have hsub : primeFractionalParts ⊆ (innerSL ℝ (qSiteRiesz 1)) ⁻¹' Set.Icc 0 1 := by
      rintro x ⟨u, _, h⟩
      change inner ℝ (qSiteRiesz 1) x ∈ Set.Icc 0 1
      rw [qSiteRiesz_inner 1 (by decide), h 1]
      exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have hI := (closure_minimal hsub hclosed1) hc
    change inner ℝ (qSiteRiesz 1) (c • qOne) ∈ Set.Icc 0 1 at hI
    rw [real_inner_smul_right, qSiteRiesz_inner 1 (by decide), qSequence_qOne] at hI
    norm_num [qOneSequence] at hI
    have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ (z : ℝ) by simpa [hz] using hI.1)
    have hz1 : z ≤ (1 : ℤ) := by exact_mod_cast (show (z : ℝ) ≤ (1 : ℝ) by simpa [hz] using hI.2)
    rcases (show z = 0 ∨ z = 1 by omega) with h | h <;> simp_all
  · rintro (rfl | rfl)
    · rw [zero_smul]
      apply subset_closure
      refine ⟨0, primeAtomSpan.zero_mem, ?_⟩
      intro n
      change qSequenceLinear 0 n = Int.fract (qSequenceLinear 0 n)
      simp
    · rw [one_smul]
      choose p hle hp using Nat.exists_infinite_primes
      have ht : Tendsto p atTop atTop := tendsto_atTop.mpr fun k =>
        (eventually_ge_atTop k).mono fun j hj => hj.trans (hle j)
      exact mem_closure_of_tendsto (qReflected_tendsto_one p ht)
        (Eventually.of_forall (fun j => primeFractionalParts_reflected (p j) (hp j)))

end RiemannResearch.RH.ZetaTwoHilbert

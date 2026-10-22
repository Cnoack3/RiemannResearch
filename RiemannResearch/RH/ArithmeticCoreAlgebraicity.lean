/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CotangentContraction
import RiemannResearch.RH.ArithmeticCoreInertia
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraicity of the actual finite arithmetic core

Rational-angle sine and cosine algebraicity comes from Mathlib's Niven module,
whose proof uses the integral root-of-unity exponential. Division and the
complete signed finite sums then preserve algebraicity over `ℚ`. Determinants,
adjugates and the total matrix inverse preserve algebraic entries too.
The previously proved arithmetic/physical core equality transfers this to the
actual inverse charge and constrained optimizer, without an algebraic-core
premise or a supplied inverse. No arithmetic limiting endpoint is asserted.

Source: user-directed continuation of `PhysicalMeanOneAdvance20261008.md`;
Mathlib `NumberTheory.Niven`, rational-angle root-of-unity proof strategy.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ArithmeticCoreAlgebraicity
open RiemannResearch.RH.Pareto

private theorem algebraic_rat (q : ℚ) : IsAlgebraic ℚ (q : ℝ) := by
  simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q)

private theorem algebraic_nat (n : ℕ) : IsAlgebraic ℚ (n : ℝ) := by
  simpa using algebraic_rat (n : ℚ)

private theorem algebraic_int (n : ℤ) : IsAlgebraic ℚ (n : ℝ) := by
  simpa using algebraic_rat (n : ℚ)

private theorem algebraic_two : IsAlgebraic ℚ (2 : ℝ) := by
  simpa using algebraic_rat 2

private theorem algebraic_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, IsAlgebraic ℚ (f i)) : IsAlgebraic ℚ (∑ i ∈ s, f i) :=
  (IsIntegral.sum f (fun i hi => (h i hi).isIntegral)).isAlgebraic

private theorem algebraic_div {a b : ℝ} (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a/b) := by
  simpa only [div_eq_mul_inv] using ha.mul hb.inv

/-- Rational-angle cotangent is algebraic, including the total zero-denominator convention. -/
theorem periodCotangent_algebraic (Q r : ℕ) : IsAlgebraic ℚ (periodCotangent Q r) := by
  let q : ℚ := (r : ℚ)/(Q : ℚ)
  have hc : IsAlgebraic ℚ (Real.cos ((q : ℝ)*Real.pi)) :=
    (Real.isAlgebraic_cos_rat_mul_pi q).extendScalars (S := ℚ)
      (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective)
  have hs : IsAlgebraic ℚ (Real.sin ((q : ℝ)*Real.pi)) :=
    (Real.isAlgebraic_sin_rat_mul_pi q).extendScalars (S := ℚ)
      (show Function.Injective (algebraMap ℤ ℚ) from Int.cast_injective)
  have he : (q : ℝ)*Real.pi = Real.pi*(r : ℝ)/(Q : ℝ) := by
    dsimp [q]
    push_cast
    ring
  unfold periodCotangent
  rw [← he]
  exact algebraic_div hc hs

/-- Every finite `V` value is algebraic, with its complete natural-remainder sum. -/
theorem cotangentV_algebraic (a b : ℕ) : IsAlgebraic ℚ (cotangentV a b) := by
  unfold cotangentV
  apply algebraic_sum
  intro r _
  exact (algebraic_div (algebraic_nat (a*r % b)) (algebraic_nat b)).mul
    (periodCotangent_algebraic b r)

/-- The originally specified signed double-divisor arithmetic core is algebraic. -/
theorem ramanujanCotangentCoreEntry_algebraic (d e : ℕ) :
    IsAlgebraic ℚ (ramanujanCotangentCoreEntry d e) := by
  unfold ramanujanCotangentCoreEntry
  apply (algebraic_div isAlgebraic_one algebraic_two).neg.mul
  apply algebraic_sum
  intro a _
  apply algebraic_sum
  intro b _
  exact ((algebraic_int (ArithmeticFunction.moebius (d/a))).mul
    (algebraic_int (ArithmeticFunction.moebius (e/b)))).mul
      ((cotangentV_algebraic a b).add (cotangentV_algebraic b a))

theorem finiteCotangentCore_entry_algebraic (n : ℕ) (i j : Fin n) :
    IsAlgebraic ℚ (finiteCotangentCore n i j) :=
  ramanujanCotangentCoreEntry_algebraic (i.val+2) (j.val+2)

theorem residue_algebraic (a k : ℕ) : IsAlgebraic ℚ (residue a k) :=
  algebraic_nat (k % a)

theorem centeredResidueProduct_algebraic (a b k : ℕ) :
    IsAlgebraic ℚ (centeredResidueProduct a b k) := by
  unfold centeredResidueProduct
  exact (((residue_algebraic a k).mul (residue_algebraic b k)).sub
    ((algebraic_div ((algebraic_nat b).sub isAlgebraic_one) algebraic_two).mul
      (residue_algebraic a k))).sub
    ((algebraic_div ((algebraic_nat a).sub isAlgebraic_one) algebraic_two).mul
      (residue_algebraic b k))

/-- The direct cotangent-difference core is algebraic even before any Gram contraction. -/
theorem residueDifferenceCotangentCore_algebraic (Q a b : ℕ) :
    IsAlgebraic ℚ (residueDifferenceCotangentCore Q a b) := by
  unfold residueDifferenceCotangentCore
  apply (algebraic_div isAlgebraic_one (algebraic_two.mul (algebraic_nat Q))).mul
  apply algebraic_sum
  intro r _
  exact (centeredResidueProduct_algebraic a b r.val).mul
    ((periodCotangent_algebraic Q r.val).sub (periodCotangent_algebraic Q (r.val+1)))

theorem packetDifferenceCotangentCoreEntry_algebraic (Q d e : ℕ) :
    IsAlgebraic ℚ (packetDifferenceCotangentCoreEntry Q d e) := by
  unfold packetDifferenceCotangentCoreEntry
  apply algebraic_sum
  intro a _
  apply algebraic_sum
  intro b _
  exact ((algebraic_int (ArithmeticFunction.moebius (d/a.val))).mul
    (algebraic_int (ArithmeticFunction.moebius (e/b.val)))).mul
      (residueDifferenceCotangentCore_algebraic Q a.val b.val)

theorem arithmeticPacketCore_entry_algebraic (Q : ℕ) (s : Finset ℕ) (i j : s) :
    IsAlgebraic ℚ (arithmeticPacketCore Q s i j) :=
  packetDifferenceCotangentCoreEntry_algebraic Q i.val j.val

/-- Actual physical core entries are algebraic, by the established arithmetic identity. -/
theorem derivedCore_entry_algebraic (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (i j : s) :
    IsAlgebraic ℚ (PhysicalPacketCore.derivedCore s i j) := by
  rw [← specified_core_eq_derivedCore_of_legal s hs]
  exact ramanujanCotangentCoreEntry_algebraic i.val j.val

private theorem algebraic_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, IsAlgebraic ℚ (M i j)) :
    IsAlgebraic ℚ M.det :=
  (IsIntegral.det (fun i j => (hM i j).isIntegral)).isAlgebraic

private theorem algebraic_matrix_adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, IsAlgebraic ℚ (M i j)) (i j : ι) :
    IsAlgebraic ℚ (M.adjugate i j) := by
  rw [Matrix.adjugate_apply]
  apply algebraic_matrix_det
  intro k l
  rw [Matrix.updateRow_apply]
  by_cases hk : k = j
  · rw [if_pos hk]
    by_cases hl : l = i
    · simpa [Pi.single_apply, hl] using algebraic_nat 1
    · simpa [Pi.single_apply, hl] using algebraic_nat 0
  · rw [if_neg hk]
    exact hM k l

private theorem algebraic_matrix_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, IsAlgebraic ℚ (M i j)) (i j : ι) :
    IsAlgebraic ℚ (M⁻¹ i j) := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (algebraic_matrix_det M hM).inv.mul (algebraic_matrix_adjugate M hM i j)

theorem finiteCotangentCore_det_algebraic (n : ℕ) :
    IsAlgebraic ℚ (finiteCotangentCore n).det :=
  algebraic_matrix_det (finiteCotangentCore n) (finiteCotangentCore_entry_algebraic n)

theorem finiteCotangentCore_inverse_entry_algebraic (n : ℕ) (i j : Fin n) :
    IsAlgebraic ℚ ((finiteCotangentCore n)⁻¹ i j) :=
  algebraic_matrix_inverse (finiteCotangentCore n) (finiteCotangentCore_entry_algebraic n) i j

/-- Algebraicity of the total matrix inverse, including its singular convention. -/
theorem specifiedCore_inverse_entry_algebraic (s : Finset ℕ) (i j : s) :
    IsAlgebraic ℚ ((@Inv.inv (Matrix s s ℝ) Matrix.inv
      (fun a b : s => ramanujanCotangentCoreEntry a.val b.val)) i j) :=
  algebraic_matrix_inverse (fun a b : s => ramanujanCotangentCoreEntry a.val b.val)
    (fun a b => ramanujanCotangentCoreEntry_algebraic a.val b.val) i j

/-- The independently defined finite cotangent-difference matrix has algebraic inverse entries. -/
theorem arithmeticPacketCore_inverse_entry_algebraic (Q : ℕ) (s : Finset ℕ) (i j : s) :
    IsAlgebraic ℚ ((arithmeticPacketCore Q s)⁻¹ i j) :=
  algebraic_matrix_inverse (arithmeticPacketCore Q s)
    (arithmeticPacketCore_entry_algebraic Q s) i j

/-- Algebraicity of the independently defined arithmetic inverse charge, at every finite stage. -/
theorem arithmeticInverseCharge_algebraic (Q : ℕ) (s : Finset ℕ) :
    IsAlgebraic ℚ (ArithmeticCoreInertia.arithmeticInverseCharge Q s) := by
  unfold ArithmeticCoreInertia.arithmeticInverseCharge mulVec dotProduct ramanujanTotientVector
  apply algebraic_sum
  intro i _
  apply (algebraic_nat (Nat.totient i.val)).mul
  apply algebraic_sum
  intro j _
  exact (arithmeticPacketCore_inverse_entry_algebraic Q s i j).mul
    (algebraic_nat (Nat.totient j.val))

/-- Algebraicity of each independently defined arithmetic constrained coefficient. -/
theorem arithmeticConstrainedOptimizer_entry_algebraic (Q : ℕ) (s : Finset ℕ) (i : s) :
    IsAlgebraic ℚ (ArithmeticCoreInertia.arithmeticConstrainedOptimizer Q s i) := by
  unfold ArithmeticCoreInertia.arithmeticConstrainedOptimizer
  simp only [Pi.smul_apply, smul_eq_mul]
  apply (algebraic_div algebraic_two (arithmeticInverseCharge_algebraic Q s)).mul
  unfold mulVec dotProduct ramanujanTotientVector
  apply algebraic_sum
  intro j _
  exact (arithmeticPacketCore_inverse_entry_algebraic Q s i j).mul
    (algebraic_nat (Nat.totient j.val))

theorem derivedCore_det_algebraic (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    IsAlgebraic ℚ (PhysicalPacketCore.derivedCore s).det :=
  algebraic_matrix_det (PhysicalPacketCore.derivedCore s) (derivedCore_entry_algebraic s hs)

/-- Every entry of the actual core inverse is algebraic. No inverse is supplied. -/
theorem derivedCore_inverse_entry_algebraic (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (i j : s) :
    IsAlgebraic ℚ ((PhysicalPacketCore.derivedCore s)⁻¹ i j) :=
  algebraic_matrix_inverse (PhysicalPacketCore.derivedCore s)
    (derivedCore_entry_algebraic s hs) i j

theorem inverseCharge_algebraic (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    IsAlgebraic ℚ (PhysicalPacketCore.inverseCharge s) := by
  unfold PhysicalPacketCore.inverseCharge mulVec dotProduct ramanujanTotientVector
  apply algebraic_sum
  intro i _
  apply (algebraic_nat (Nat.totient i.val)).mul
  apply algebraic_sum
  intro j _
  exact (derivedCore_inverse_entry_algebraic s hs i j).mul
    (algebraic_nat (Nat.totient j.val))

theorem constrainedOptimizer_entry_algebraic (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (i : s) :
    IsAlgebraic ℚ (PhysicalPacketCore.constrainedOptimizer s i) := by
  unfold PhysicalPacketCore.constrainedOptimizer
  simp only [Pi.smul_apply, smul_eq_mul]
  apply (algebraic_div algebraic_two (inverseCharge_algebraic s hs)).mul
  unfold mulVec dotProduct ramanujanTotientVector
  apply algebraic_sum
  intro j _
  exact (derivedCore_inverse_entry_algebraic s hs i j).mul
    (algebraic_nat (Nat.totient j.val))

/-- The charge at each physical divisor stage is algebraic over the rationals. -/
theorem divisor_stage_charge_algebraic (L : ℕ) :
    IsAlgebraic ℚ (PhysicalPacketCore.inverseCharge (PhysicalPacketCore.divisorPackets L)) :=
  inverseCharge_algebraic _ (PhysicalPacketCore.divisorPackets_legal L)

/-- Every constrained coefficient at each physical divisor stage is algebraic. -/
theorem divisor_stage_optimizer_entry_algebraic (L : ℕ)
    (i : PhysicalPacketCore.divisorPackets L) :
    IsAlgebraic ℚ (PhysicalPacketCore.constrainedOptimizer (PhysicalPacketCore.divisorPackets L) i) :=
  constrainedOptimizer_entry_algebraic _ (PhysicalPacketCore.divisorPackets_legal L) i

end RiemannResearch.RH.Pareto.ArithmeticCoreAlgebraicity

/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTCarryArithmetic
import RiemannResearch.Analysis.ScreenedCarry
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QConductorCoefficientMass

/-!
# Actual Q-Hilbert CRT floor carries

Source: Christian Noack's `CRT_Carries_and_Squarefree_Residual_Exhaustion`,
19 October 2026, sections 2 and 5. The definition encodes the actual
integer floor sequence in the existing complete inverse-square Hilbert
space. The decomposition is subsequently proved, not built into the
definition or assumed. All projections are the actual `starProjection`.
No asymptotic exhaustion statement is assumed or proved here.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.RH.QCRTCarry

open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.ScreenedCarry

private theorem carry_square_summable (p q : ℕ) (a b : ℤ) :
    Summable (fun n => positiveQWeight n *
      (CRTCarryArithmetic.carry p q a b n : ℝ) ^ 2) :=
  boundedQ_square_summable _ (|(a : ℝ)| + |(b : ℝ)| + 1) (by positivity)
    (CRTCarryArithmetic.carry_abs_le p q a b)

/-- The actual floor-defined carry, encoded for all parameters independently
of whether the coefficients satisfy a CRT relation. -/
def qCarry (p q : ℕ) (a b : ℤ) : QHilbert :=
  encodeQ (fun n => (CRTCarryArithmetic.carry p q a b n : ℝ))
    (carry_square_summable p q a b)

@[simp] theorem qSequence_qCarry (p q : ℕ) (a b : ℤ) :
    qSequence (qCarry p q a b) = fun n => (CRTCarryArithmetic.carry p q a b n : ℝ) :=
  qSequence_encodeQ _ _ (by simp [CRTCarryArithmetic.carry_zero])

/-- The actual floor vector equals the real synthesis combination. -/
theorem qCarry_eq_linear (p q : ℕ) (a b t : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
      1 + (t : ℝ) * (p : ℝ) * (q : ℝ)) :
    qCarry p q a b = (a : ℝ) • qResidue p + (b : ℝ) • qResidue q - qResidue (p * q) := by
  apply qSequence_injective
  funext n
  change qSequence (qCarry p q a b) n =
    qSequenceLinear ((a : ℝ) • qResidue p + (b : ℝ) • qResidue q - qResidue (p * q)) n
  rw [map_sub, map_add, map_smul, map_smul]
  change qSequence (qCarry p q a b) n =
    (a : ℝ) * qSequence (qResidue p) n +
      (b : ℝ) * qSequence (qResidue q) n - qSequence (qResidue (p * q)) n
  rw [qSequence_qCarry, qSequence_qResidue, qSequence_qResidue, qSequence_qResidue]
  exact CRTCarryArithmetic.real_decomposition p q a b t n hp hq hcrt

theorem qCarry_swap (p q : ℕ) (a b : ℤ) : qCarry p q a b = qCarry q p b a := by
  apply qSequence_injective
  funext n
  simp only [qSequence_qCarry, CRTCarryArithmetic.carry_swap]

theorem qCarry_period (p q : ℕ) (a b : ℤ) (n : ℕ) :
    qSequence (qCarry p q a b) (n + p * q) = qSequence (qCarry p q a b) n := by
  simp only [qSequence_qCarry, CRTCarryArithmetic.carry_period]

section ValidCRT

variable (p q : ℕ) (a b t : ℤ) (hp : 0 < p) (hq : 0 < q)
variable (hcrt : (a : ℝ) * (q : ℝ) + (b : ℝ) * (p : ℝ) =
  1 + (t : ℝ) * (p : ℝ) * (q : ℝ))

include hp hq hcrt

/-- The raw vector change, including its signed old-space terms. -/
theorem qCarry_change_of_valid_representatives (a' b' t' : ℤ)
    (hcrt' : (a' : ℝ) * (q : ℝ) + (b' : ℝ) * (p : ℝ) =
      1 + (t' : ℝ) * (p : ℝ) * (q : ℝ)) :
    qCarry p q a' b' - qCarry p q a b =
      ((a' : ℝ) - (a : ℝ)) • qResidue p +
        ((b' : ℝ) - (b : ℝ)) • qResidue q := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt,
    qCarry_eq_linear p q a' b' t' hp hq hcrt']
  simp only [sub_smul]
  abel

/-- Complete signed raw Gram energy, with all six terms retained. -/
theorem qCarry_norm_sq :
    ‖qCarry p q a b‖ ^ 2 =
      (a : ℝ) ^ 2 * ‖qResidue p‖ ^ 2 + (b : ℝ) ^ 2 * ‖qResidue q‖ ^ 2 +
      ‖qResidue (p * q)‖ ^ 2 +
      2 * (a : ℝ) * (b : ℝ) * inner ℝ (qResidue p) (qResidue q) -
      2 * (a : ℝ) * inner ℝ (qResidue p) (qResidue (p * q)) -
      2 * (b : ℝ) * inner ℝ (qResidue q) (qResidue (p * q)) := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact carry_norm_sq (a : ℝ) (b : ℝ) (qResidue p) (qResidue q) (qResidue (p * q))

variable (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]

/-- The requested actual floor-to-orthogonal-projection bridge. -/
theorem screen_qCarry (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    screen V (qCarry p q a b) = -screen V (qResidue (p * q)) := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact screen_carry V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

/-- Any two valid CRT coefficient choices yield the same screened vector. -/
theorem screen_qCarry_representatives (a' b' t' : ℤ)
    (hcrt' : (a' : ℝ) * (q : ℝ) + (b' : ℝ) * (p : ℝ) =
      1 + (t' : ℝ) * (p : ℝ) * (q : ℝ))
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    screen V (qCarry p q a b) = screen V (qCarry p q a' b') := by
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV,
    screen_qCarry p q a' b' t' hp hq hcrt' V hpV hqV]

theorem project_qCarry (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    V.starProjection (qCarry p q a b) =
      (a : ℝ) • qResidue p + (b : ℝ) • qResidue q -
        V.starProjection (qResidue (p * q)) := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact project_carry V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

theorem norm_screen_qCarry_eq (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    ‖screen V (qCarry p q a b)‖ = ‖screen V (qResidue (p * q))‖ := by
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV, norm_neg]

theorem norm_screen_qCarry_le (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    ‖screen V (qCarry p q a b)‖ ≤ ‖qResidue (p * q)‖ := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact norm_screen_carry_le V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

/-- The screened norm is controlled by the small composite atom, not by
the potentially large raw positive-representative carry. -/
theorem norm_screen_qCarry_sq_le (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V)
    (hprod : 2 ≤ p * q) :
    ‖screen V (qCarry p q a b)‖ ^ 2 ≤ 2 / (zetaTwo * ((p * q : ℕ) : ℝ)) := by
  have hn := norm_screen_qCarry_le p q a b t hp hq hcrt V hpV hqV
  calc
    _ ≤ ‖qResidue (p * q)‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    _ ≤ _ := qResidue_norm_sq_le_two_div (p * q) hprod

theorem screen_qCarry_eq_zero_iff (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    screen V (qCarry p q a b) = 0 ↔ qResidue (p * q) ∈ V := by
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV, neg_eq_zero, screen_eq_zero_iff]

theorem qCarry_mem_iff (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    qCarry p q a b ∈ V ↔ qResidue (p * q) ∈ V := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact carry_mem_iff V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

theorem qCarry_energy_pythagoras (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    ‖qCarry p q a b‖ ^ 2 = ‖V.starProjection (qCarry p q a b)‖ ^ 2 +
      ‖screen V (qResidue (p * q))‖ ^ 2 := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact carry_energy_pythagoras V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

theorem residual_inner_qCarry (u : QHilbert)
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    inner ℝ (screen V u) (qCarry p q a b) =
      -inner ℝ (screen V u) (qResidue (p * q)) := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact residual_inner_carry V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) u hpV hqV

theorem screened_target_inner_qCarry (u : QHilbert)
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    inner ℝ (screen V u) (screen V (qCarry p q a b)) =
      -inner ℝ (screen V u) (screen V (qResidue (p * q))) := by
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV, inner_neg_right]

/-- Every entry of a complete screened carry Gram block is intrinsic. -/
theorem screened_gram_qCarry (p' q' : ℕ) (a' b' t' : ℤ)
    (hp' : 0 < p') (hq' : 0 < q')
    (hcrt' : (a' : ℝ) * (q' : ℝ) + (b' : ℝ) * (p' : ℝ) =
      1 + (t' : ℝ) * (p' : ℝ) * (q' : ℝ))
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V)
    (hpV' : qResidue p' ∈ V) (hqV' : qResidue q' ∈ V) :
    inner ℝ (screen V (qCarry p q a b)) (screen V (qCarry p' q' a' b')) =
      inner ℝ (screen V (qResidue (p * q))) (screen V (qResidue (p' * q'))) := by
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV,
    screen_qCarry p' q' a' b' t' hp' hq' hcrt' V hpV' hqV']
  rw [inner_neg_left, inner_neg_right, neg_neg]

/-- The two actual finite-space enlargements are identical. -/
theorem qCarry_sup_span_eq (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    V ⊔ Submodule.span ℝ {qCarry p q a b} =
      V ⊔ Submodule.span ℝ {qResidue (p * q)} := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact sup_span_carry_eq V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) hpV hqV

theorem qCarry_refit_eq (u : QHilbert)
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    refit V u (qCarry p q a b) = refit V u (qResidue (p * q)) := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact refit_carry_eq V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) u hpV hqV

theorem qCarry_gain_quotient_eq (u : QHilbert)
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    (inner ℝ (screen V u) (qCarry p q a b)) ^ 2 /
        ‖screen V (qCarry p q a b)‖ ^ 2 =
      (inner ℝ (screen V u) (qResidue (p * q))) ^ 2 /
        ‖screen V (qResidue (p * q))‖ ^ 2 := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact gain_quotient_carry_eq V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) u hpV hqV

theorem qCarry_optimal_refit_gain (u : QHilbert)
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V)
    (hz : screen V (qResidue (p * q)) ≠ 0) :
    ‖screen V u‖ ^ 2 - ‖u - refit V u (qCarry p q a b)‖ ^ 2 =
      (inner ℝ (screen V u) (qResidue (p * q))) ^ 2 /
        ‖screen V (qResidue (p * q))‖ ^ 2 := by
  rw [qCarry_eq_linear p q a b t hp hq hcrt]
  exact optimal_refit_gain_carry V (a : ℝ) (b : ℝ) (qResidue p) (qResidue q)
    (qResidue (p * q)) u hpV hqV hz


/-- Exact distance gain for the actual enlarged Q-Hilbert projection. -/
theorem qCarry_projection_gain (u : QHilbert)
    [(V ⊔ Submodule.span ℝ {qCarry p q a b}).HasOrthogonalProjection]
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V)
    (hz : screen V (qResidue (p * q)) ≠ 0) :
    ‖screen V u‖ ^ 2 -
        ‖u - (V ⊔ Submodule.span ℝ {qCarry p q a b}).starProjection u‖ ^ 2 =
      (inner ℝ (screen V u) (qCarry p q a b)) ^ 2 /
        ‖screen V (qCarry p q a b)‖ ^ 2 := by
  apply projection_gain V u (qCarry p q a b)
  rw [screen_qCarry p q a b t hp hq hcrt V hpV hqV]
  exact neg_ne_zero.mpr hz

/-- The equality concerns actual projections of every target, not only
candidate refits or equal formal spans. -/
theorem qCarry_projection_eq_composite (u : QHilbert)
    [(V ⊔ Submodule.span ℝ {qCarry p q a b}).HasOrthogonalProjection]
    [(V ⊔ Submodule.span ℝ {qResidue (p * q)}).HasOrthogonalProjection]
    (hpV : qResidue p ∈ V) (hqV : qResidue q ∈ V) :
    (V ⊔ Submodule.span ℝ {qCarry p q a b}).starProjection u =
      (V ⊔ Submodule.span ℝ {qResidue (p * q)}).starProjection u := by
  rw [← refit_eq_projection V u (qCarry p q a b),
    qCarry_refit_eq p q a b t hp hq hcrt V u hpV hqV,
    refit_eq_projection V u (qResidue (p * q))]

end ValidCRT


/-- Every finite actual floor-carry block has the composite screened
synthesis, with its complete signed cancellation retained. -/
theorem screen_qCarry_block {ι : Type*} [Fintype ι]
    (p q : ι → ℕ) (a b t : ι → ℤ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hcrt : ∀ i, (a i : ℝ) * (q i : ℝ) + (b i : ℝ) * (p i : ℝ) =
      1 + (t i : ℝ) * (p i : ℝ) * (q i : ℝ))
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hpV : ∀ i, qResidue (p i) ∈ V) (hqV : ∀ i, qResidue (q i) ∈ V)
    (c : ι → ℝ) :
    screen V (∑ i, c i • qCarry (p i) (q i) (a i) (b i)) =
      -screen V (∑ i, c i • qResidue (p i * q i)) := by
  have hi : ∀ i, screen V (qCarry (p i) (q i) (a i) (b i)) =
      -screen V (qResidue (p i * q i)) := fun i =>
    screen_qCarry (p i) (q i) (a i) (b i) (t i) (hp i) (hq i)
      (hcrt i) V (hpV i) (hqV i)
  simp only [map_sum, map_smul, hi, smul_neg, Finset.sum_neg_distrib]

theorem norm_screen_qCarry_block {ι : Type*} [Fintype ι]
    (p q : ι → ℕ) (a b t : ι → ℤ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hcrt : ∀ i, (a i : ℝ) * (q i : ℝ) + (b i : ℝ) * (p i : ℝ) =
      1 + (t i : ℝ) * (p i : ℝ) * (q i : ℝ))
    (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]
    (hpV : ∀ i, qResidue (p i) ∈ V) (hqV : ∀ i, qResidue (q i) ∈ V)
    (c : ι → ℝ) :
    ‖screen V (∑ i, c i • qCarry (p i) (q i) (a i) (b i))‖ ^ 2 =
      ‖screen V (∑ i, c i • qResidue (p i * q i))‖ ^ 2 := by
  rw [screen_qCarry_block p q a b t hp hq hcrt V hpV hqV c, norm_neg]

end RiemannResearch.RH.QCRTCarry

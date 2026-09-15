/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResonanceCellRefit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# From seven signed Gram entries to the screened resonance bound

Source: independently derived finite covariance estimate in Christian Noack's
two-three packet continuation, 15 September 2026. The arithmetic estimates on
the raw seven Gram entries are explicit hypotheses. All signed mixed terms
remain present, and the two old directions are removed by legal corrections.
-/

namespace RiemannResearch.Analysis.ResonanceLeadingGram

open scoped BigOperators
open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ResonanceCellRefit

noncomputable section

/-- An entrywise error estimate controls every signed quadratic combination. -/
theorem quadratic_error_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (e : ι → ι → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (he : ∀ i j, |e i j| ≤ E) :
    |∑ i, ∑ j, w i * w j * e i j| ≤
      (Fintype.card ι : ℝ) * E * (∑ i, (w i)^2) := by
  have ht (i j : ι) :
      |w i * w j * e i j| ≤ E/2*((w i)^2+(w j)^2) := by
    have hc : 2*(|w i| * |w j|) ≤ (w i)^2+(w j)^2 := by
      nlinarith [sq_nonneg (|w i|-|w j|), sq_abs (w i), sq_abs (w j)]
    have hm := mul_le_mul_of_nonneg_left hc hE
    calc
      |w i * w j * e i j| = |w i| * |w j| * |e i j| := by
        rw [abs_mul, abs_mul]
      _ ≤ |w i| * |w j| * E :=
        mul_le_mul_of_nonneg_left (he i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ E/2*((w i)^2+(w j)^2) := by nlinarith
  calc
    |∑ i, ∑ j, w i*w j*e i j| ≤ ∑ i, |∑ j, w i*w j*e i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |w i*w j*e i j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, E/2*((w i)^2+(w j)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact ht i j
    _ = (Fintype.card ι : ℝ)*E*(∑ i, (w i)^2) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem synthesis_norm_sq {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → H) :
    ‖∑ i, w i • u i‖^2 = ∑ i, ∑ j, w i*w j*inner ℝ (u i) (u j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (u j) (u i)]
  ring

/-- No positivity or invertibility of the leading matrix is required here. -/
theorem synthesis_bound_of_gram {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (u : ι → H) (C : ι → ι → ℝ)
    {L E : ℝ} (hE : 0 ≤ E)
    (he : ∀ i j, |inner ℝ (u i) (u j)-L*C i j| ≤ E) :
    ‖∑ i, w i • u i‖^2 ≤
      L*(∑ i, ∑ j, w i*w j*C i j) +
        (Fintype.card ι : ℝ)*E*(∑ i, (w i)^2) := by
  have hb := quadratic_error_le w (fun i j => inner ℝ (u i) (u j)-L*C i j) hE he
  have hd : (∑ i, ∑ j, w i*w j*(inner ℝ (u i) (u j)-L*C i j)) =
      (∑ i, ∑ j, w i*w j*inner ℝ (u i) (u j)) -
        L*(∑ i, ∑ j, w i*w j*C i j) := by
    calc
      _ = ∑ i, ∑ j, (w i*w j*inner ℝ (u i) (u j)-L*(w i*w j*C i j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hd] at hb
  rw [synthesis_norm_sq]
  have ht := (le_abs_self _).trans hb
  linarith

/-- Raw order: three binary packets, two ternary packets, two old packets. -/
def rawColumns (u : CellColumns H) (oldTwo oldThree : H) : Fin 7 → H :=
  ![u.x0, u.x1, u.x2, u.y0, u.y1, oldTwo, oldThree]

/-- The exact seven-by-seven leading coefficient matrix before correction. -/
def leadingGram : Fin 7 → Fin 7 → ℝ :=
  ![![1, 0, 0, 2/3, 0, 1/3, 0],
    ![0, 1, 0, 1/3, 1/3, 1/3, 0],
    ![0, 0, 1, 0, 2/3, 1/3, 0],
    ![2/3, 1/3, 0, 2, 0, 0, 1],
    ![0, 1/3, 2/3, 0, 2, 0, 1],
    ![1/3, 1/3, 1/3, 0, 0, 1, 0],
    ![0, 0, 0, 1, 1, 0, 2]]

/-- Subtract the leading optimal amount of each old packet. -/
def liftedCoefficients (a : CellVector) : Fin 7 → ℝ :=
  ![a.x0, a.x1, a.x2, a.y0, a.y1, -binarySum a/3, -ternarySum a/2]

def correctedSynthesis (u : CellColumns H) (oldTwo oldThree : H)
    (a : CellVector) : H :=
  synthesis u a - (binarySum a/3) • oldTwo - (ternarySum a/2) • oldThree

theorem correctedSynthesis_eq_sum (u : CellColumns H) (oldTwo oldThree : H)
    (a : CellVector) :
    correctedSynthesis u oldTwo oldThree a =
      ∑ i, liftedCoefficients a i • rawColumns u oldTwo oldThree i := by
  simp [correctedSynthesis, liftedCoefficients, rawColumns, synthesis,
    Fin.sum_univ_succ, neg_div, neg_smul]
  abel

/-- The finite Schur correction produces exactly the existing four-square form. -/
theorem leading_quadratic_eq_energy (a : CellVector) :
    (∑ i, ∑ j, liftedCoefficients a i*liftedCoefficients a j*leadingGram i j) =
      energy a := by
  simp [Fin.sum_univ_succ, liftedCoefficients, leadingGram,
    energy, binarySum, ternarySum]
  ring

theorem lifted_size (a : CellVector) :
    (∑ i, (liftedCoefficients a i)^2) =
      sizeSq a+(binarySum a)^2/9+(ternarySum a)^2/4 := by
  simp [Fin.sum_univ_succ, liftedCoefficients, sizeSq]
  ring

/-- The old-coordinate correction increases coefficient size by at most 3/2. -/
theorem lifted_size_le (a : CellVector) :
    (∑ i, (liftedCoefficients a i)^2) ≤ (3:ℝ)/2*sizeSq a := by
  rw [lifted_size]
  have hi : (3:ℝ)/2*sizeSq a-
      (sizeSq a+(binarySum a)^2/9+(ternarySum a)^2/4) =
      (a.x0^2+a.x1^2+a.x2^2)/6 +
        ((a.x0-a.x1)^2+(a.x0-a.x2)^2+(a.x1-a.x2)^2)/9 +
        (a.y0-a.y1)^2/4 := by
    unfold sizeSq binarySum ternarySum
    ring
  have hn : 0 ≤ (3:ℝ)/2*sizeSq a-
      (sizeSq a+(binarySum a)^2/9+(ternarySum a)^2/4) := by
    rw [hi]
    positivity
  linarith

/-- Uniform raw entry errors give an explicit bounded correction to the leading energy. -/
theorem correctedSynthesis_bound (u : CellColumns H) (oldTwo oldThree : H)
    {L E : ℝ} (hE : 0 ≤ E)
    (he : ∀ i j, |inner ℝ (rawColumns u oldTwo oldThree i)
        (rawColumns u oldTwo oldThree j)-L*leadingGram i j| ≤ E)
    (a : CellVector) :
    ‖correctedSynthesis u oldTwo oldThree a‖^2 ≤
      L*energy a+(21:ℝ)/2*E*sizeSq a := by
  have hb := synthesis_bound_of_gram (liftedCoefficients a)
    (rawColumns u oldTwo oldThree) leadingGram hE he
  rw [leading_quadratic_eq_energy] at hb
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at hb
  have hm := mul_le_mul_of_nonneg_left (lifted_size_le a)
    (show 0 ≤ (7:ℝ)*E by positivity)
  rw [correctedSynthesis_eq_sum]
  nlinarith

variable (P : Submodule ℝ H) [P.HasOrthogonalProjection]

/-- Full screening can only improve the explicit correction by the two old packets. -/
theorem screened_synthesis_le_corrected (u : CellColumns H) (oldTwo oldThree : H)
    (hTwo : oldTwo ∈ P) (hThree : oldThree ∈ P) (a : CellVector) :
    ‖residual P (synthesis u a)‖^2 ≤
      ‖correctedSynthesis u oldTwo oldThree a‖^2 := by
  let y := (binarySum a/3) • oldTwo+(ternarySum a/2) • oldThree
  have hy : y ∈ P := P.add_mem (P.smul_mem _ hTwo) (P.smul_mem _ hThree)
  have hp := refit_pythagoras P (synthesis u a) y 0 hy
  have hz : residual P (0 : H) = 0 := by
    simp [RiemannResearch.Analysis.ProjectionSourceImprovement.residual]
  simp only [add_zero, hz, sub_zero, map_zero] at hp
  have hi : synthesis u a-y = correctedSynthesis u oldTwo oldThree a := by
    unfold y correctedSynthesis
    abel
  rw [hi] at hp
  nlinarith [sq_nonneg ‖P.starProjection (synthesis u a)-y‖]

/-- Concrete seven-entry input for the sharp `7/3` source-gain theorem. -/
theorem screened_synthesis_leading_bound (u : CellColumns H) (oldTwo oldThree : H)
    (hTwo : oldTwo ∈ P) (hThree : oldThree ∈ P)
    {L E : ℝ} (hE : 0 ≤ E)
    (he : ∀ i j, |inner ℝ (rawColumns u oldTwo oldThree i)
        (rawColumns u oldTwo oldThree j)-L*leadingGram i j| ≤ E)
    (a : CellVector) :
    ‖residual P (synthesis u a)‖^2 ≤
      L*energy a+(21:ℝ)/2*E*sizeSq a :=
  (screened_synthesis_le_corrected P u oldTwo oldThree hTwo hThree a).trans
    (correctedSynthesis_bound u oldTwo oldThree hE he a)

variable (W : Submodule ℝ H) [W.HasOrthogonalProjection]

/-- The seven raw entry estimates feed directly into the actual enlarged gain. -/
theorem enlarged_gain_of_raw_gram (hPW : P ≤ W) (b : H)
    (u : CellColumns H) (hu : ColumnsIn W u)
    (hh : Compatible (source P b u)) (oldTwo oldThree : H)
    (hTwo : oldTwo ∈ P) (hThree : oldThree ∈ P)
    {L E : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hC : 0 < (7:ℝ)/3*L+(21:ℝ)/2*E)
    (he : ∀ i j, |inner ℝ (rawColumns u oldTwo oldThree i)
        (rawColumns u oldTwo oldThree j)-L*leadingGram i j| ≤ E) :
    sizeSq (source P b u)/((7:ℝ)/3*L+(21:ℝ)/2*E) ≤
      ‖residual P b‖^2-‖residual W b‖^2 := by
  apply enlarged_gain_lower_of_leading_bound P W hPW b u hu hh hL hC
  intro a ha
  exact screened_synthesis_leading_bound P u oldTwo oldThree hTwo hThree hE he a

end
end RiemannResearch.Analysis.ResonanceLeadingGram

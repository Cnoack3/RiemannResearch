/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteTwistedMoment
import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual nonstandard mollifier's exact finite second moment

Source for the coefficient and cutoff conventions: Baluyot (2017),
On the Zeros of Riemann's Zeta-function, (1.2.6)-(1.2.7) and Section 3.3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The finite expansion proposed in the user-provided continuation is proved
for the actual coefficients, with sigma and the evaluation line distinct.
The signed off-diagonal is retained. The final iff isolates precisely the
remaining estimate; it does not supply an arithmetic provider or RH.
-/
noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot
private theorem nat_cpow_vertical (n : ℕ) (hn : 0 < n) (ell t : ℝ) :
    (n : ℂ) ^ (-((ell : ℂ) + I * t)) =
    (Real.exp (-Real.log n * ell) : ℂ) * Complex.exp (-I * t * Real.log n) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [show Complex.log (n : ℂ) = (Real.log n : ℂ) by norm_cast]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring


def mollifierAmplitude (σ y l : ℝ) (n : ℕ) : ℂ :=
  mollifierCoefficient σ y n * ((n : ℝ) ^ (-l) : ℝ)

theorem nonstandardMollifier_vertical_eq_sum (σ y ε l t : ℝ) :
    nonstandardMollifier σ y ε ((l : ℂ) + (t : ℂ) * I) =
      ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        mollifierAmplitude σ y l n * exp (I * t * (-Real.log n)) := by
  unfold nonstandardMollifier
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [show (l : ℂ) + (t : ℂ) * I = (l : ℂ) + I * t by ring,
    nat_cpow_vertical n hnpos l t]
  unfold mollifierAmplitude
  rw [Real.rpow_def_of_pos (by exact_mod_cast hnpos)]
  have he : -Real.log (n : ℝ) * l = Real.log n * (-l) := by ring
  rw [he]
  have hp : exp (-I * (t : ℂ) * (Real.log n : ℂ)) =
      exp (I * (t : ℂ) * (-Real.log n : ℝ)) := by
    congr 1
    push_cast
    ring
  rw [hp]
  simp only [Complex.ofReal_neg]
  ring

private theorem continuousOn_zeta_vertical (l : ℝ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ContinuousOn (fun t : ℝ => riemannZeta ((l : ℂ) + (t : ℂ) * I)) (uIcc u v) := by
  rw [uIcc_of_le huv]
  intro t ht
  have hs : (l : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    linarith [ht.1]
  exact (ContinuousAt.comp (g := riemannZeta)
    (f := fun t : ℝ => (l : ℂ) + (t : ℂ) * I)
    (analyticAt_riemannZeta hs).continuousAt
    (show ContinuousAt (fun t : ℝ => (l : ℂ) + (t : ℂ) * I) t by fun_prop)).continuousWithinAt

/-- Exact finite twisted moment, for the actual cutoff and coefficients. -/
theorem mollifiedZeta_secondMoment_eq_twisted (σ y ε l : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    ((∫ t in u..v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
          mollifierAmplitude σ y l m * star (mollifierAmplitude σ y l n) *
            Complex.finiteTwistedMoment
              (fun t => riemannZeta ((l : ℂ) + (t : ℂ) * I))
              u v (Real.log n - Real.log m) := by
  simp_rw [mollifiedZeta, nonstandardMollifier_vertical_eq_sum]
  simpa only [neg_sub_neg, Complex.ofReal_neg] using Complex.integral_finite_sum_norm_sq
    (Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊) (mollifierAmplitude σ y l)
    (fun n => -Real.log n)
    (fun t => riemannZeta ((l : ℂ) + (t : ℂ) * I)) u v
    (continuousOn_zeta_vertical l hu huv)


theorem mollifierAmplitude_mul_star (σ y l : ℝ) (m n : ℕ) :
    mollifierAmplitude σ y l m * star (mollifierAmplitude σ y l n) =
      mollifierCoefficient σ y m * star (mollifierCoefficient σ y n) *
        (((m : ℝ) * (n : ℝ)) ^ (-l) : ℝ) := by
  simp only [mollifierAmplitude, star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), Complex.ofReal_mul]
  ring

theorem mollifierAmplitude_norm_sq (σ y l : ℝ) (n : ℕ) :
    ‖mollifierAmplitude σ y l n‖ ^ 2 =
      ‖mollifierCoefficient σ y n‖ ^ 2 * (n : ℝ) ^ (-2*l) := by
  rw [mollifierAmplitude, norm_mul,
    Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_pow]
  congr 1
  rw [show -2*l = (-l)*2 by ring, Real.rpow_mul (Nat.cast_nonneg n), Real.rpow_two]

def mollifiedSecondMomentDiagonal (σ y ε l u v : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
    ‖mollifierCoefficient σ y n‖ ^ 2 * (n : ℝ) ^ (-2*l)) *
    ∫ t in u..v, ‖riemannZeta ((l : ℂ) + (t : ℂ)*I)‖ ^ 2

def mollifiedSecondMomentOffDiagonal (σ y ε l u v : ℝ) : ℂ :=
  Complex.finiteTwistedOffDiagonal (Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊)
    (mollifierAmplitude σ y l) (fun n => -Real.log n)
    (fun t => riemannZeta ((l : ℂ) + (t : ℂ)*I)) u v

theorem mollifiedZeta_secondMoment_eq_diagonal_add (σ y ε l : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ^ 2) =
      mollifiedSecondMomentDiagonal σ y ε l u v +
        (mollifiedSecondMomentOffDiagonal σ y ε l u v).re := by
  have h := congrArg Complex.re (Complex.integral_finite_sum_norm_sq_diagonal
    (Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊) (mollifierAmplitude σ y l)
    (fun n => -Real.log n) (fun t => riemannZeta ((l : ℂ) + (t : ℂ)*I))
    u v (continuousOn_zeta_vertical l hu huv))
  simpa only [Complex.ofReal_re, Complex.add_re, mollifierAmplitude_norm_sq,
    mollifiedSecondMomentDiagonal, mollifiedSecondMomentOffDiagonal, mollifiedZeta,
    nonstandardMollifier_vertical_eq_sum, Complex.ofReal_neg] using h

theorem mollifiedZeta_secondMoment_le_iff_offDiagonal (σ y ε l E : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ^ 2) ≤ v-u+E ↔
      (mollifiedSecondMomentOffDiagonal σ y ε l u v).re ≤
        v-u+E-mollifiedSecondMomentDiagonal σ y ε l u v := by
  rw [mollifiedZeta_secondMoment_eq_diagonal_add σ y ε l hu huv]
  constructor <;> intro h <;> linarith


/-- The handoff's expansion, including its exact real power and phase sign. -/
theorem mollifiedZeta_secondMoment_eq_twisted_coefficients (σ y ε l : ℝ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    ((∫ t in u..v, ‖mollifiedZeta σ y ε ((l : ℂ) + (t : ℂ)*I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
        ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊,
          mollifierCoefficient σ y m * star (mollifierCoefficient σ y n) *
            (((m : ℝ)*(n : ℝ)) ^ (-l) : ℝ) *
            Complex.finiteTwistedMoment (fun t => riemannZeta ((l : ℂ)+(t : ℂ)*I))
              u v (Real.log n - Real.log m) := by
  simpa only [mollifierAmplitude_mul_star] using
    mollifiedZeta_secondMoment_eq_twisted σ y ε l hu huv
end RiemannResearch.Analysis.ConreyBaluyot

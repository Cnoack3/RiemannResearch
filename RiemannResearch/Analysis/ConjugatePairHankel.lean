/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.HankelMomentPositivity
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
An exact finite obstruction from one nonreal conjugate pair.

The moment `2 * re (v * z^k)` is the sum of the weighted atoms at `z` and
its conjugate when the conjugate atom has the conjugate weight. Its first
two-by-two Hankel determinant is negative for every nonzero weight and
every nonreal node. Gaussian weights are included as a specialization.

These statements concern an isolated conjugate pair, not the full infinite
zeta-zero moment form. The last theorem records an explicit entrywise tail
budget needed to preserve a finite negative direction after adding moments.
No analytic identification or vanishing-tail provider is asserted.
Source: independently developed finite algebra continuing the user-provided
`Ordinate_Harmonic_Theory_20261010(1).md`, Appendix II. The negative-direction
argument uses the existing `HankelMomentPositivity` API.
-/

namespace RiemannResearch.Analysis.ConjugatePairHankel

open RiemannResearch.Analysis.HankelMomentPositivity

/-- The real moments of an isolated node together with its conjugate. -/
def pairMoment (v z : ℂ) (k : ℕ) : ℝ :=
  2 * (v * z ^ k).re

/-- The conjugate-pair determinant retains both real and imaginary weights. -/
theorem pairMoment_determinant (v z : ℂ) :
    pairMoment v z 0 * pairMoment v z 2 - pairMoment v z 1 ^ 2 =
      -4 * (v.re ^ 2 + v.im ^ 2) * z.im ^ 2 := by
  simp only [pairMoment, pow_zero, pow_one, mul_one, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Every nonreal pair with nonzero weight has a strictly negative determinant. -/
theorem pairMoment_determinant_neg {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    pairMoment v z 0 * pairMoment v z 2 - pairMoment v z 1 ^ 2 < 0 := by
  have hvpos : 0 < v.re ^ 2 + v.im ^ 2 := by
    by_cases hre : v.re = 0
    · have him : v.im ≠ 0 := by
        intro him
        apply hv
        apply Complex.ext
        · simpa using hre
        · simpa using him
      simpa [hre] using sq_pos_of_ne_zero him
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hre) (sq_nonneg v.im)
  have hzpos : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  rw [pairMoment_determinant]
  nlinarith only [mul_pos hvpos hzpos]

/-- A pair obstruction gives a real two-coordinate quadratic witness. -/
theorem pairMoment_negative_witness {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    ∃ x y : ℝ,
      pairMoment v z 0 * x ^ 2 + 2 * pairMoment v z 1 * x * y +
        pairMoment v z 2 * y ^ 2 < 0 :=
  exists_negative_direction_of_det_neg (pairMoment_determinant_neg hv hz)

theorem pairMoment_not_PSD2 {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    ¬ PSD2 (pairMoment v z 0) (pairMoment v z 1) (pairMoment v z 2) := by
  intro h
  obtain ⟨x, y, hneg⟩ := pairMoment_negative_witness hv hz
  exact (not_le_of_gt hneg) (h x y)

/-- The obstruction already occurs in the unshifted size-two Hankel form. -/
theorem pairMoment_not_FinitePSD {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    ¬ FinitePSD (fun i j : Fin 2 => pairMoment v z (i.val + j.val)) := by
  intro h
  obtain ⟨x, y, hneg⟩ := pairMoment_negative_witness hv hz
  have hh := h (fun i : Fin 2 => if i.val = 0 then x else y)
  simp only [Fin.sum_univ_two] at hh
  norm_num at hh
  nlinarith only [hh, hneg]

theorem pairMoment_not_shiftedHankelPSD {v z : ℂ} (hv : v ≠ 0) (hz : z.im ≠ 0) :
    ¬ ShiftedHankelPSD (pairMoment v z) := by
  intro h
  apply pairMoment_not_PSD2 hv hz
  simpa using hankel_pair h 0

/-- Gaussian weights remain nonzero, independently of the smoothing parameter. -/
theorem gaussianPair_negative_witness (a : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ x y : ℝ,
      pairMoment (Complex.exp (-(a : ℂ) * z ^ 2)) z 0 * x ^ 2 +
        2 * pairMoment (Complex.exp (-(a : ℂ) * z ^ 2)) z 1 * x * y +
        pairMoment (Complex.exp (-(a : ℂ) * z ^ 2)) z 2 * y ^ 2 < 0 :=
  pairMoment_negative_witness (Complex.exp_ne_zero _) hz

/-- Exact contamination budget for a fixed two-coordinate negative witness. -/
theorem negative_witness_of_entrywise_tail_bound
    (m tail : ℕ → ℝ) (x y ε : ℝ)
    (h0 : |tail 0| ≤ ε) (h1 : |tail 1| ≤ ε) (h2 : |tail 2| ≤ ε)
    (hmargin : m 0 * x ^ 2 + 2 * m 1 * x * y + m 2 * y ^ 2 <
      -ε * (|x| + |y|) ^ 2) :
    (m 0 + tail 0) * x ^ 2 + 2 * (m 1 + tail 1) * x * y +
      (m 2 + tail 2) * y ^ 2 < 0 := by
  have ht0 : tail 0 * x ^ 2 ≤ ε * x ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self (tail 0)).trans h0) (sq_nonneg x)
  have ht2 : tail 2 * y ^ 2 ≤ ε * y ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self (tail 2)).trans h2) (sq_nonneg y)
  have ht1 : tail 1 * x * y ≤ ε * |x| * |y| := by
    calc
      tail 1 * x * y ≤ |tail 1 * x * y| := le_abs_self _
      _ = |tail 1| * |x| * |y| := by rw [abs_mul, abs_mul]
      _ ≤ ε * |x| * |y| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 (abs_nonneg x)) (abs_nonneg y)
  have hbudget : ε * (|x| + |y|) ^ 2 =
      ε * x ^ 2 + 2 * ε * |x| * |y| + ε * y ^ 2 := by
    rw [add_sq, sq_abs, sq_abs]
    ring
  nlinarith only [ht0, ht1, ht2, hmargin, hbudget]

end RiemannResearch.Analysis.ConjugatePairHankel

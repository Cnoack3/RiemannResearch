import RiemannResearch.Analysis.InfiniteWeightedCauchy
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact signed noise certificates for complete weighted coordinate arrays

Source: full square expansion and weighted Cauchy--Schwarz, sixth transfer
program, 24 October 2026. Measurement errors need not be coordinates of an
ambient Hilbert vector. The complete signed cross series is kept explicitly.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.NoisyWeightedCoordinates

def arrayEnergy (w a : ℕ → ℝ) : ℝ := ∑' j, w j * (a j) ^ 2

def arrayPairing (w a e : ℕ → ℝ) : ℝ := ∑' j, w j * a j * e j

theorem arrayEnergy_nonneg (w a : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    0 ≤ arrayEnergy w a := tsum_nonneg (fun j => mul_nonneg (hw j) (sq_nonneg _))

theorem array_sum_summable (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    Summable (fun j => w j * (a j + e j) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (sq_nonneg _)) _
    ((ha.add he).mul_left 2)
  intro j
  nlinarith [mul_nonneg (hw j) (sq_nonneg (a j - e j))]

theorem array_pairing_summable (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    Summable (fun j => w j * a j * e j) := by
  apply (ha.add he).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (hw j) (sq_nonneg (a j - e j)),
    mul_nonneg (hw j) (sq_nonneg (a j + e j)),
    mul_nonneg (hw j) (sq_nonneg (a j)), mul_nonneg (hw j) (sq_nonneg (e j))]

/-- Full noisy energy, including the signed cross term and complete noise energy. -/
theorem array_add_exact (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    arrayEnergy w (fun j => a j + e j) =
      arrayEnergy w a + 2 * arrayPairing w a e + arrayEnergy w e := by
  have hp := array_pairing_summable w a e hw ha he
  unfold arrayEnergy arrayPairing
  calc
    _ = ∑' j, ((w j * (a j) ^ 2 + 2 * (w j * a j * e j)) + w j * (e j) ^ 2) := by
      apply tsum_congr
      intro j
      ring
    _ = _ := by rw [(ha.add (hp.mul_left 2)).tsum_add he, ha.tsum_add (hp.mul_left 2), tsum_mul_left]

theorem array_pairing_sq_le (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    (arrayPairing w a e) ^ 2 ≤ arrayEnergy w a * arrayEnergy w e := by
  apply InfiniteWeightedCauchy.weighted_tsum_cauchy
    (fun j => w j * a j * e j) (fun j => w j * (a j) ^ 2) (fun j => w j * (e j) ^ 2)
    (array_pairing_summable w a e hw ha he) ha he
    (fun j => mul_nonneg (hw j) (sq_nonneg _))
    (fun j => mul_nonneg (hw j) (sq_nonneg _))
  intro j
  exact le_of_eq (by ring)

theorem array_add_le (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    arrayEnergy w (fun j => a j + e j) ≤ 2 * arrayEnergy w a + 2 * arrayEnergy w e := by
  have h := (array_sum_summable w a e hw ha he).tsum_le_tsum
    (fun j => show w j * (a j + e j) ^ 2 ≤ 2 * (w j * (a j) ^ 2) + 2 * (w j * (e j) ^ 2) by
      nlinarith [mul_nonneg (hw j) (sq_nonneg (a j - e j))])
    ((ha.mul_left 2).add (he.mul_left 2))
  simpa only [arrayEnergy, (ha.mul_left 2).tsum_add (he.mul_left 2), tsum_mul_left] using h

theorem array_true_le_noisy (w a e : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (ha : Summable (fun j => w j * (a j) ^ 2))
    (he : Summable (fun j => w j * (e j) ^ 2)) :
    arrayEnergy w a ≤ 2 * arrayEnergy w (fun j => a j + e j) + 2 * arrayEnergy w e := by
  have hen : Summable (fun j => w j * (-e j) ^ 2) := by simpa only [neg_sq] using he
  have h := array_add_le w (fun j => a j + e j) (fun j => -e j) hw
    (array_sum_summable w a e hw ha he) hen
  simpa only [add_neg_cancel_right, arrayEnergy, neg_sq] using h

/-- Vanishing complete observation noise preserves zero-convergence in
both directions, without boundedness of the true signal energies. -/
theorem noisy_zero_iff {α : Type*} {l : Filter α}
    (W A E : α → ℕ → ℝ) (hw : ∀ i j, 0 ≤ W i j)
    (ha : ∀ i, Summable (fun j => W i j * (A i j) ^ 2))
    (he : ∀ i, Summable (fun j => W i j * (E i j) ^ 2))
    (hnoise : Tendsto (fun i => arrayEnergy (W i) (E i)) l (𝓝 0)) :
    Tendsto (fun i => arrayEnergy (W i) (fun j => A i j + E i j)) l (𝓝 0) ↔
      Tendsto (fun i => arrayEnergy (W i) (A i)) l (𝓝 0) := by
  constructor
  · intro h
    have hb : Tendsto (fun i => 2 * arrayEnergy (W i) (fun j => A i j + E i j) +
        2 * arrayEnergy (W i) (E i)) l (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (h.const_mul 2).add (hnoise.const_mul 2)
    exact squeeze_zero (fun i => arrayEnergy_nonneg _ _ (hw i))
      (fun i => array_true_le_noisy _ _ _ (hw i) (ha i) (he i)) hb
  · intro h
    have hb : Tendsto (fun i => 2 * arrayEnergy (W i) (A i) +
        2 * arrayEnergy (W i) (E i)) l (𝓝 0) := by
      simpa only [mul_zero, add_zero] using (h.const_mul 2).add (hnoise.const_mul 2)
    exact squeeze_zero (fun i => arrayEnergy_nonneg _ _ (hw i))
      (fun i => array_add_le _ _ _ (hw i) (ha i) (he i)) hb

end RiemannResearch.Analysis.NoisyWeightedCoordinates

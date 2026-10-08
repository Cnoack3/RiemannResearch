import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.StepCorrectionNorm
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Complete physical correction energies

The series below are the complete interval energies, with the first interval
retained as the scalar square.  No finite truncation or assumed assembly law
is used.  The only hypothesis on a step sequence is its finite Pareto energy.
The sharp transfer follows from the full signed source and the full residual
variance.

Source: Christian Noack, RH_CRT_Optimized_Gains_and_Uniform_Obstruction_20261007.md, correction-norm and tail-bracket sections. The norm assembly is derived from the literal integrals, rather than taken as a compatibility assumption.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.StepCorrectionNorm

open Pareto

/-- Complete energy of a step sequence on the intervals indexed from one. -/
def stepEnergy (h : ℕ → ℝ) : ℝ :=
  ∑' n, positiveWeight (n + 1) * (h n) ^ 2

/-- The literal signed source of the correction. -/
def correctionSource (h : ℕ → ℝ) : ℝ :=
  ∑' n, positiveWeight (n + 1) * h n * cellMean n

/-- Complete norm of the weighted cell means. -/
def projectionEnergy : ℝ := stepEnergy cellMean

/-- Complete fractional-part energy, including the interval from zero to one. -/
def residueEnergy : ℝ := 1 + ∑' n, rawResidueCellEnergy n

/-- Complete residual variance, including the interval from zero to one. -/
def residualEnergy : ℝ := 1 + ∑' n, centeredEnergy n

/-- The literal corrected integral over one whole positive cell. -/
def correctedCellEnergy (n : ℕ) (b a : ℝ) : ℝ :=
  ∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2),
    (b - a * (x - ((n : ℝ) + 1))) ^ 2 / x ^ 2

/-- The complete corrected norm square.  Its first cell contributes `a²`. -/
def correctedEnergy (h : ℕ → ℝ) (a : ℝ) : ℝ :=
  a ^ 2 + ∑' n, correctedCellEnergy n (h n) a

private theorem shifted_weight_summable :
    Summable (fun n => positiveWeight (n + 1)) :=
  (summable_nat_add_iff 1).2 positiveWeight_summable

private theorem shifted_weight_tsum :
    (∑' n, positiveWeight (n + 1)) = 1 := by
  simpa only [positiveWeight_succ] using paretoWeight_tsum

theorem projection_series_summable :
    Summable (fun n => positiveWeight (n + 1) * (cellMean n) ^ 2) := by
  apply shifted_weight_summable.of_norm_bounded
  intro n
  have hw := positiveWeight_nonneg (n + 1)
  have hc := cellMean_nonneg n
  have hc' := cellMean_le_one n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  have hsq : cellMean n ^ 2 ≤ (1 : ℝ) := by nlinarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq hw

/-- Finite step energy forces absolute convergence of the signed source. -/
theorem correctionSource_summable {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) :
    Summable (fun n => positiveWeight (n + 1) * h n * cellMean n) := by
  apply (hh.add shifted_weight_summable).of_norm_bounded
  intro n
  have hw := positiveWeight_nonneg (n + 1)
  have hc := cellMean_nonneg n
  have hc' := cellMean_le_one n
  have habs : |h n| ≤ (h n) ^ 2 + 1 := by
    have hs := sq_nonneg (|h n| - 1)
    have he : |h n| ^ 2 = (h n) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (h n)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg hw, abs_of_nonneg hc]
  calc
    positiveWeight (n + 1) * |h n| * cellMean n ≤
        positiveWeight (n + 1) * |h n| := by
      nlinarith [mul_nonneg hw (abs_nonneg (h n))]
    _ ≤ positiveWeight (n + 1) * (h n) ^ 2 + positiveWeight (n + 1) := by
      nlinarith [mul_nonneg hw (sub_nonneg.mpr habs)]

theorem shifted_step_series_summable {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    Summable (fun n => positiveWeight (n + 1) * (h n - a * cellMean n) ^ 2) := by
  have hs := (hh.sub ((correctionSource_summable hh).mul_left (2 * a))).add
    (projection_series_summable.mul_left (a ^ 2))
  apply hs.congr
  intro n
  ring

theorem shifted_step_energy {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    (∑' n, positiveWeight (n + 1) * (h n - a * cellMean n) ^ 2) =
      stepEnergy h - 2 * a * correctionSource h + a ^ 2 * projectionEnergy := by
  have hs := correctionSource_summable hh
  calc
    _ = ∑' n, ((positiveWeight (n + 1) * (h n) ^ 2 -
        (2 * a) * (positiveWeight (n + 1) * h n * cellMean n)) +
        a ^ 2 * (positiveWeight (n + 1) * (cellMean n) ^ 2)) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by
      rw [(hh.sub (hs.mul_left (2 * a))).tsum_add
          (projection_series_summable.mul_left (a ^ 2)),
        hh.tsum_sub (hs.mul_left (2 * a)),
        hs.tsum_mul_left (2 * a), projection_series_summable.tsum_mul_left (a ^ 2)]
      rfl

/-- Cauchy--Schwarz for the complete source, proved using the complete
nonnegative shifted energy rather than a finite source estimate. -/
theorem correctionSource_sq_le {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) :
    correctionSource h ^ 2 ≤ stepEnergy h * projectionEnergy := by
  have hp : ∀ a : ℝ, 0 ≤ projectionEnergy * (a * a) +
      (-2 * correctionSource h) * a + stepEnergy h := by
    intro a
    have hn : 0 ≤ (∑' n, positiveWeight (n + 1) *
        (h n - a * cellMean n) ^ 2) := tsum_nonneg (fun n => mul_nonneg
      (positiveWeight_nonneg (n + 1)) (sq_nonneg (h n - a * cellMean n)))
    rw [shifted_step_energy hh a] at hn
    nlinarith
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

/-- The literal residual series is the difference of the complete energies. -/
theorem residualEnergy_eq : residualEnergy = residueEnergy - projectionEnergy := by
  unfold residualEnergy residueEnergy projectionEnergy stepEnergy
  simp only [centeredEnergy]
  rw [rawResidueCellEnergy_summable.tsum_sub projection_series_summable]
  ring

theorem residualEnergy_ge_one : 1 ≤ residualEnergy := by
  unfold residualEnergy
  have hn : 0 ≤ (∑' n, centeredEnergy n) := tsum_nonneg centeredEnergy_nonneg
  linarith

theorem projectionEnergy_nonneg : 0 ≤ projectionEnergy := by
  exact tsum_nonneg (fun n => mul_nonneg
    (positiveWeight_nonneg (n + 1)) (sq_nonneg (cellMean n)))

theorem projectionEnergy_le_one : projectionEnergy ≤ 1 := by
  have hle : ∀ n, positiveWeight (n + 1) * (cellMean n) ^ 2 ≤
      positiveWeight (n + 1) := by
    intro n
    have hsq : cellMean n ^ 2 ≤ (1 : ℝ) := by
      nlinarith [cellMean_nonneg n, cellMean_le_one n]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq
      (positiveWeight_nonneg (n + 1))
  have hs := projection_series_summable.tsum_le_tsum hle shifted_weight_summable
  simpa only [projectionEnergy, stepEnergy, shifted_weight_tsum] using hs

theorem residueEnergy_pos : 0 < residueEnergy := by
  have hres := residualEnergy_ge_one
  rw [residualEnergy_eq] at hres
  linarith [projectionEnergy_nonneg]

/-- Absolute convergence of every complete corrected cell norm. -/
theorem correctedEnergy_summable {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    Summable (fun n => correctedCellEnergy n (h n) a) := by
  have hs := (shifted_step_series_summable hh a).add
    (centeredEnergy_summable.mul_left (a ^ 2))
  apply hs.congr
  intro n
  exact (scaled_cell_error_energy n (h n) a).symm

/-- The exact complete orthogonal split, including all infinitely many cells
and the correction square on the interval from zero to one. -/
theorem correctedEnergy_orthogonal_split {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    correctedEnergy h a =
      (∑' n, positiveWeight (n + 1) * (h n - a * cellMean n) ^ 2) +
        a ^ 2 * residualEnergy := by
  unfold correctedEnergy correctedCellEnergy
  simp_rw [scaled_cell_error_energy]
  rw [(shifted_step_series_summable hh a).tsum_add
    (centeredEnergy_summable.mul_left (a ^ 2)),
    centeredEnergy_summable.tsum_mul_left (a ^ 2)]
  unfold residualEnergy
  ring

/-- The complete signed norm assembly, with the actual convergent source. -/
theorem correctedEnergy_assembly {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    correctedEnergy h a = stepEnergy h - 2 * a * correctionSource h +
      a ^ 2 * residueEnergy := by
  rw [correctedEnergy_orthogonal_split hh a, shifted_step_energy hh a,
    residualEnergy_eq]
  ring

/-- Completion in the actual scalar charge, retaining its full square. -/
theorem correctedEnergy_completed_square {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    correctedEnergy h a = stepEnergy h - correctionSource h ^ 2 / residueEnergy +
      residueEnergy * (a - correctionSource h / residueEnergy) ^ 2 := by
  rw [correctedEnergy_assembly hh a]
  field_simp [ne_of_gt residueEnergy_pos]
  <;> ring

/-- Exact transfer gap: a charge square and the complete Cauchy gap. -/
theorem correctedEnergy_transfer_gap {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    residueEnergy * correctedEnergy h a - residualEnergy * stepEnergy h =
      (residueEnergy * a - correctionSource h) ^ 2 +
        (stepEnergy h * projectionEnergy - correctionSource h ^ 2) := by
  rw [correctedEnergy_assembly hh a, residualEnergy_eq]
  ring

/-- The denominator-cleared sharp transfer for every finite-energy step. -/
theorem correctedEnergy_transfer_mul {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    residualEnergy * stepEnergy h ≤ residueEnergy * correctedEnergy h a := by
  have hg := correctedEnergy_transfer_gap hh a
  have hc := correctionSource_sq_le hh
  nlinarith [sq_nonneg (residueEnergy * a - correctionSource h)]

/-- The exact sharp structural transfer with a proved positive denominator. -/
theorem correctedEnergy_transfer {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    stepEnergy h ≤ (residueEnergy / residualEnergy) * correctedEnergy h a := by
  have hpos : 0 < residualEnergy := by linarith [residualEnergy_ge_one]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).2
  simpa only [mul_comm] using correctedEnergy_transfer_mul hh a

/-- The interval from zero to one forces a charge-square lower bound; no
positive-cell contribution is needed to cover the charge. -/
theorem correctedEnergy_charge_sq_le {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    a ^ 2 ≤ correctedEnergy h a := by
  rw [correctedEnergy_orthogonal_split hh a]
  have hs : 0 ≤ (∑' n, positiveWeight (n + 1) *
      (h n - a * cellMean n) ^ 2) := tsum_nonneg (fun n => mul_nonneg
    (positiveWeight_nonneg (n + 1)) (sq_nonneg (h n - a * cellMean n)))
  nlinarith [residualEnergy_ge_one, sq_nonneg a]

/-- The actual source divided by the actual complete residue energy is the
best scalar charge. -/
theorem correctedEnergy_minimizer {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    correctedEnergy h (correctionSource h / residueEnergy) ≤ correctedEnergy h a := by
  rw [correctedEnergy_completed_square hh a,
    correctedEnergy_completed_square hh (correctionSource h / residueEnergy)]
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  exact le_add_of_nonneg_right (mul_nonneg (le_of_lt residueEnergy_pos) (sq_nonneg _))

/-- The complete minimum over the scalar charge, retaining the exact signed source. -/
theorem correctedEnergy_minimum {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) :
    correctedEnergy h (correctionSource h / residueEnergy) =
      stepEnergy h - correctionSource h ^ 2 / residueEnergy := by
  rw [correctedEnergy_completed_square hh (correctionSource h / residueEnergy)]
  simp

/-- The complete weighted means are an equality witness, establishing
sharpness on the full finite-energy step space. -/
theorem correctedEnergy_transfer_equality :
    residueEnergy * correctedEnergy cellMean (projectionEnergy / residueEnergy) =
      residualEnergy * projectionEnergy := by
  have hsource : correctionSource cellMean = projectionEnergy := by
    unfold correctionSource projectionEnergy stepEnergy
    apply tsum_congr
    intro n
    ring
  rw [correctedEnergy_assembly projection_series_summable
      (projectionEnergy / residueEnergy), hsource]
  change residueEnergy * (projectionEnergy - 2 *
      (projectionEnergy / residueEnergy) * projectionEnergy +
      (projectionEnergy / residueEnergy) ^ 2 * residueEnergy) =
    residualEnergy * projectionEnergy
  rw [residualEnergy_eq]
  field_simp [ne_of_gt residueEnergy_pos]
  <;> ring

/-- The scalar complete step energy is exactly the canonical Hilbert norm. -/
theorem stepEnergy_hilbert (f : ThresholdHilbert) :
    stepEnergy (fun n => hilbertSequence f (n + 1)) = ‖f‖ ^ 2 := by
  unfold stepEnergy
  simp_rw [hilbertSequence_weighted_square]
  exact (hilbert_norm_sq f).symm

/-- Complete correction assembly for every vector of the actual step Hilbert space. -/
theorem correctedEnergy_hilbert (f : ThresholdHilbert) (a : ℝ) :
    correctedEnergy (fun n => hilbertSequence f (n + 1)) a =
      ‖f‖ ^ 2 - 2 * a * correctionSource (fun n => hilbertSequence f (n + 1)) +
        a ^ 2 * residueEnergy := by
  have hh : Summable (fun n => positiveWeight (n + 1) *
      (hilbertSequence f (n + 1)) ^ 2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  rw [correctedEnergy_assembly hh a, stepEnergy_hilbert]

/-- A proved global bound on the complete projection norm. -/
theorem projectionEnergy_le_quarter : projectionEnergy ≤ 1 / 4 := by
  have hle : ∀ n, positiveWeight (n + 1) * (cellMean n) ^ 2 ≤
      (1 / 4 : ℝ) * positiveWeight (n + 1) := by
    intro n
    have hc := cellMean_nonneg n
    have hc' := cellMean_le_half n
    have hw := positiveWeight_nonneg (n + 1)
    have hs : cellMean n ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hs)]
  have hs := projection_series_summable.tsum_le_tsum hle
    (shifted_weight_summable.mul_left (1 / 4 : ℝ))
  rw [shifted_weight_summable.tsum_mul_left (1 / 4 : ℝ), shifted_weight_tsum] at hs
  simpa only [projectionEnergy, stepEnergy, mul_one] using hs

/-- A uniform explicit bound for the exact structural factor. -/
theorem correctionTransferFactor_le_four_thirds :
    residueEnergy / residualEnergy ≤ 4 / 3 := by
  have hb : 0 < residualEnergy := by linarith [residualEnergy_ge_one]
  have hC : 1 ≤ residueEnergy := by
    have hr := residualEnergy_ge_one
    rw [residualEnergy_eq] at hr
    linarith [projectionEnergy_nonneg]
  apply (div_le_iff₀ hb).2
  rw [residualEnergy_eq]
  nlinarith [projectionEnergy_le_quarter]

/-- A concrete uniform squared-norm transfer, stronger than a generic
compatibility theorem: its complete analytic denominator is proved positive. -/
theorem correctedEnergy_transfer_four_thirds {h : ℕ → ℝ}
    (hh : Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2)) (a : ℝ) :
    stepEnergy h ≤ (4 / 3 : ℝ) * correctedEnergy h a := by
  have he : 0 ≤ correctedEnergy h a :=
    le_trans (sq_nonneg a) (correctedEnergy_charge_sq_le hh a)
  exact (correctedEnergy_transfer hh a).trans
    (mul_le_mul_of_nonneg_right correctionTransferFactor_le_four_thirds he)


-- This section needs `import RiemannResearch.RH.NearbyDilationGram`.

/-- A rigorous upper bound on the complete projection tail. -/
theorem projectionEnergy_tail_le (N : ℕ) :
    (∑' n, positiveWeight (n + N + 1) * (cellMean (n + N)) ^ 2) ≤
      1 / (4 * ((N : ℝ) + 1)) := by
  have hp : Summable (fun n => positiveWeight (n + N + 1) *
      (cellMean (n + N)) ^ 2) :=
    (summable_nat_add_iff N).2 projection_series_summable
  have hw : Summable (fun n => positiveWeight (n + N + 1)) :=
    (summable_nat_add_iff N).2 shifted_weight_summable
  have hle : ∀ n, positiveWeight (n + N + 1) * (cellMean (n + N)) ^ 2 ≤
      (1 / 4 : ℝ) * positiveWeight (n + N + 1) := by
    intro n
    have hs : cellMean (n + N) ^ 2 ≤ (1 / 4 : ℝ) := by
      nlinarith [cellMean_nonneg (n + N), cellMean_le_half (n + N)]
    nlinarith [mul_nonneg (positiveWeight_nonneg (n + N + 1)) (sub_nonneg.mpr hs)]
  have hb := hp.tsum_le_tsum hle (hw.mul_left (1 / 4 : ℝ))
  rw [hw.tsum_mul_left (1 / 4 : ℝ)] at hb
  have hmass : (∑' n, positiveWeight (n + N + 1)) = 1 / ((N : ℝ) + 1) := by
    simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      positiveWeight_tail_tsum (N + 1) (Nat.succ_pos N)
  rw [hmass] at hb
  have heq : (1 / 4 : ℝ) * (1 / ((N : ℝ) + 1)) =
      1 / (4 * ((N : ℝ) + 1)) := by
    field_simp
    <;> ring
  rw [heq] at hb
  exact hb

/-- Every finite prefix certifies both sides of the actual complete projection norm. -/
theorem projectionEnergy_prefix_bracket (N : ℕ) :
    (∑ n ∈ Finset.range N, positiveWeight (n + 1) * (cellMean n) ^ 2) ≤
        projectionEnergy ∧
      projectionEnergy ≤
        (∑ n ∈ Finset.range N, positiveWeight (n + 1) * (cellMean n) ^ 2) +
          1 / (4 * ((N : ℝ) + 1)) := by
  have hd := projection_series_summable.sum_add_tsum_nat_add N
  have hn : 0 ≤ (∑' n, positiveWeight (n + N + 1) * (cellMean (n + N)) ^ 2) :=
    tsum_nonneg (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  change (∑ n ∈ Finset.range N, positiveWeight (n + 1) * (cellMean n) ^ 2) +
      (∑' n, positiveWeight (n + N + 1) * (cellMean (n + N)) ^ 2) = projectionEnergy at hd
  constructor <;> linarith [projectionEnergy_tail_le N]

private theorem cellSeries_tail_bound {f : ℕ → ℝ}
    (hf : Summable f) (hn : ∀ n, 0 ≤ f n)
    (hb : ∀ n, f n ≤ positiveWeight (n + 1) / 3) (N : ℕ) :
    0 ≤ (∑' n, f (n + N)) ∧
      (∑' n, f (n + N)) ≤ 1 / (3 * ((N : ℝ) + 1)) := by
  have hs : Summable (fun n => f (n + N)) := (summable_nat_add_iff N).2 hf
  have hw : Summable (fun n => positiveWeight (n + N + 1)) :=
    (summable_nat_add_iff N).2 shifted_weight_summable
  constructor
  · exact tsum_nonneg (fun n => hn (n + N))
  · have hle : ∀ n, f (n + N) ≤ (1 / 3 : ℝ) * positiveWeight (n + N + 1) := by
      intro n
      convert hb (n + N) using 1 <;> ring
    have ht := hs.tsum_le_tsum hle (hw.mul_left (1 / 3 : ℝ))
    rw [hw.tsum_mul_left (1 / 3 : ℝ)] at ht
    have hmass : (∑' n, positiveWeight (n + N + 1)) = 1 / ((N : ℝ) + 1) := by
      simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
        positiveWeight_tail_tsum (N + 1) (Nat.succ_pos N)
    rw [hmass] at ht
    have heq : (1 / 3 : ℝ) * (1 / ((N : ℝ) + 1)) =
        1 / (3 * ((N : ℝ) + 1)) := by
      field_simp
      <;> ring
    rw [heq] at ht
    exact ht

/-- Retaining the interval from zero to one yields a complete two-sided norm
certificate from every finite raw-cell prefix. -/
theorem residueEnergy_prefix_bracket (N : ℕ) :
    1 + (∑ n ∈ Finset.range N, rawResidueCellEnergy n) ≤ residueEnergy ∧
      residueEnergy ≤ 1 + (∑ n ∈ Finset.range N, rawResidueCellEnergy n) +
        1 / (3 * ((N : ℝ) + 1)) := by
  have hd := rawResidueCellEnergy_summable.sum_add_tsum_nat_add N
  have ht := cellSeries_tail_bound rawResidueCellEnergy_summable
    rawResidueCellEnergy_nonneg (fun n => (rawResidueCellEnergy_lt_third_weight n).le) N
  unfold residueEnergy
  constructor <;> linarith [ht.1, ht.2]

/-- Both sides of the complete residual variance are certified by every
finite centered-cell prefix. -/
theorem residualEnergy_prefix_bracket (N : ℕ) :
    1 + (∑ n ∈ Finset.range N, centeredEnergy n) ≤ residualEnergy ∧
      residualEnergy ≤ 1 + (∑ n ∈ Finset.range N, centeredEnergy n) +
        1 / (3 * ((N : ℝ) + 1)) := by
  have hd := centeredEnergy_summable.sum_add_tsum_nat_add N
  have ht := cellSeries_tail_bound centeredEnergy_summable
    centeredEnergy_nonneg (fun n => (centeredEnergy_lt_third_weight n).le) N
  unfold residualEnergy
  constructor <;> linarith [ht.1, ht.2]


/-- The projection is a genuine nonzero vector of the complete step space. -/
theorem projectionEnergy_pos : 0 < projectionEnergy := by
  have hle : positiveWeight (0 + 1) * (cellMean 0) ^ 2 ≤ projectionEnergy := by
    simpa only [Finset.sum_singleton, projectionEnergy, stepEnergy] using
      projection_series_summable.sum_le_tsum ({0} : Finset ℕ)
        (fun n _ => mul_nonneg (positiveWeight_nonneg (n + 1)) (sq_nonneg _))
  have hw : 0 < positiveWeight (0 + 1) := by unfold positiveWeight; norm_num
  exact (mul_pos hw (sq_pos_of_pos (cellMean_pos 0))).trans_le hle

/-- Any factor valid for every finite-energy step and every scalar charge is
at least the exact factor.  This proves optimality, beyond displaying equality
on a potentially zero witness. -/
theorem correctionTransferFactor_minimal (K : ℝ)
    (hK : ∀ h : ℕ → ℝ,
      Summable (fun n => positiveWeight (n + 1) * (h n) ^ 2) →
        ∀ a : ℝ, stepEnergy h ≤ K * correctedEnergy h a) :
    residueEnergy / residualEnergy ≤ K := by
  have h := hK cellMean projection_series_summable (projectionEnergy / residueEnergy)
  change projectionEnergy ≤ K *
    correctedEnergy cellMean (projectionEnergy / residueEnergy) at h
  have hm : residueEnergy * projectionEnergy ≤ K * residualEnergy * projectionEnergy := by
    calc
      residueEnergy * projectionEnergy ≤ residueEnergy *
          (K * correctedEnergy cellMean (projectionEnergy / residueEnergy)) :=
        mul_le_mul_of_nonneg_left h (le_of_lt residueEnergy_pos)
      _ = K * (residueEnergy *
          correctedEnergy cellMean (projectionEnergy / residueEnergy)) := by ring
      _ = K * (residualEnergy * projectionEnergy) := by
        rw [correctedEnergy_transfer_equality]
      _ = K * residualEnergy * projectionEnergy := by ring
  have hb : 0 < residualEnergy := by linarith [residualEnergy_ge_one]
  apply (div_le_iff₀ hb).2
  exact (mul_le_mul_iff_of_pos_right projectionEnergy_pos).mp hm

/-- The exact sharp factor is strictly greater than one. -/
theorem correctionTransferFactor_gt_one : 1 < residueEnergy / residualEnergy := by
  have hb : 0 < residualEnergy := by linarith [residualEnergy_ge_one]
  apply (lt_div_iff₀ hb).2
  rw [one_mul, residualEnergy_eq]
  linarith [projectionEnergy_pos]


end RiemannResearch.RH.StepCorrectionNorm

import RiemannResearch.Analysis.ParetoPeriodicAbelTail
import RiemannResearch.RH.CenteredMeanGramTail
import RiemannResearch.RH.ParetoParityPeriodSection

/-!
# Exact periodic main term for the tail of a fixed digamma Gram section

For a fixed solve cutoff the residue sequence is periodic. Abel summation
gives the mean squared error over a full period and bounds the remainder
by one period's total mass times the first omitted point weight. The
period depends on the solve cutoff.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.PeriodicWeightedMean
open RiemannResearch.Analysis.ParetoPeriodicAbelTail

/-- On the period wrap the model uses the squared error against the scalar
one. The complete physical tail begins at a strictly positive site. -/
def sectionSquare (B k : ℕ) : ℝ := (sectionCoordinate (B + 1) k - 1) ^ 2

def sectionPeriodMean (B : ℕ) : ℝ :=
  partialSum (sectionSquare B) (Nat.lcmUpto (B + 2)) / (Nat.lcmUpto (B + 2) : ℝ)

private theorem sectionSquare_period (B k : ℕ) :
    sectionSquare B (k + Nat.lcmUpto (B + 2)) = sectionSquare B k := by
  simp only [sectionSquare, sectionCoordinate_eq,
    finiteSpace_lcmUpto_period (B+1) (packetUnitMean_legal B) k]

private theorem weighted_sectionSquare_coordinate (B N k : ℕ) :
    sectionSquare B (k + (N + 1)) * weight N k =
      ((hilbertTailShift (packetUnitMean B - hilbertOne) N) k) ^ 2 := by
  have hs := hilbertSequence_weighted_square (packetUnitMean B - hilbertOne) (k + N)
  change _ = ((packetUnitMean B - hilbertOne) (k + N)) ^ 2
  rw [← hs, positiveWeight_succ, hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence]
  simp only [zeroAnchor, sectionSquare, sectionCoordinate_eq,
    Nat.add_assoc]
  unfold weight paretoWeight
  push_cast
  ring

/-- The unit norm error on the periodic wrap gives a positive lower bound
for the full period mean, even when the ambient snake boundary vanishes. -/
theorem sectionPeriodMean_lower (B : ℕ) :
    1 / (Nat.lcmUpto (B + 2) : ℝ) ≤ sectionPeriodMean B := by
  let L := Nat.lcmUpto (B + 2)
  have hL : 0 < L := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)
  have hzero : sectionSquare B 0 = 1 := by simp [sectionSquare, sectionCoordinate_eq]
  have hsum := Finset.single_le_sum (f := sectionSquare B)
    (fun k (_ : k ∈ Finset.range L) => sq_nonneg _) (Finset.mem_range.mpr hL)
  change 1 / (L : ℝ) ≤ partialSum (sectionSquare B) L / (L : ℝ)
  rw [hzero] at hsum
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

/-- The relative normalized tail error at a fixed solve is at most one
period divided by `N + 2`. -/
theorem finiteSectionTailCost_period_error (B N : ℕ) :
    |((N : ℝ) + 1) * finiteSectionTailCost B N - sectionPeriodMean B| ≤
      (Nat.lcmUpto (B + 2) : ℝ) * sectionPeriodMean B / ((N : ℝ) + 2) := by
  let L := Nat.lcmUpto (B + 2)
  let μ := sectionPeriodMean B
  let f := sectionSquare B
  let a := fun k : ℕ => f (k + (N + 1))
  have hL : 0 < L := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero _)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hm : partialSum f L = (L : ℝ) * μ := by
    change partialSum f L = (L : ℝ) * (partialSum f L / (L : ℝ))
    field_simp [hLR.ne']
  have hμ : 0 ≤ μ := (by positivity : 0 ≤ 1 / (L : ℝ)).trans (sectionPeriodMean_lower B)
  have hper (k : ℕ) : a (k + L) = a k := by
    simpa only [a, f, L, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      sectionSquare_period B (k + (N + 1))
  have hblock : partialSum a L = (L : ℝ) * μ :=
    (period_sum_shift f L (N + 1) (sectionSquare_period B)).trans hm
  have hs : Summable (fun k : ℕ => a k * weight N k) := by
    simpa only [a, f, weighted_sectionSquare_coordinate] using
      (hilbert_coordinate_square_summable (hilbertTailShift (packetUnitMean B - hilbertOne) N))
  have hr := centered_error_bound a N μ ((L : ℝ) * μ) hs
    (nonnegative_periodic_discrepancy a L μ hL hμ (fun _ => sq_nonneg _) hper hblock)
  have htail : (∑' k : ℕ, a k * weight N k) = finiteSectionTailCost B N := by
    simp only [a, f, weighted_sectionSquare_coordinate, finiteSectionTailCost_eq, hilbert_norm_sq]
  rw [htail] at hr
  push_cast at hr
  have hN : 0 < (N : ℝ) + 1 := by positivity
  calc
    _ = ((N : ℝ) + 1) * |finiteSectionTailCost B N - μ / ((N : ℝ) + 1)| := by
      change |((N : ℝ) + 1) * finiteSectionTailCost B N - μ| = _
      have hdiff : ((N : ℝ) + 1) * finiteSectionTailCost B N - μ =
          ((N : ℝ) + 1) * (finiteSectionTailCost B N - μ / ((N : ℝ) + 1)) := by
        field_simp
      rw [hdiff, abs_mul, abs_of_pos hN]
    _ ≤ ((N : ℝ) + 1) *
        (((L : ℝ) * μ) / (((N : ℝ) + 1) * ((N : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hr hN.le
    _ = _ := by
      change ((N : ℝ) + 1) * _ = (L : ℝ) * μ / ((N : ℝ) + 2)
      field_simp

/-- The physical-cutoff limit for each finite solve is its exact finite
period mean. The period and the error bound may vary with the solve. -/
theorem scaled_finiteSectionTailCost_tendsto_periodMean (B : ℕ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) * finiteSectionTailCost B N) atTop
      (𝓝 (sectionPeriodMean B)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (2 : ℝ)
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have ht : Tendsto (fun N : ℕ => (Nat.lcmUpto (B + 2) : ℝ) * sectionPeriodMean B /
      ((N : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      hr.const_mul ((Nat.lcmUpto (B + 2) : ℝ) * sectionPeriodMean B)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by
    simpa only [Real.norm_eq_abs] using finiteSectionTailCost_period_error B N) ht

private theorem later_tail_vector (B A N : ℕ) :
    hilbertTailShift (packetUnitMean A - hilbertOne) N =
      hilbertTailShift (packetUnitMean B - hilbertOne) N -
        hilbertTailShift (packetUnitMean B - packetUnitMean A) N := by
  ext k
  change packetUnitMean A (k + N) - hilbertOne (k + N) = _
  change _ = (packetUnitMean B (k + N) - hilbertOne (k + N)) -
    (packetUnitMean B (k + N) - packetUnitMean A (k + N))
  ring

/-- The exact cost transfer between two Gram solves retains the signed
cross term and the norm of the change after the physical cutoff. -/
theorem later_finiteSectionTailCost_identity (B A N : ℕ) :
    finiteSectionTailCost A N = finiteSectionTailCost B N -
      2 * inner ℝ (hilbertTailShift (packetUnitMean B - hilbertOne) N)
        (hilbertTailShift (packetUnitMean B - packetUnitMean A) N) +
      ‖hilbertTailShift (packetUnitMean B - packetUnitMean A) N‖ ^ 2 := by
  rw [finiteSectionTailCost_eq, finiteSectionTailCost_eq, later_tail_vector B A N,
    norm_sub_sq_real]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection

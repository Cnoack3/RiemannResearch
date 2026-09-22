import RiemannResearch.RH.ThresholdHilbertMean
/-!
# The full Pareto L1 norm on the sequence Hilbert space

Source: the user's L2-to-L1 convergence argument, 22 September 2026.
The absolute-value vector realizes the complete weighted L1 norm as
a Hilbert pairing with the constant target. Cauchy--Schwarz gives
L1 <= L2 because the Pareto measure has total mass one.
These estimates apply to every actual ThresholdHilbert vector.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

private theorem abs_sequence_square_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * |hilbertSequence f k| ^ 2) := by
  simpa only [sq_abs] using hilbertSequence_square_summable f

def hilbertAbs (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (fun k => |hilbertSequence f k|) (abs_sequence_square_summable f)

theorem hilbertAbs_sequence (f : ThresholdHilbert) :
    hilbertSequence (hilbertAbs f) = fun k => |hilbertSequence f k| := by
  apply hilbertSequence_sequenceHilbert
  simp

theorem hilbertAbs_norm (f : ThresholdHilbert) : ‖hilbertAbs f‖ = ‖f‖ := by
  have h : ‖hilbertAbs f‖ ^ 2 = ‖f‖ ^ 2 := by
    simp only [hilbert_norm_weighted_sq, hilbertAbs_sequence, sq_abs]
  nlinarith [norm_nonneg (hilbertAbs f), norm_nonneg f]

/-- The complete Pareto L1 norm, with zero coordinate anchored. -/
def hilbertL1Norm (f : ThresholdHilbert) : ℝ :=
  ∑' k, positiveWeight k * |hilbertSequence f k|

theorem hilbertL1Norm_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * |hilbertSequence f k|) :=
  weighted_summable_of_square (abs_sequence_square_summable f)

theorem hilbertL1Norm_nonneg (f : ThresholdHilbert) : 0 ≤ hilbertL1Norm f :=
  tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k) (abs_nonneg _))

theorem hilbertL1Norm_eq_inner_abs (f : ThresholdHilbert) :
    hilbertL1Norm f = inner ℝ (hilbertAbs f) hilbertOne := by
  rw [hilbert_inner_one, hilbertAbs_sequence]
  rfl

theorem hilbertL1Norm_le_norm (f : ThresholdHilbert) : hilbertL1Norm f ≤ ‖f‖ := by
  have hOne : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  rw [hilbertL1Norm_eq_inner_abs]
  simpa only [hilbertAbs_norm, hOne, mul_one] using real_inner_le_norm (hilbertAbs f) hilbertOne

theorem inner_one_le_hilbertL1Norm (f : ThresholdHilbert) :
    inner ℝ f hilbertOne ≤ hilbertL1Norm f := by
  rw [hilbert_inner_one]
  exact Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (le_abs_self _) (positiveWeight_nonneg k))
    (weighted_summable_of_square (hilbertSequence_square_summable f))
    (hilbertL1Norm_summable f)

theorem hilbertL1Norm_tendsto_zero_of_norm {f : ℕ → ThresholdHilbert}
    (h : Tendsto (fun n => ‖f n‖) atTop (𝓝 0)) :
    Tendsto (fun n => hilbertL1Norm (f n)) atTop (𝓝 0) :=
  squeeze_zero (fun n => hilbertL1Norm_nonneg (f n))
    (fun n => hilbertL1Norm_le_norm (f n)) h

end RiemannResearch.RH.Pareto

import RiemannResearch.Analysis.DistinctGapCofinalTransfer
import RiemannResearch.Analysis.MicroscopicSquareTailCriteria
import RiemannResearch.Analysis.MicroscopicWindowSubdivision
import RiemannResearch.Analysis.ZeroDPPFactorialWidthContrast

/-!
# Occurrence and distinct-ordinate PCC under the short-window upper estimate

Under the sine second-moment law the second factorial moment on cells of
width `Q/k` absorbs the quadratic cost of subdividing the width `Q`. This
gives uniform integrability of the translated square for each fixed width.
Consequently the transfer in both directions only requires the short-window
second-moment upper estimate.
-/

noncomputable section

namespace RiemannResearch.Analysis.DistinctOrdinatePCC
open Filter MeasureTheory ActualZeroWindowVariance MontgomeryPositiveGap
open ZeroDPPCorrelation MicroscopicSquareTailCriteria MicroscopicWindowSubdivision
open scoped Topology

theorem vanishingTranslatedSquareTail_of_sineWindowMoment (hs : SineWindowMoment)
    {Q : ℝ} (hQ : 0 < Q) : VanishingTranslatedSquareTail Q := by
  intro ε hε
  obtain ⟨k, hk, h⟩ := exists_scaled_factorialWindowMoment_lt hs hQ hε
  refine ⟨2*k, ?_⟩
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hT ht
  apply (truncatedWindowSecondMoment_subdivision ht hQ.le hk).trans_lt
  simpa only [unfoldedFactorialWindowMoment, windowLatticeExcess, unfoldingScale,
    Nat.cast_zero, mul_zero, zero_mul, zero_add, one_mul, add_zero, mul_sub, mul_one, sq] using hT

/-- Neither direction requires a separate translated third-moment or tail
hypothesis. The short-window upper estimate is the only analytic premise. -/
theorem positiveGapPCC_iff_distinctLaw_of_shortUpper (hm : ShortWindowSecondMomentUpper) :
    PositiveGapPCC ↔ DistinctPositiveGapLaw := by
  constructor
  · intro hp
    have hs := sineWindowMoment_of_positiveGapPCC hp hm
    apply (positiveGapPCC_iff_distinctLaw_of_squareTail hm ?_).mp hp
    intro q hq
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    exact vanishingTranslatedSquareTail_of_sineWindowMoment hs (by linarith)
  · intro hd
    exact positiveGapPCC_of_distinctLaw_shortUpper hd hm

/-- info: 'RiemannResearch.Analysis.DistinctOrdinatePCC.positiveGapPCC_iff_distinctLaw_of_shortUpper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_distinctLaw_of_shortUpper

end RiemannResearch.Analysis.DistinctOrdinatePCC

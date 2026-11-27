import RiemannResearch.Analysis.MicroscopicOrdinatePacking
import RiemannResearch.Analysis.MontgomeryMicroscopicGapPacking
import RiemannResearch.Analysis.MontgomeryMicroscopicCovariance
import RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs

/-! # Size of strict microscopic pair counts

The two external estimates used in the asymptotic applications are exposed
in the theorem types. Alpöge–Furman, arXiv:2608.13637v2, Theorem A, supplies
the simple critical-line proportion. Lamzouri, arXiv:2611.14486, Lemmas
2.2–2.3, obtains the Cauchy row bound from Fujii's microscopic moments.
The finite packing and Cauchy-row comparisons are unconditional.
-/
noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualMontgomeryExceptionalPairs
open MontgomeryExceptionalPairs

/-- Physical one-sided pair count, including every occurrence, omitting ties. -/
def physicalStrictPairs (T h : ℝ) : ℝ :=
  ∑ i : Copies T, ∑ j : Copies T,
    if 0 < copyOrdinate T j - copyOrdinate T i ∧ copyOrdinate T j - copyOrdinate T i ≤ h
      then 1 else 0

private theorem scale_pos {T : ℝ} (hT : 1 < T) : 0 < unfoldingScale T :=
  div_pos (Real.log_pos hT) (by positivity)

theorem physicalStrictPairs_normalized {T : ℝ} (hT : 1 < T) (h : ℝ) :
    physicalStrictPairs T h / unfoldedCutoff T = positiveGapMass T (unfoldingScale T * h) := by
  change (_ / _) = (∑ i : Copies T, ∑ j : Copies T, if
    0 < unfoldingScale T * (copyOrdinate T j - copyOrdinate T i) ∧
    unfoldingScale T * (copyOrdinate T j - copyOrdinate T i) ≤ unfoldingScale T * h
    then (1:ℝ) else 0) / unfoldedCutoff T
  simp only [physicalStrictPairs, mul_pos_iff_of_pos_left (scale_pos hT),
    mul_le_mul_iff_right₀ (scale_pos hT)]

theorem PositiveGapPCC.moving_physical_width {ι : Type*} {l : Filter ι} (h : PositiveGapPCC)
    {T w : ι → ℝ} {q : ℝ} (hT : Tendsto T l atTop)
    (hw : Tendsto (fun i => unfoldingScale (T i) * w i) l (𝓝 q)) (hq : 0 < q) :
    Tendsto (fun i => physicalStrictPairs (T i) (w i) / unfoldedCutoff (T i)) l
      (𝓝 (sineGapMass q)) := by
  apply (h.moving_width hT hw hq).congr'
  filter_upwards [hT.eventually (eventually_gt_atTop (1 : ℝ))] with i hi
  exact (physicalStrictPairs_normalized hi _).symm

/-- Count distinct actual heights in a band using its own length and pairs
with both endpoints in the band. This also applies when the band moves. -/
theorem distinct_band_packing {T a b w : ℝ} (hab : a ≤ b) (hw : 0 < w) :
    let s := (distinctOrdinates T).filter fun t => t ∈ Icc a b
    (s.card : ℝ) ≤ (b-a)/w + 1 +
      ∑ i : s, ∑ j : s, if 0 < j.val - i.val ∧ j.val - i.val ≤ w then (1 : ℝ) else 0 := by
  intro s
  exact MicroscopicPacking.strict_pair_packing_in_band s id (fun _ _ _ _ h => h)
    hab hw fun _ hi => (Finset.mem_filter.mp hi).2

theorem physicalStrictPairs_le_cauchy_rows {T w : ℝ} (hT : 1 < T) :
    physicalStrictPairs T w ≤ (1+(w*Real.log T)^2) *
      ∑ i : Copies T, rowMass Finset.univ (gapWeight T) i := by
  have hlog := (Real.log_pos hT).le
  unfold physicalStrictPairs rowMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h
  · let d := copyOrdinate T j - copyOrdinate T i
    have h0 : 0 ≤ d * Real.log T := mul_nonneg h.1.le hlog
    have h1 : d * Real.log T ≤ w * Real.log T := mul_le_mul_of_nonneg_right h.2 hlog
    have hsq := pow_le_pow_left₀ h0 h1 2
    have hden : 0 < 1+((-d)*Real.log T)^2 := by positivity
    change 1 ≤ (1+(w*Real.log T)^2) * (1/(1+
      ((copyOrdinate T i - copyOrdinate T j)*Real.log T)^2))
    rw [show copyOrdinate T i - copyOrdinate T j = -d by dsimp [d]; ring, mul_one_div]
    apply (le_div_iff₀ hden).2
    simpa [neg_mul] using (add_le_add_left hsq 1)
  · exact mul_nonneg (by positivity) (gapWeight_nonneg T i j)

/-- The first of Fujii's row moments suffices for bounded normalized pair
counts, uniformly over a bounded range of physical widths. -/
theorem eventually_microscopic_upper_of_fujii (hf : FujiiMicroscopicRowMoments)
    (Q : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ w : ℝ,
      0 ≤ w → w * Real.log T ≤ Q →
      physicalStrictPairs T w ≤ C * (Ncount 0 T : ℝ) := by
  obtain ⟨A,hA,ha⟩ := hf 1 le_rfl
  refine ⟨(1+Q^2)*A, mul_nonneg (by positivity) hA, ?_⟩
  filter_upwards [ha, eventually_gt_atTop (1:ℝ), eventually_count_pos] with T hb hT hN
  intro w hw hwidth
  have hn : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
  simp only [pow_one, ← Finset.mul_sum] at hb
  have hrow : (∑ i : Copies T, rowMass Finset.univ (gapWeight T) i) ≤ A*(Ncount 0 T : ℝ) := by
    apply (div_le_iff₀ hn).mp
    simpa only [div_eq_inv_mul] using hb
  have hsq := pow_le_pow_left₀ (mul_nonneg hw (Real.log_pos hT).le) hwidth 2
  calc
    _ ≤ _ := physicalStrictPairs_le_cauchy_rows hT
    _ ≤ (1+Q^2) * (A*(Ncount 0 T : ℝ)) :=
      mul_le_mul (by linarith only [hsq]) hrow
        (Finset.sum_nonneg fun i _ => (one_le_gap_row T i).trans' zero_le_one) (by positivity)
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryPositiveGap

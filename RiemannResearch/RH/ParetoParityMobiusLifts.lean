import RiemannResearch.RH.ParetoParityFiniteHeadTransfer
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.QCanonicalMobiusCostRates

/-!
# Sublinear complete energy for finite exact heads of the parity adjoint

The input is the unconditional reciprocal Möbius cancellation theorem.
At each cutoff, use a single canonical Möbius vector in every forward
dilation in the transfer. The resulting error estimate includes all sites.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- A finite legal realization uses the same arithmetic cutoff in every dilate. -/
def parityMobiusLift (N : ℕ) : ThresholdHilbert :=
  parityHeadTransfer N (canonicalMobiusHilbert N)

theorem parityMobiusLift_mem (N : ℕ) :
    parityMobiusLift N ∈ finiteSpace (N * (N + 1)) :=
  parityHeadTransfer_mem N N (canonicalMobiusHilbert N)
    (canonicalMobiusHilbert_mem_finiteSpace N)

theorem parityMobiusLift_exact (N : ℕ) :
    compactHead N (parityMobiusLift N) = compactHead N parityAdjointPacket := by
  apply parityHeadTransfer_exact
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst k
    simp only [hilbertSequence_zero]
  · rw [canonicalMobiusHilbert_exact N k hk0 hk, hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt hk0]

/-- Every coordinate lies between zero and one half, and the Pareto weights
sum to one. -/
theorem parityAdjointPacket_norm_sq_le_quarter :
    ‖parityAdjointPacket‖ ^ 2 ≤ 1 / 4 := by
  rw [hilbert_norm_weighted_sq]
  calc
    _ ≤ ∑' k : ℕ, positiveWeight k * (1/4 : ℝ) := by
      apply Summable.tsum_le_tsum _ (hilbertSequence_square_summable _)
        (positiveWeight_summable.mul_right _)
      intro k
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      rw [parityAdjointPacket_coordinate]
      have hnon : 0 ≤ (k : ℝ)/(2*(k : ℝ)+1) := by positivity
      have hhalf : (k : ℝ)/(2*(k : ℝ)+1) ≤ 1/2 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      convert (sq_le_sq₀ hnon (by norm_num : (0 : ℝ) ≤ 1/2)).mpr hhalf using 1 <;> norm_num
    _ = _ := by rw [tsum_mul_right, positiveWeight_tsum, one_mul]

/-- A finite forward transfer costs at most one half of the source energy
plus one half, for the complete error against the adjoint target. -/
theorem parityMobiusLift_error_sq_le (N : ℕ) :
    ‖parityAdjointPacket - parityMobiusLift N‖ ^ 2 ≤
      1/2 + (1/2 : ℝ) * ‖canonicalMobiusHilbert N‖ ^ 2 := by
  have htransfer := parityHeadTransfer_norm_le N (canonicalMobiusHilbert N)
  change ‖parityMobiusLift N‖ ≤ (1/2 : ℝ) * ‖canonicalMobiusHilbert N‖ at htransfer
  have hnorm : ‖parityAdjointPacket - parityMobiusLift N‖ ≤
      ‖parityAdjointPacket‖ + (1/2 : ℝ) * ‖canonicalMobiusHilbert N‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl htransfer)
  have hsq := (sq_le_sq₀ (norm_nonneg (parityAdjointPacket - parityMobiusLift N))
    (add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _)))).mpr hnorm
  nlinarith [parityAdjointPacket_norm_sq_le_quarter,
    sq_nonneg (‖parityAdjointPacket‖ - (1/2 : ℝ) * ‖canonicalMobiusHilbert N‖)]

/-- The full squared error of these finite legal exact heads is little-o of
the head length. -/
theorem parityMobiusLift_error_sq_div_tendsto_zero :
    Tendsto (fun N : ℕ => ‖parityAdjointPacket - parityMobiusLift N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hconst := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2 : ℝ)
  have hcan := canonicalMobiusHilbert_sublinear.const_mul (1/2 : ℝ)
  have hlim : Tendsto (fun N : ℕ => (1/2 : ℝ) * (1 / (N : ℝ)) +
      (1/2 : ℝ) * (‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hconst.add hcan
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) _ hlim
  intro N
  calc
    _ ≤ (1/2 + (1/2 : ℝ) * ‖canonicalMobiusHilbert N‖ ^ 2) / (N : ℝ) :=
      div_le_div_of_nonneg_right (parityMobiusLift_error_sq_le N) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Unconditional stretched-exponential saving on the complete squared
error of the transferred exact heads. -/
theorem parityMobiusLift_eventual_stretched_error :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖parityAdjointPacket - parityMobiusLift N‖ ^ 2 ≤ 2 + C * (N : ℝ) *
        Real.exp (-a * RiemannResearch.Analysis.logProductPower
          (1 / 11) (6 + Real.log (N : ℝ))) := by
  obtain ⟨a, ha, C, hC, hbound⟩ := canonicalMobius_eventual_stretched_bounds
  refine ⟨a, ha, C/2, by positivity, ?_⟩
  filter_upwards [hbound] with N hN
  linarith only [parityMobiusLift_error_sq_le N, hN.2]

open RiemannResearch.NumberTheory.PrimeNumberTheorem
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.QCanonicalMobiusCost

/-- All positive contour rates below the classical endpoint survive in
the full squared error, at every positive head length. -/
theorem parityMobiusLift_global_sqrt_log_error (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 0 < N →
      ‖parityAdjointPacket - parityMobiusLift N‖ ^ 2 ≤
        13/2 + B * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ))) := by
  have hζ := zetaTwo_pos
  obtain ⟨C, hC, hcost⟩ := balanced_cost_global_sqrt_log c hc hcE
  refine ⟨zetaTwo * C / 2, by positivity, ?_⟩
  intro N hN
  have hR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let e := Real.exp (-c * Real.sqrt (Real.log (N : ℝ)))
  have h := (balanced_cost_source_lower N).trans (hcost N hN)
  have hsource : ‖canonicalMobiusHilbert N‖ ^ 2 ≤
      12 + zetaTwo * C * (N : ℝ) * e := by
    calc
      _ = ((((N : ℝ)^2)⁻¹ * ‖canonicalMobiusHilbert N‖^2 / zetaTwo) *
          (zetaTwo * (N : ℝ)^2)) := by field_simp [hR.ne', zetaTwo_pos.ne']
      _ ≤ (12/(zetaTwo * (N : ℝ)^2) + C/(N : ℝ) * e) *
          (zetaTwo * (N : ℝ)^2) := mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by field_simp [hR.ne', zetaTwo_pos.ne']
  change ‖parityAdjointPacket - parityMobiusLift N‖ ^ 2 ≤
    13/2 + (zetaTwo * C / 2) * (N : ℝ) * e
  linarith only [parityMobiusLift_error_sq_le N, hsource]

end RiemannResearch.RH.Pareto.PrimePowerSchur

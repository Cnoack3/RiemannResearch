import RiemannResearch.RH.PrimeSupportCokernel
import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.MixedConductorGlobalParseval

/-!
# Parity in the prime-support cokernel tower

The classes of the normalized parity packet minus the ambient constant have
squared norms equal to the squared centered snake boundary plus the omitted
mixed energy. Orthogonal projection in the mixed space realizes the minimum
over each ambient support stage. See S. Axler, *Measure, Integration & Real
Analysis*, Chapter 8, on best approximation in Hilbert space.

B. Bagchi, *On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of
the Riemann hypothesis*, Proc. Indian Acad. Sci. Math. Sci. 116 (2006), 137–146,
Theorem 1, treats approximation in the discrete weighted Hilbert space.
L. Báez-Duarte, *A strengthening of the Nyman-Beurling criterion for the Riemann
hypothesis*, Rend. Lincei Mat. Appl. 14 (2003), 5–11, gives the integer-dilation
criterion. J.-F. Burnol, *A note on Nyman's equivalent formulation of the Riemann
hypothesis*, Contemp. Math. 287 (2001), 23–26, relates the continuous projection
to a product over zeros. The bound below uses the repository's finite Mellin
inequality for one zero.

For a finite dictionary of mixed packets, the quadratic test uses its Gram matrix
and the inner products with the centered parity input. Packet independence makes
the Gram matrix positive definite. Solving the finite normal equations gives
coefficients that minimize this trial error. The open arithmetic step
is to construct dictionaries and coefficients with arbitrarily small error.
A trial error below 2σ/(T² + 1/4) excludes zeros with real part at least
1/2 + σ and absolute imaginary part at most T in the open critical strip.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- The class of the normalized conductor-two packet minus the ambient constant. -/
def parityQuotientClass (n : ℕ) : ThresholdHilbert ⧸ ambientSupport n :=
  (ambientSupport n).mkQ ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne)

/-- The squared quotient distance includes the snake obstruction and the omitted mixed energy. -/
theorem parityQuotientClass_norm_sq (n : ℕ) :
    ‖parityQuotientClass n‖ ^ 2 = ‖CenteredMeanSnake.boundary‖ ^ 2 +
      ‖parityMixedProjection - (supportSpace n).starProjection parityMixedProjection‖ ^ 2 := by
  let g : ThresholdHilbert := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  let m := parityMixedProjection
  let p := (supportSpace n).starProjection m
  let d := normalizedScreenedTwo - hilbertOne
  have hsplit : g - hilbertOne = d + (m : ThresholdHilbert) := by
    have hu := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
    rw [Submodule.starProjection_orthogonal_val, smul_sub] at hu
    change g - hilbertOne = (normalizedScreenedTwo - hilbertOne) + mixedClosure.starProjection g
    dsimp only [g]
    rw [map_smul, hu]
    abel
  have hnorm (w : mixedClosure) :
      ‖g - hilbertOne - (w : ThresholdHilbert)‖ ^ 2 =
        ‖CenteredMeanSnake.boundary‖ ^ 2 + ‖m - w‖ ^ 2 := by
    have ho : inner ℝ d ((m - w : mixedClosure) : ThresholdHilbert) = 0 :=
      (real_inner_comm _ _).trans
        (CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2 _ (m - w).property)
    rw [hsplit, add_sub_assoc]
    change ‖d + ((m - w : mixedClosure) : ThresholdHilbert)‖ ^ 2 = _
    rw [norm_add_sq_real, ho, CenteredMeanSnake.boundary_norm]
    change ‖d‖ ^ 2 + 2 * 0 + ‖m - w‖ ^ 2 = ‖d‖ ^ 2 + ‖m - w‖ ^ 2
    ring
  have hp : (p : ThresholdHilbert) ∈ ambientSupport n :=
    ⟨p, (supportSpace n).starProjection_apply_mem m, rfl⟩
  have hmin (w : mixedClosure) (hw : w ∈ supportSpace n) : ‖m - p‖ ≤ ‖m - w‖ := by
    change ‖m - (supportSpace n).starProjection m‖ ≤ ‖m - w‖
    rw [← (supportSpace n).infDist_eq_norm_sub_starProjection m]
    simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := m) hw
  have hdist : ‖parityQuotientClass n‖ = ‖g - hilbertOne - (p : ThresholdHilbert)‖ := by
    have hq : ‖parityQuotientClass n‖ =
        Metric.infDist (g - hilbertOne) (ambientSupport n : Set ThresholdHilbert) :=
      QuotientAddGroup.norm_mk (S := (ambientSupport n).toAddSubgroup) (g - hilbertOne)
    rw [hq]
    apply le_antisymm
    · simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := g - hilbertOne) hp
    · apply (Metric.le_infDist ⟨0, (ambientSupport n).zero_mem⟩).mpr
      rintro _ ⟨w, hw, rfl⟩
      rw [dist_eq_norm]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖g - hilbertOne - (p : ThresholdHilbert)‖ ^ 2 ≤
        ‖g - hilbertOne - (w : ThresholdHilbert)‖ ^ 2
      rw [hnorm p, hnorm w]
      exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hmin w hw) 2)
  rw [hdist]
  exact hnorm p

/-- Along the support diagram the squared quotient norms converge to the squared boundary norm. -/
theorem tendsto_parityQuotientClass_norm_sq :
    Tendsto (fun n => ‖parityQuotientClass n‖ ^ 2) atTop
      (𝓝 (‖CenteredMeanSnake.boundary‖ ^ 2)) := by
  have hp := tendsto_sum_supportLayer_projection parityMixedProjection
  simp only [sum_supportLayer_projection] at hp
  have ht := ((tendsto_const_nhds (x := parityMixedProjection)).sub hp).norm.pow 2
  simpa only [parityQuotientClass_norm_sq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero] using (tendsto_const_nhds (x := ‖CenteredMeanSnake.boundary‖ ^ 2)).add ht

/-- An arbitrarily small quotient error is equivalent to vanishing of the centered boundary. -/
theorem boundary_eq_zero_iff_small_parity_quotients :
    CenteredMeanSnake.boundary = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖parityQuotientClass n‖ ^ 2 < ε := by
  constructor
  · intro hb ε hε
    have ht := tendsto_parityQuotientClass_norm_sq
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)] at ht
    exact ((tendsto_order.mp ht).2 ε hε).exists
  · intro h
    by_contra hb
    have hpos : 0 < ‖CenteredMeanSnake.boundary‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
    obtain ⟨n, hn⟩ := h _ hpos
    rw [parityQuotientClass_norm_sq] at hn
    exact (not_lt_of_ge (le_add_of_nonneg_right (sq_nonneg _))) hn

/-- Arbitrarily small quadratic errors on finite dictionaries of mixed packets imply RH. -/
theorem riemannHypothesis_of_finite_parity_certificates
    (h : ∀ ε : ℝ, 0 < ε → ∃ (F : Finset Index) (a : Index → ℝ),
      let x := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
      let w : mixedClosure := ∑ q ∈ F, a q • packet q
      ‖x‖ ^ 2 - 2 * inner ℝ x (w : ThresholdHilbert) + ‖w‖ ^ 2 < ε) :
    RiemannHypothesis := by
  classical
  apply CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
  apply boundary_eq_zero_iff_small_parity_quotients.mpr
  intro ε hε
  obtain ⟨F, a, hscore⟩ := h ε hε
  let x := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
  let w : mixedClosure := ∑ q ∈ F, a q • packet q
  let n := F.sup fun q => q.val.primeFactors.card
  have hw : w ∈ supportSpace n := by
    apply Submodule.sum_mem
    intro q hq
    apply Submodule.smul_mem
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span
      ⟨q, Finset.le_sup (f := fun r : Index => r.val.primeFactors.card) hq, rfl⟩)
  have herr : ‖x - (w : ThresholdHilbert)‖ ^ 2 < ε := by
    rw [norm_sub_sq_real]
    exact hscore
  refine ⟨n, lt_of_le_of_lt ?_ herr⟩
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  have hq : ‖parityQuotientClass n‖ = Metric.infDist x (ambientSupport n : Set ThresholdHilbert) :=
    QuotientAddGroup.norm_mk (S := (ambientSupport n).toAddSubgroup) x
  rw [hq]
  have hw' : (w : ThresholdHilbert) ∈ ambientSupport n := ⟨w, hw, rfl⟩
  simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := x) hw'

/-- A zero to the right of the critical line gives the same positive lower bound at every cutoff. -/
theorem single_zero_le_parityQuotientClass (z : ℂ) (hz : riemannZeta z = 0)
    (hre : (1 / 2 : ℝ) < z.re) (hne : z ≠ 1) (n : ℕ) :
    2 * z.re - 1 ≤ ‖1 - z‖ ^ 2 * ‖parityQuotientClass n‖ ^ 2 := by
  have h := legalMeanSection_single_zero_excess z hz hre hne
    screenedMeanSection legalPacketMean_comp_screenedMeanSection
  rw [norm_screenedMeanSection, ← CenteredMeanSnake.boundary_norm_sq] at h
  rw [parityQuotientClass_norm_sq]
  exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _))

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

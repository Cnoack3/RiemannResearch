import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Explicit full-conductor Q candidates and their convergence conditions

Source: user-provided Q/Ramanujan candidate program, 13 October 2026.
The coefficients are literal finite matrix inverses. The same candidates
have a finite integrated-Ramanujan representation. Their exact error is the
reciprocal of one plus covariance information.

This is a conditional research reduction: divergence of this information,
or a uniform arithmetic tail bound for legal exact-head candidates, is an
open input. No unconditional approximation of one is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QExplicitCandidates
open ZetaTwoHilbert QCovarianceInverse QCovarianceInvertibility
open QFullResidueProjection

/-- A concrete scalar computed from the genuine finite covariance inverse. -/
def capacity (n : ℕ) : ℝ := covarianceInformation (conductor n)

/-- Explicit Ramanujan coefficients for the very same inverse-Gram candidate. -/
theorem candidate_eq_packets (n : ℕ) :
    candidate n = ∑ q ∈ QRamanujanPackets.packetSupport (conductor n),
      QRamanujanPackets.packetCoefficient (conductor n) (coefficients n) q •
        QRamanujanPackets.qRamanujanPacket q :=
  QRamanujanPackets.qSynthesis_eq_packets _ _
    (fun i => lt_trans Nat.zero_lt_one (conductor_gt_one n i))

theorem capacity_nonneg (n : ℕ) : 0 ≤ capacity n := by
  exact qInformation_nonneg (conductor n) (covarianceInverseSource (conductor n))
    (covarianceInverseSource_normal _ (conductor_gt_one n) (conductor_injective n))

/-- The full error, including every physical coordinate and cross term. -/
theorem candidate_error_exact (n : ℕ) :
    ‖qOne - candidate n‖ ^ 2 = 1 / (1 + capacity n) := by
  have hd := conductor_gt_one n
  have hi := conductor_injective n
  unfold candidate coefficients
  rw [gramInverseSource_eq_normalized_covariance _ hd hi]
  exact qError_genuine_inverse _ hd hi

theorem candidate_error_pos (n : ℕ) : 0 < ‖qOne - candidate n‖ ^ 2 := by
  rw [candidate_error_exact]
  have h := capacity_nonneg n
  positivity

/-- The explicit matrix candidates converge exactly when their information diverges. -/
theorem candidate_tendsto_iff_capacity :
    Tendsto candidate atTop (𝓝 qOne) ↔ Tendsto capacity atTop atTop := by
  constructor
  · intro ht
    have he : Tendsto (fun n => ‖qOne - candidate n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using ((tendsto_const_nhds (x := qOne)).sub ht).norm.pow 2
    apply tendsto_atTop.2
    intro B
    have hp : 0 < max B 0 + 2 := by positivity
    filter_upwards [he.eventually (Iio_mem_nhds (one_div_pos.mpr hp))] with n hn
    rw [candidate_error_exact] at hn
    have hd : 0 < 1 + capacity n := by have := capacity_nonneg n; linarith
    have h := (div_lt_div_iff₀ hd hp).mp hn
    have hB := le_max_left B 0
    nlinarith
  · intro ht
    have he : Tendsto (fun n => ‖qOne - candidate n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_order.2
      constructor
      · intro a ha
        exact Filter.Eventually.of_forall (fun n => ha.trans_le (sq_nonneg _))
      · intro b hb
        filter_upwards [(tendsto_atTop.mp ht) (1 / b)] with n hn
        rw [candidate_error_exact]
        have hd : 0 < 1 + capacity n := by have := capacity_nonneg n; linarith
        apply (div_lt_iff₀ hd).mpr
        have h := (div_le_iff₀ hb).mp hn
        nlinarith
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp he
    have hn' : Tendsto (fun n => ‖qOne - candidate n‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [norm_sub_rev] using hn'

/-- Any uniformly bounded legal exact-head family supplies convergence of
the fixed explicit inverse-Gram sequence; its coefficients require no
choice of an optimizer or of the auxiliary family. -/
theorem candidate_tendsto_of_bounded_exact_heads
    (F : ℕ → QHilbert) (hlegal : ∀ n, F n ∈ legalSpan)
    {B : ℝ} (hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ B)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1) :
    Tendsto candidate atTop (𝓝 qOne) := by
  obtain ⟨q, _, hmem, _, ht⟩ :=
    QExactHeadAverages.exists_legal_averages_of_bounded_exact_heads
      legalSpan F hlegal hbound hhead
  apply candidate_tendsto_qOne
  exact legalSpan.isClosed_topologicalClosure.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun m => legalSpan.le_topologicalClosure (hmem m)))

end RiemannResearch.RH.QExplicitCandidates

import RiemannResearch.RH.IntegerDPPSchur
import RiemannResearch.RH.CanonicalTailCapacityGeometry
import RiemannResearch.RH.TailCapacityJointCorrections

/-!
# Exact infinite Schur energy of the canonical tail obstruction

These identities combine the actual finite signed Schur telescope with strong
convergence of the canonical tail interpolation vectors. They describe the
nonzero-residual alternative and do not exclude it or prove RH.

Source: the user-provided odd-carry/DPP continuation of 2026-09-20 and the
existing project proofs in IntegerDPPSchur and CanonicalTailCapacityGeometry.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity

/-- Exact infinite Schur accounting under the nonzero-residual alternative. -/
theorem schur_hasSum_canonical_energy (hr : pointDualResidual ≠ 0) :
    HasSum (fun n => (schurEta n) ^ 2 / schurSigma n)
      (‖canonicalTailCertificate‖ ^ 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => div_nonneg (sq_nonneg _) (schurSigma_pos n).le) _).mpr
  simpa only [← capacity_eq_sum_schur] using
    tailCapacity_tendsto_canonical_energy hr

theorem schur_tsum_canonical_energy (hr : pointDualResidual ≠ 0) :
    (∑' n, (schurEta n) ^ 2 / schurSigma n) =
      ‖canonicalTailCertificate‖ ^ 2 :=
  (schur_hasSum_canonical_energy hr).tsum_eq

/-- The unspent total signed Schur energy is exactly the actual dual error. -/
theorem schur_tsum_sub_capacity_eq_error (hr : pointDualResidual ≠ 0) (N : ℕ) :
    (∑' n, (schurEta n) ^ 2 / schurSigma n) - tailCapacity N =
      ‖canonicalTailCertificate - tailMinimum N‖ ^ 2 := by
  rw [schur_tsum_canonical_energy hr,
    tailCertificate_energy_completion canonicalTailCertificate
      (canonicalTailCertificate_isCertificate hr) N]
  ring

/-- Every remaining Schur tail has exactly the canonical residual energy. -/
theorem schur_tail_hasSum_error (hr : pointDualResidual ≠ 0) (N : ℕ) :
    HasSum (fun j => (schurEta (j + N)) ^ 2 / schurSigma (j + N))
      (‖canonicalTailCertificate - tailMinimum N‖ ^ 2) := by
  have h := (hasSum_nat_add_iff'
    (f := fun n => (schurEta n) ^ 2 / schurSigma n)
    (g := ‖canonicalTailCertificate‖ ^ 2) N).2
      (schur_hasSum_canonical_energy hr)
  have he : ‖canonicalTailCertificate‖ ^ 2 - tailCapacity N =
      ‖canonicalTailCertificate - tailMinimum N‖ ^ 2 := by
    linarith [tailCertificate_energy_completion canonicalTailCertificate
      (canonicalTailCertificate_isCertificate hr) N]
  simpa only [← capacity_eq_sum_schur, he] using h

theorem schur_tail_tsum_eq_error (hr : pointDualResidual ≠ 0) (N : ℕ) :
    (∑' j, (schurEta (j + N)) ^ 2 / schurSigma (j + N)) =
      ‖canonicalTailCertificate - tailMinimum N‖ ^ 2 :=
  (schur_tail_hasSum_error hr N).tsum_eq

/-- All tail-atom source discrepancies are bounded by the same actual dual
error; hence the estimate is uniform over every old or future modulus. -/
theorem reciprocalDefect_le_canonical_error (hr : pointDualResidual ≠ 0)
    (N i : ℕ) :
    |reciprocalDefect N i| ≤
      ‖canonicalTailCertificate - tailMinimum N‖ * ‖tailAtom i‖ := by
  rw [reciprocalDefect_eq_certificate_error canonicalTailCertificate
    (canonicalTailCertificate_isCertificate hr)]
  simpa only [Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ)
      (canonicalTailCertificate - tailMinimum N) (tailAtom i)

/-- Uniform vanishing after normalizing by each atom norm. The conclusion is
written without division so it also handles zero trial vectors automatically. -/
theorem reciprocalDefect_uniform_normalized_vanishing
    (hr : pointDualResidual ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ i : ℕ,
      |reciprocalDefect N i| ≤ ε * ‖tailAtom i‖ := by
  have ht : Tendsto
      (fun N => ‖canonicalTailCertificate - tailMinimum N‖)
      atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := canonicalTailCertificate)).sub
      (tailMinimum_tendsto_canonical hr)).norm
    simpa only [sub_self, norm_zero] using h
  have he : ∀ᶠ N in atTop,
      ‖canonicalTailCertificate - tailMinimum N‖ < ε :=
    (tendsto_order.1 ht).2 ε hε
  filter_upwards [he] with N hN
  intro i
  exact (reciprocalDefect_le_canonical_error hr N i).trans
    (mul_le_mul_of_nonneg_right hN.le (norm_nonneg _))

end RiemannResearch.RH.Pareto.IntegerDPP

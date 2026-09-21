import RiemannResearch.RH.ExactHeadResidualTail

/-!
# Escaping support forces the energy of normalized tail certificates to diverge

Source: user-provided `RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`.
The statement uses the actual Pareto Hilbert vector g₂ and all of its tail.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Every physical value of the actual g₂ generator is zero or one half. -/
theorem residue_two_coordinate_sq_le (k : ℕ) :
    ((normalizedResidueHilbert 2 (by omega)) k) ^ 2 ≤ paretoWeight k / 4 := by
  rw [← hilbertSequence_weighted_square, positiveWeight_succ,
    normalizedResidueHilbert_sequence]
  have hm : ((k + 1) % 2 : ℕ) ≤ 1 := by omega
  have hmR : (↑((k + 1) % 2) : ℝ) ≤ 1 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ ↑((k + 1) % 2) := Nat.cast_nonneg _
  have hs : residueFraction 2 (k + 1) ^ 2 ≤ (1 / 4 : ℝ) := by
    unfold residueFraction
    norm_num
    nlinarith
  calc
    _ ≤ paretoWeight k * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hs (paretoWeight_pos k).le
    _ = _ := by ring

theorem residue_two_tail_norm_sq_le (N : ℕ) :
    ‖hilbertTailShift (normalizedResidueHilbert 2 (by omega)) N‖ ^ 2 ≤
      1 / (4 * ((N : ℝ) + 1)) := by
  have htail : (∑' n : ℕ, paretoWeight (n + N)) = 1 / ((N : ℝ) + 1) := by
    have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add N
    rw [paretoWeight_hasSum.tsum_eq, paretoWeight_partial_sum] at h
    linarith
  rw [hilbert_norm_sq]
  change (∑' n : ℕ, ((normalizedResidueHilbert 2 (by omega)) (n + N)) ^ 2) ≤ _
  calc
    _ ≤ ∑' n : ℕ, paretoWeight (n + N) / 4 := by
      exact Summable.tsum_le_tsum (fun n => residue_two_coordinate_sq_le (n + N))
        ((summable_nat_add_iff N).mpr
          (hilbert_coordinate_square_summable (normalizedResidueHilbert 2 (by omega))))
        (((summable_nat_add_iff N).mpr paretoWeight_hasSum.summable).div_const 4)
    _ = _ := by
      rw [tsum_div_const, htail]
      field_simp

/-- A certificate with fixed g₂ pairing and a vanishing physical head has
at least linear norm-squared cost in the first possible support location. -/
theorem normalized_certificate_head_vanishing_energy_lower
    (N : ℕ) (z : ThresholdHilbert)
    (hsupp : ∀ k, 0 < k → k ≤ N → hilbertSequence z k = 0)
    (hpair : inner ℝ (normalizedResidueHilbert 2 (by omega)) z = 1 / 2) :
    (N : ℝ) + 1 ≤ ‖z‖ ^ 2 := by
  have hz : ∀ n < N, z n = 0 := by
    intro n hn
    have hs := hsupp (n + 1) (by omega) (by omega)
    change z n / Real.sqrt (paretoWeight n) = 0 at hs
    exact (div_eq_zero_iff.mp hs).resolve_right
      (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne'
  have hc := hilbertTailShift_inner_sq_le
    (normalizedResidueHilbert 2 (by omega)) z N hz
  rw [hpair] at hc
  have hb := mul_le_mul_of_nonneg_right (residue_two_tail_norm_sq_le N) (sq_nonneg ‖z‖)
  have hc' : (1 / 4 : ℝ) ≤ ‖z‖ ^ 2 / (4 * ((N : ℝ) + 1)) := by
    have hcombined := hc.trans hb
    norm_num at hcombined
    simpa only [div_eq_mul_inv, one_mul, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hcombined
  have hcross := (le_div_iff₀ (show 0 < 4 * ((N : ℝ) + 1) by positivity)).mp hc'
  nlinarith

/-- Literal physical-support formulation from the research note. -/
theorem normalized_certificate_support_energy_lower
    (M : ℕ) (z : ThresholdHilbert)
    (hsupp : ∀ k < M, hilbertSequence z k = 0)
    (hpair : inner ℝ (normalizedResidueHilbert 2 (by omega)) z = 1 / 2) :
    (M : ℝ) ≤ ‖z‖ ^ 2 := by
  cases M with
  | zero => simpa using sq_nonneg ‖z‖
  | succ N =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        normalized_certificate_head_vanishing_energy_lower N z
          (fun k _ hk => hsupp k (by omega)) hpair

/-- Escaping support cannot give uniformly bounded normalized certificates. -/
theorem normalized_certificate_escaping_support_energy_tendsto
    (z : ℕ → ThresholdHilbert)
    (hsupp : ∀ M k, k < M → hilbertSequence (z M) k = 0)
    (hpair : ∀ M, inner ℝ (normalizedResidueHilbert 2 (by omega)) (z M) = 1 / 2) :
    Tendsto (fun M => ‖z M‖ ^ 2) atTop atTop :=
  tendsto_atTop_mono
    (fun M => normalized_certificate_support_energy_lower M (z M) (hsupp M) (hpair M))
    tendsto_natCast_atTop_atTop

end RiemannResearch.RH.Pareto

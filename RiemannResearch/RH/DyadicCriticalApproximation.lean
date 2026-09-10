import RiemannResearch.RH.DyadicCriticalResolvent
import RiemannResearch.RH.DyadicStepMeanIdentity

/-!
# Quantitative finite approximation of the actual critical quotient

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026, first next target. This continuation supplies an effective
truncation of the already constructed physical critical norm.

The exact terminal vector is retained. Its squared norm is bounded by
2^(-N) * ‖f‖², and the complete critical energy includes its signed mixed term.
For an integer step of index m ≤ 2^N, N+K levels give squared error at most
2^(-K). These are unconditional operator estimates and a genuine norm limit.
They do not prove the arithmetic off-diagonal Gram bound, the uniform
vanishing-damping norm bound, or full two-seed legal approximation.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary
noncomputable section

theorem dyadicHalfAdjoint_orbit_eq (f : ThresholdHilbert) (N : ℕ) :
    orbit dyadicHalfAdjoint f N =
      (1 / 2 : ℝ) ^ N • orbit (hilbertDilationAdjoint 2 (by norm_num)) f N := by
  induction N with
  | zero => simp only [orbit_zero, pow_zero, one_smul]
  | succ N ih =>
      rw [orbit_succ, ih, map_smul, dyadicHalfAdjoint_apply, smul_smul,
        pow_succ, orbit_succ]

theorem dyadicHalfAdjoint_orbit_norm_sq_le (f : ThresholdHilbert) (N : ℕ) :
    ‖orbit dyadicHalfAdjoint f N‖ ^ 2 ≤ (1 / 2 : ℝ) ^ N * ‖f‖ ^ 2 := by
  induction N with
  | zero => simp only [orbit_zero, pow_zero, one_mul, le_refl]
  | succ N ih =>
      calc
        _ ≤ (1 / 2 : ℝ) * ‖orbit dyadicHalfAdjoint f N‖ ^ 2 :=
          dyadicHalfAdjoint_norm_sq_le _
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ N * ‖f‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (N + 1) * ‖f‖ ^ 2 := by rw [pow_succ]; ring

/-- The finite critical reconstruction has exactly the projected terminal residual. -/
theorem dyadicCriticalPacket_error_eq (N : ℕ) (f : ThresholdHilbert) :
    dyadicQuotientProjection f -
        dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) =
      dyadicQuotientProjection (orbit dyadicHalfAdjoint f N) := by
  rw [dyadicQuotientProjection_kernelDefect_packet, dyadicHalfAdjoint_orbit_eq,
    map_smul]
  abel

/-- Uniform quantitative truncation for every actual physical vector. -/
theorem dyadicCriticalPacket_error_norm_sq_le (N : ℕ) (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f -
        dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f))‖ ^ 2 ≤
      (1 / 2 : ℝ) ^ N * ‖f‖ ^ 2 := by
  rw [dyadicCriticalPacket_error_eq]
  have hq := dyadicQuotientProjection_norm_le (orbit dyadicHalfAdjoint f N)
  have hs := dyadicHalfAdjoint_orbit_norm_sq_le f N
  nlinarith [norm_nonneg (dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)),
    norm_nonneg (orbit dyadicHalfAdjoint f N)]

theorem dyadicProjectedStep_packet_error_norm_sq_le (N m : ℕ) (hm : 0 < m) :
    ‖dyadicProjectedStep m hm -
        dyadicQuotientProjection
          (dyadicKernelDefect (dyadicAdjointPacket N (hilbertDilation m hm hilbertOne)))‖ ^ 2 ≤
      (1 / 2 : ℝ) ^ N * m := by
  simpa only [dyadicProjectedStep, hilbertDilation_norm_sq, hilbertOne_norm_sq, mul_one]
    using dyadicCriticalPacket_error_norm_sq_le N (hilbertDilation m hm hilbertOne)


/-- Exact critical energy, including both the signed terminal interaction and its square. -/
theorem dyadicCriticalPacket_norm_sq_eq (N : ℕ) (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖ ^ 2 =
      (1 / 2 : ℝ) * ‖dyadicKernelDefect (dyadicAdjointPacket N f)‖ ^ 2 +
      2 * inner ℝ
        (dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)))
        (dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)) +
      ‖dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)‖ ^ 2 := by
  have he := dyadicCriticalPacket_error_eq N f
  have hsum : dyadicQuotientProjection f =
      dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) +
      dyadicQuotientProjection (orbit dyadicHalfAdjoint f N) := by
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  calc
    _ = ‖dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) +
        dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)‖ ^ 2 := congrArg (fun x => ‖x‖ ^ 2) hsum
    _ = _ := by
      rw [norm_add_sq_real, dyadicQuotientProjection_kernel_norm_sq _
        (dyadicKernelDefect_adjoint_zero _)]

/-- Increasing the cutoff genuinely converges to the physical quotient vector. -/
theorem dyadicCriticalPacket_tendsto (f : ThresholdHilbert) :
    Filter.Tendsto (fun N => dyadicQuotientProjection
      (dyadicKernelDefect (dyadicAdjointPacket N f))) Filter.atTop
      (nhds (dyadicQuotientProjection f)) := by
  have hg : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N * ‖f‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (‖f‖ ^ 2)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hg.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [hs] with N hN
  rw [dist_eq_norm, norm_sub_rev]
  have hb := dyadicCriticalPacket_error_norm_sq_le N f
  nlinarith [norm_nonneg (dyadicQuotientProjection f -
    dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)))]

/-- A dyadic cutoff above the integer step index gives a scale-free accuracy certificate. -/
theorem dyadicProjectedStep_packet_error_norm_sq_le_of_le_two_pow
    (N K m : ℕ) (hm : 0 < m) (hmN : m ≤ 2 ^ N) :
    ‖dyadicProjectedStep m hm -
        dyadicQuotientProjection (dyadicKernelDefect
          (dyadicAdjointPacket (N + K) (hilbertDilation m hm hilbertOne)))‖ ^ 2 ≤
      (1 / 2 : ℝ) ^ K := by
  have hmR : (m : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hmN
  have hb : (1 / 2 : ℝ) ^ N * m ≤ 1 := by
    calc
      _ = (m : ℝ) / (2 : ℝ) ^ N := by rw [div_pow]; ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr hmR
  calc
    _ ≤ (1 / 2 : ℝ) ^ (N + K) * m :=
      dyadicProjectedStep_packet_error_norm_sq_le (N + K) m hm
    _ = (1 / 2 : ℝ) ^ K * ((1 / 2 : ℝ) ^ N * m) := by rw [pow_add]; ring
    _ ≤ (1 / 2 : ℝ) ^ K * 1 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := mul_one _

end
end RiemannResearch.RH.Pareto

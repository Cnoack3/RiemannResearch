import RiemannResearch.RH.DyadicCriticalApproximation
import RiemannResearch.RH.DyadicResidueAdjointBlocks

/-!
# Finite-depth quotient control from arithmetic kernel blocks

Source: user-provided DyadicResidueKernelVerification20260910(1).md,
September 10, 2026, finite-residual growth argument.

The exact physical reconstruction established in `DyadicCriticalApproximation`
retains the terminal vector and its full signed interaction. Here its norm is
bounded after that equality has been proved. A bound C on each of the first N
actual kernel blocks gives N C / sqrt 2 plus the actual terminal norm.

For an integer dilation m ≤ 2^N, contraction bounds the terminal norm by the
undilated norm. The unconditional triadic block estimate consequently gives
‖Q T_m R₃‖ ≤ 4 N / sqrt 2 + ‖R₃‖. This is a logarithmic depth estimate, not a
uniform arithmetic packet estimate or a proof of RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.Analysis.AbelCoboundary

noncomputable section

/-- The exact critical factor on every actual kernel-defect vector. -/
theorem dyadicQuotientProjection_kernelDefect_norm (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection (dyadicKernelDefect f)‖ =
      ‖dyadicKernelDefect f‖ / Real.sqrt 2 := by
  have he := dyadicQuotientProjection_kernel_norm_sq
    (dyadicKernelDefect f) (dyadicKernelDefect_adjoint_zero f)
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (eq_div_iff (ne_of_gt hp)).mpr
  have heq : (‖dyadicQuotientProjection (dyadicKernelDefect f)‖ * Real.sqrt 2) ^ 2 =
      ‖dyadicKernelDefect f‖ ^ 2 := by
    rw [mul_pow, hs]
    nlinarith [he]
  have hn := mul_nonneg
    (norm_nonneg (dyadicQuotientProjection (dyadicKernelDefect f))) hp.le
  exact (sq_eq_sq₀ hn (norm_nonneg (dyadicKernelDefect f))).mp heq

/-- The finite adjoint packet is exactly the sum of the half-adjoint blocks. -/
theorem dyadicKernelDefect_packet_eq_sum_halfAdjoint
    (N : ℕ) (f : ThresholdHilbert) :
    dyadicKernelDefect (dyadicAdjointPacket N f) =
      ∑ j ∈ Finset.range N, dyadicKernelDefect (orbit dyadicHalfAdjoint f j) := by
  simp only [dyadicAdjointPacket, map_sum, dyadicHalfAdjoint_orbit_eq, map_smul]

/-- A general finite-packet estimate, before any arithmetic specialization. -/
theorem dyadicKernelDefect_packet_norm_le_sum_halfAdjoint
    (N : ℕ) (f : ThresholdHilbert) :
    ‖dyadicKernelDefect (dyadicAdjointPacket N f)‖ ≤
      ∑ j ∈ Finset.range N, ‖dyadicKernelDefect (orbit dyadicHalfAdjoint f j)‖ := by
  rw [dyadicKernelDefect_packet_eq_sum_halfAdjoint]
  exact norm_sum_le _ _

/-- The finite critical norm estimate keeps the actual terminal norm. -/
theorem dyadicQuotientProjection_norm_le_kernel_sum_add_terminal
    (N : ℕ) (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖ ≤
      (∑ j ∈ Finset.range N, ‖dyadicKernelDefect (orbit dyadicHalfAdjoint f j)‖) /
          Real.sqrt 2 + ‖orbit dyadicHalfAdjoint f N‖ := by
  have he := dyadicCriticalPacket_error_eq N f
  have hrecon : dyadicQuotientProjection f =
      dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) +
        dyadicQuotientProjection (orbit dyadicHalfAdjoint f N) := by
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  calc
    _ = ‖dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f)) +
          dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)‖ :=
      congrArg (fun x => ‖x‖) hrecon
    _ ≤ ‖dyadicQuotientProjection (dyadicKernelDefect (dyadicAdjointPacket N f))‖ +
          ‖dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)‖ := norm_add_le _ _
    _ = ‖dyadicKernelDefect (dyadicAdjointPacket N f)‖ / Real.sqrt 2 +
          ‖dyadicQuotientProjection (orbit dyadicHalfAdjoint f N)‖ := by
      rw [dyadicQuotientProjection_kernelDefect_norm]
    _ ≤ (∑ j ∈ Finset.range N, ‖dyadicKernelDefect (orbit dyadicHalfAdjoint f j)‖) /
          Real.sqrt 2 + ‖orbit dyadicHalfAdjoint f N‖ := by
      exact add_le_add
        (div_le_div_of_nonneg_right
          (dyadicKernelDefect_packet_norm_le_sum_halfAdjoint N f) (Real.sqrt_nonneg 2))
        (dyadicQuotientProjection_norm_le _)

/-- Bounded actual kernel blocks give depth-linear control with a retained tail. -/
theorem dyadicQuotientProjection_norm_le_of_kernel_blocks
    (N : ℕ) (f : ThresholdHilbert) (C : ℝ)
    (hblocks : ∀ j < N, ‖dyadicKernelDefect (orbit dyadicHalfAdjoint f j)‖ ≤ C) :
    ‖dyadicQuotientProjection f‖ ≤
      (N : ℝ) * C / Real.sqrt 2 + ‖orbit dyadicHalfAdjoint f N‖ := by
  have hsum : (∑ j ∈ Finset.range N,
      ‖dyadicKernelDefect (orbit dyadicHalfAdjoint f j)‖) ≤ (N : ℝ) * C := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, C :=
        Finset.sum_le_sum (fun j hj => hblocks j (Finset.mem_range.mp hj))
      _ = _ := by simp
  exact (dyadicQuotientProjection_norm_le_kernel_sum_add_terminal N f).trans
    (add_le_add
      (div_le_div_of_nonneg_right hsum (Real.sqrt_nonneg 2)) le_rfl)

/-- Above the dilation scale, the terminal norm is at most the seed norm. -/
theorem dyadicHalfAdjoint_dilation_orbit_norm_le_of_le_two_pow
    (N m : ℕ) (hm : 0 < m) (hmN : m ≤ 2 ^ N) (f : ThresholdHilbert) :
    ‖orbit dyadicHalfAdjoint (hilbertDilation m hm f) N‖ ≤ ‖f‖ := by
  have hmR : (m : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hmN
  have hb : (1 / 2 : ℝ) ^ N * m ≤ 1 := by
    calc
      _ = (m : ℝ) / (2 : ℝ) ^ N := by rw [div_pow]; ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr hmR
  have hs := dyadicHalfAdjoint_orbit_norm_sq_le (hilbertDilation m hm f) N
  rw [hilbertDilation_norm_sq] at hs
  have hsq : ‖orbit dyadicHalfAdjoint (hilbertDilation m hm f) N‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ N * ((m : ℝ) * ‖f‖ ^ 2) := hs
      _ = ((1 / 2 : ℝ) ^ N * (m : ℝ)) * ‖f‖ ^ 2 := by ring
      _ ≤ 1 * ‖f‖ ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
      _ = _ := one_mul _
  nlinarith [norm_nonneg f,
    norm_nonneg (orbit dyadicHalfAdjoint (hilbertDilation m hm f) N)]

/-- An arithmetic application of the general finite critical packet estimate. -/
theorem dyadicQuotientProjection_dilation_norm_le_of_kernel_blocks
    (N m : ℕ) (hm : 0 < m) (hmN : m ≤ 2 ^ N) (f : ThresholdHilbert) (C : ℝ)
    (hblocks : ∀ j < N,
      ‖dyadicKernelDefect (orbit dyadicHalfAdjoint (hilbertDilation m hm f) j)‖ ≤ C) :
    ‖dyadicQuotientProjection (hilbertDilation m hm f)‖ ≤
      (N : ℝ) * C / Real.sqrt 2 + ‖f‖ := by
  exact (dyadicQuotientProjection_norm_le_of_kernel_blocks N
    (hilbertDilation m hm f) C hblocks).trans
      (add_le_add le_rfl
        (dyadicHalfAdjoint_dilation_orbit_norm_le_of_le_two_pow N m hm hmN f))

/-- Unconditional logarithmic-depth growth for the actual triadic residue. -/
theorem dyadicQuotientProjection_triadicResidue_norm_le_depth
    (N m : ℕ) (hm : 0 < m) (hmN : m ≤ 2 ^ N) :
    ‖dyadicQuotientProjection
      (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))‖ ≤
      4 * (N : ℝ) / Real.sqrt 2 + ‖hilbertResidue 3 (by norm_num)‖ := by
  have hb := dyadicQuotientProjection_dilation_norm_le_of_kernel_blocks
    N m hm hmN (hilbertResidue 3 (by norm_num)) 4
    (fun j _ => dyadicKernelDefect_halfAdjoint_triadicResidue_norm_le m hm j)
  simpa only [mul_comm (N : ℝ) 4] using hb

end
end RiemannResearch.RH.Pareto

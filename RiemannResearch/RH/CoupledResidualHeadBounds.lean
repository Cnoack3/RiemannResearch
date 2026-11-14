import RiemannResearch.RH.CoupledResidualCorrections
import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Unconditional head bounds for the actual coupled residual gain

Source: user-requested residual-projection investigation, 14 November 2026.
The exact signed binary and ternary source identities are imported from
`CoupledResidualCorrections`. Cauchy--Schwarz bounds only their dilation terms.
The resulting positive-part lower bounds concern the actual residual and the
actual doubled budget, without RH or an approximation-rate hypothesis.

These estimates can be zero. They do not establish a stage-independent
logarithmic projection bound: quantitative control of the signed head terms
is still needed. The complete source identities remain the primary results.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket

/-- Binary lower source estimate, with the first head coordinate retained. -/
def binaryHeadLower (M : ℕ) : ℝ :=
  (2 - Real.sqrt 2) * distance M - hilbertSequence (error M) 1

/-- Ternary lower source estimate. The floor at the earlier scale is exact. -/
def ternaryHeadLower (M : ℕ) : ℝ :=
  3 * distance M - (3 / 2 : ℝ) * hilbertSequence (error M) 1 -
    (1 / 2 : ℝ) * hilbertSequence (error M) 2 -
    Real.sqrt 3 * ‖error M‖ * ‖error (2 * M / 3)‖

theorem binaryHeadLower_le_source (M : ℕ) :
    binaryHeadLower M ≤ source M 2 (by omega) := by
  have h := real_inner_le_norm (error M) (hilbertDilation 2 (by omega) (error M))
  rw [hilbertDilation_norm] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [binary_source]
  dsimp only [binaryHeadLower, distance]
  nlinarith

theorem ternaryHeadLower_le_source (M : ℕ) :
    ternaryHeadLower M ≤ source M 3 (by omega) := by
  have h := real_inner_le_norm (error M)
    (hilbertDilation 3 (by omega) (error (2 * M / 3)))
  rw [hilbertDilation_norm] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [ternary_source]
  dsimp only [ternaryHeadLower]
  nlinarith

private theorem positivePart_sq_le {a s : ℝ} (h : a ≤ s) :
    (max 0 a) ^ 2 ≤ s ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ s + a)]
  · rw [max_eq_left (le_of_not_ge ha)]
    simpa using sq_nonneg s

/-- An unconditional lower bound, including zero prior gain and zero positive part. -/
theorem binary_positivePart_gain (M : ℕ) :
    (max 0 (binaryHeadLower M)) ^ 2 ≤ 2 * priorGain M 2 * gain M := by
  have h := interscale_source_sq M 2 (by omega)
  norm_num only [Nat.cast_ofNat] at h
  exact (positivePart_sq_le (binaryHeadLower_le_source M)).trans h

theorem ternary_positivePart_gain (M : ℕ) :
    (max 0 (ternaryHeadLower M)) ^ 2 ≤ 3 * priorGain M 3 * gain M := by
  have h := interscale_source_sq M 3 (by omega)
  norm_num only [Nat.cast_ofNat] at h
  exact (positivePart_sq_le (ternaryHeadLower_le_source M)).trans h

/-- A source lower certificate computed from the two head coordinates and earlier errors. -/
def headSourceSquare (M : ℕ) : ℝ :=
  (max 0 (binaryHeadLower M)) ^ 2 + (max 0 (ternaryHeadLower M)) ^ 2

theorem headSourceSquare_le_sourceSquare (M : ℕ) :
    headSourceSquare M ≤ sourceSquare M := by
  exact add_le_add (positivePart_sq_le (binaryHeadLower_le_source M))
    (positivePart_sq_le (ternaryHeadLower_le_source M))

/-- Undivided lower bound: valid even when the trace vanishes. -/
theorem headSourceSquare_le_trace_gain (M : ℕ) :
    headSourceSquare M ≤ trace M * gain M := by
  have h2 := binary_positivePart_gain M
  have h3 := ternary_positivePart_gain M
  dsimp only [headSourceSquare, trace]
  nlinarith

/-- The resulting unconditional lower bound for the actual residual-projection energy. -/
theorem gain_ge_headSourceSquare_div_trace (M : ℕ) (htrace : 0 < trace M) :
    headSourceSquare M / trace M ≤ gain M := by
  apply (div_le_iff₀ htrace).mpr
  simpa only [mul_comm] using headSourceSquare_le_trace_gain M

/-- Exact identification with the residual projection in the user's estimate. -/
theorem projected_error_norm_sq_eq_gain (M : ℕ) :
    ‖(budgetHilbert (2 * M)).starProjection (error M)‖ ^ 2 = gain M := by
  have hmem : fit M ∈ budgetHilbert (2 * M) :=
    budgetHilbert_mono (by omega : M ≤ 2 * M)
      ((budgetHilbert M).starProjection_apply_mem hilbertOne)
  have hp : (budgetHilbert (2 * M)).starProjection (fit M) = fit M :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  have he : (budgetHilbert (2 * M)).starProjection (error M) =
      fit (2 * M) - fit M := by
    rw [error, map_sub, hp]
    rfl
  rw [he]
  exact (distance_sub M (2 * M) (by omega)).symm

theorem residual_projection_ge_head_certificate (M : ℕ) (htrace : 0 < trace M) :
    headSourceSquare M / trace M ≤
      ‖(budgetHilbert (2 * M)).starProjection (error M)‖ ^ 2 := by
  rw [projected_error_norm_sq_eq_gain]
  exact gain_ge_headSourceSquare_div_trace M htrace

/-- Failure of gain forces a concrete signed head obstruction. -/
theorem binary_head_obstruction_of_zero_gain (M : ℕ) (hgain : gain M = 0) :
    (2 - Real.sqrt 2) * distance M ≤ hilbertSequence (error M) 1 := by
  have h := binary_positivePart_gain M
  rw [hgain, mul_zero] at h
  have hz : max 0 (binaryHeadLower M) = 0 := by
    nlinarith [sq_nonneg (max 0 (binaryHeadLower M))]
  have hm := le_max_right (0 : ℝ) (binaryHeadLower M)
  rw [hz] at hm
  dsimp only [binaryHeadLower] at hm
  linarith

/-- A checkable sufficient head certificate for a prescribed logarithmic gain.
The certificate is a hypothesis, not an unconditional arithmetic provider. -/
theorem logarithmic_gain_of_head_certificate (M : ℕ) (C L : ℝ)
    (hC : 0 < C) (hL : 1 < L) (htrace : 0 < trace M)
    (hhead : distance M * trace M ≤ C * Real.log L * headSourceSquare M) :
    distance M / (C * Real.log L) ≤ gain M := by
  have hscale : 0 < C * Real.log L := mul_pos hC (Real.log_pos hL)
  apply (div_le_iff₀ hscale).mpr
  apply le_of_mul_le_mul_right ?_ htrace
  calc
    distance M * trace M ≤ C * Real.log L * headSourceSquare M := hhead
    _ ≤ C * Real.log L * (trace M * gain M) :=
      mul_le_mul_of_nonneg_left (headSourceSquare_le_trace_gain M) hscale.le
    _ = gain M * (C * Real.log L) * trace M := by ring

end RiemannResearch.RH.Pareto.CoupledResidual

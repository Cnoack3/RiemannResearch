import RiemannResearch.RH.CriticalMellinCellAsymptotics
import RiemannResearch.RH.HarmonicToeplitz
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Logarithmic means of imaginary powers

Source: user-provided critical Mellin mixture argument. The proof uses
discrete telescoping and harmonic Toeplitz convergence, rather than an
unproved estimate for oscillatory power sums.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction

def powerPhase (t : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1) ^ (-(t : ℂ) * Complex.I)

theorem powerPhase_norm (t : ℝ) (n : ℕ) : ‖powerPhase t n‖ = 1 := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [powerPhase, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem powerPhase_div (t : ℝ) (n : ℕ) :
    ((n : ℂ) + 1) ^ (-1 - (t : ℂ) * Complex.I) =
      powerPhase t n / ((n : ℂ) + 1) := by
  have hx : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have he : (-1 - (t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I - 1 := by ring
  rw [he, Complex.cpow_sub _ _ hx, Complex.cpow_one]
  rfl

theorem powerPhase_difference (t : ℝ) (n : ℕ) :
    powerPhase t n - powerPhase t (n + 1) =
      powerPhase t n / ((n : ℂ) + 1) * cellSlope ((t : ℂ) * Complex.I) n := by
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hx0 : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have hprod : (x : ℂ) * ((1 + 1 / x : ℝ) : ℂ) = (n : ℂ) + 2 := by
    dsimp [x]
    push_cast
    field_simp
    <;> ring
  have hp := Complex.mul_cpow_ofReal_nonneg hx.le
    (show 0 ≤ 1 + 1 / x by positivity) (-(t : ℂ) * Complex.I)
  rw [hprod] at hp
  have hxcast : (x : ℂ) = (n : ℂ) + 1 := by simp [x]
  rw [hxcast] at hp
  simp only [powerPhase, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℂ) + 1 + 1 = (n : ℂ) + 2 by ring, hp]
  simp only [cellSlope, neg_mul]
  dsimp [x] at *
  field_simp [hx0]
  <;> ring

theorem powerPhase_difference_sum (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (powerPhase t n - powerPhase t (n + 1))) =
      1 - powerPhase t N := by
  induction N with
  | zero => simp [powerPhase]
  | succ N hN =>
      rw [Finset.sum_range_succ, hN]
      ring

def phaseSlopeError (t : ℝ) (n : ℕ) : ℂ :=
  powerPhase t n * (cellSlope ((t : ℂ) * Complex.I) n - (t : ℂ) * Complex.I)

theorem phaseSlopeError_tendsto (t : ℝ) :
    Tendsto (phaseSlopeError t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := ((cellSlope_tendsto ((t : ℂ) * Complex.I)).sub_const
    ((t : ℂ) * Complex.I)).norm
  simpa only [phaseSlopeError, norm_mul, powerPhase_norm, one_mul,
    sub_self, norm_zero] using hh

theorem phase_sum_exact (t : ℝ) (N : ℕ) :
    ((t : ℂ) * Complex.I) *
        (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (t : ℂ) * Complex.I)) =
      1 - powerPhase t N -
        ∑ n ∈ Finset.range N, phaseSlopeError t n / ((n : ℂ) + 1) := by
  calc
    _ = ∑ n ∈ Finset.range N,
        ((powerPhase t n - powerPhase t (n + 1)) -
          phaseSlopeError t n / ((n : ℂ) + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [powerPhase_div, powerPhase_difference]
      simp only [phaseSlopeError]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, powerPhase_difference_sum]

theorem powerPhase_log_tendsto_zero (t : ℝ) :
    Tendsto (fun N : ℕ => (1 - powerPhase t N) /
      (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ (hlog.const_div_atTop 2)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hp : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by exact_mod_cast
    (show 1 < N + 1 by omega))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  calc
    ‖1 - powerPhase t N‖ ≤ ‖(1 : ℂ)‖ + ‖powerPhase t N‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, powerPhase_norm]; norm_num

/-- Off-diagonal logarithmic orthogonality of the actual imaginary powers.
Only differentiability at one, a telescoping identity, and the proved
harmonic Toeplitz lemma enter the argument. -/
theorem harmonic_phase_offDiagonal (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (t : ℂ) * Complex.I)) /
        (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 0) := by
  have hs : (t : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have herr := harmonic_toeplitz_zero (phaseSlopeError t) (phaseSlopeError_tendsto t)
  have hlim := (powerPhase_log_tendsto_zero t).sub herr
  have hmul : Tendsto (fun N : ℕ => ((t : ℂ) * Complex.I) *
      ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (t : ℂ) * Complex.I)) /
        (Real.log ((N : ℝ) + 1) : ℂ))) atTop (𝓝 0) := by
    convert hlim using 1
    · ext N
      rw [← sub_div, ← phase_sum_exact]
      ring
    · simp
  have hfinal := hmul.const_mul (((t : ℂ) * Complex.I)⁻¹)
  simpa only [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_zero] using hfinal

/-- The complete diagonal/off-diagonal logarithmic power mean. -/
theorem harmonic_phase_tendsto (t : ℝ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - (t : ℂ) * Complex.I)) /
        (Real.log ((N : ℝ) + 1) : ℂ)) atTop (𝓝 (if t = 0 then 1 else 0)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero, Complex.cpow_neg_one,
      one_div, if_pos rfl, ite_true] using harmonic_diagonal_tendsto
  · simpa only [if_neg ht] using harmonic_phase_offDiagonal t ht

end RiemannResearch.RH.Pareto.SpectralObstruction

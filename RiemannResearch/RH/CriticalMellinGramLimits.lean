import RiemannResearch.RH.LogarithmicPowerMeans

/-!
# Actual critical Mellin Gram limits

Source: user-provided critical Mellin mixture argument, 21 September 2026.
The exact cell-slope factorization reduces the actual weighted Gram entries
to logarithmic power means and a proved harmonic Toeplitz error.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

def criticalCross (t u : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, (paretoWeight n : ℂ) *
    mellinMode (MellinFrequency.criticalPoint t) n *
      star (mellinMode (MellinFrequency.criticalPoint u) n)) /
    (Real.log ((N : ℝ) + 1) : ℂ)

def crossSlope (t u : ℝ) (n : ℕ) : ℂ :=
  (1 + 1 / ((n : ℂ) + 1)) * cellSlope (MellinFrequency.criticalPoint t) n *
    star (cellSlope (MellinFrequency.criticalPoint u) n)

def crossSlopeError (t u : ℝ) (n : ℕ) : ℂ :=
  powerPhase (t - u) n * (crossSlope t u n -
    MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u))

theorem crossSlope_tendsto (t u : ℝ) :
    Tendsto (crossSlope t u) atTop
      (𝓝 (MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u))) := by
  have he : Tendsto (fun n : ℕ => (1 : ℂ) + 1 / ((n : ℂ) + 1)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0))
  change Tendsto (fun n : ℕ =>
    (1 + 1 / ((n : ℂ) + 1)) * cellSlope (MellinFrequency.criticalPoint t) n *
      star (cellSlope (MellinFrequency.criticalPoint u) n)) atTop
      (𝓝 (MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u)))
  simpa only [one_mul] using
    (he.mul (cellSlope_tendsto (MellinFrequency.criticalPoint t))).mul
      (cellSlope_tendsto (MellinFrequency.criticalPoint u)).star

theorem crossSlopeError_tendsto (t u : ℝ) :
    Tendsto (crossSlopeError t u) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := ((crossSlope_tendsto t u).sub_const
    (MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u))).norm
  simpa only [crossSlopeError, norm_mul, powerPhase_norm, one_mul,
    sub_self, norm_zero] using hh

private theorem conj_real_cpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
    star ((x : ℂ) ^ s) = (x : ℂ) ^ (star s) := by
  have harg : Complex.arg (x : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  simpa only [Complex.star_def, Complex.conj_ofReal] using
    (Complex.cpow_conj (x : ℂ) s harg).symm

theorem criticalCross_term_eq (t u : ℝ) (n : ℕ) :
    (paretoWeight n : ℂ) * mellinMode (MellinFrequency.criticalPoint t) n *
      star (mellinMode (MellinFrequency.criticalPoint u) n) =
    powerPhase (t - u) n * crossSlope t u n / ((n : ℂ) + 1) := by
  let x : ℝ := (n : ℝ) + 1
  let y : ℝ := (n : ℝ) + 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hxcast : (x : ℂ) = (n : ℂ) + 1 := by simp [x]
  have hycast : (y : ℂ) = (n : ℂ) + 2 := by simp [y]
  have hc : star (((n : ℂ) + 1) ^ (-MellinFrequency.criticalPoint u)) =
      ((n : ℂ) + 1) ^ (-star (MellinFrequency.criticalPoint u)) := by
    rw [← hxcast, conj_real_cpow x hx]
    simp only [star_neg]
  have he : -MellinFrequency.criticalPoint t - star (MellinFrequency.criticalPoint u) =
      -1 - ((t - u : ℝ) : ℂ) * Complex.I := by
    simp [MellinFrequency.criticalPoint, Complex.star_def]
    ring
  have hp : ((n : ℂ) + 1) ^ (-MellinFrequency.criticalPoint t) *
      ((n : ℂ) + 1) ^ (-star (MellinFrequency.criticalPoint u)) =
      powerPhase (t - u) n / ((n : ℂ) + 1) := by
    rw [← Complex.cpow_add _ _ (by simpa only [hxcast] using hx0)]
    rw [show -MellinFrequency.criticalPoint t + -star (MellinFrequency.criticalPoint u) =
      -MellinFrequency.criticalPoint t - star (MellinFrequency.criticalPoint u) by ring]
    rw [he, powerPhase_div]
  rw [mellinMode_eq_cellSlope, mellinMode_eq_cellSlope]
  simp only [star_mul]
  have hyreal : star ((n : ℂ) + 2) = (n : ℂ) + 2 := by simp [Complex.star_def]
  rw [hyreal, hc]
  have hweight : (paretoWeight n : ℂ) = 1 / ((x : ℂ) * (y : ℂ)) := by
    simp [paretoWeight, x, y]
  rw [hweight]
  calc
    _ = ((y : ℂ) / (x : ℂ)) *
        (((n : ℂ) + 1) ^ (-MellinFrequency.criticalPoint t) *
          ((n : ℂ) + 1) ^ (-star (MellinFrequency.criticalPoint u))) *
        cellSlope (MellinFrequency.criticalPoint t) n *
          star (cellSlope (MellinFrequency.criticalPoint u) n) := by
      rw [← hycast]
      field_simp [hx0, hy0]
      <;> ring
    _ = _ := by
      rw [hp, crossSlope]
      rw [hxcast, hycast]
      field_simp [show (n : ℂ) + 1 ≠ 0 by simpa only [hxcast] using hx0]
      <;> ring

theorem criticalCross_decomposition (t u : ℝ) (N : ℕ) :
    criticalCross t u N =
      (MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u)) *
        ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-1 - ((t - u : ℝ) : ℂ) * Complex.I)) /
          (Real.log ((N : ℝ) + 1) : ℂ)) +
      (∑ n ∈ Finset.range N, crossSlopeError t u n / ((n : ℂ) + 1)) /
        (Real.log ((N : ℝ) + 1) : ℂ) := by
  rw [criticalCross, ← mul_div_assoc, ← add_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [criticalCross_term_eq, powerPhase_div]
  simp only [crossSlopeError]
  ring

theorem criticalCross_tendsto (t u : ℝ) :
    Tendsto (criticalCross t u) atTop
      (𝓝 (if t = u then MellinFrequency.criticalPoint t *
        star (MellinFrequency.criticalPoint u) else 0)) := by
  have hp := (harmonic_phase_tendsto (t - u)).const_mul
    (MellinFrequency.criticalPoint t * star (MellinFrequency.criticalPoint u))
  have he := harmonic_toeplitz_zero (crossSlopeError t u) (crossSlopeError_tendsto t u)
  have hh := hp.add he
  simpa only [← criticalCross_decomposition, sub_eq_zero, mul_ite, mul_one, mul_zero,
    add_zero] using hh

theorem crossSlope_norm_le (t u : ℝ) (n : ℕ) :
    ‖crossSlope t u n‖ ≤ 2 * ‖MellinFrequency.criticalPoint t‖ *
      ‖MellinFrequency.criticalPoint u‖ := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hh : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one hx).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hnorm : ‖(1 : ℂ) + 1 / ((n : ℂ) + 1)‖ = 1 + 1 / ((n : ℝ) + 1) := by
    have he : (1 : ℂ) + 1 / ((n : ℂ) + 1) =
        ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by simp
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [crossSlope, norm_mul, norm_mul, norm_star, hnorm]
  have ht := cellSlope_norm_le (MellinFrequency.criticalPoint t) (by simp) n
  have hu := cellSlope_norm_le (MellinFrequency.criticalPoint u) (by simp) n
  gcongr
  linarith

theorem reciprocal_le_twice_log_increment (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤
      2 * (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) := by
  let x : ℝ := (n : ℝ) + 1
  let y : ℝ := (n : ℝ) + 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hlog
  have he : 1 - (y / x)⁻¹ = 1 / y := by
    dsimp [x, y]
    field_simp
    <;> ring
  rw [he] at hlog
  have hr : 1 / x ≤ 2 / y := by
    apply (div_le_div_iff₀ hx hy).2
    dsimp [x, y]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hr' : 1 / x ≤ 2 * (1 / y) := by simpa only [mul_one_div] using hr
  change 1 / x ≤ 2 * (Real.log y - Real.log x)
  linarith only [hr', hlog]

theorem realHarmonicSum_le_twice_log (N : ℕ) :
    realHarmonicSum N ≤ 2 * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [realHarmonicSum]
  | succ N hN =>
      have he : realHarmonicSum (N + 1) = realHarmonicSum N + 1 / ((N : ℝ) + 1) := by
        simp only [realHarmonicSum, Finset.sum_range_succ]
      rw [he]
      have hh := reciprocal_le_twice_log_increment N
      have hc : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by push_cast; ring
      rw [hc]
      linarith

theorem criticalCross_norm_le (t u : ℝ) (N : ℕ) :
    ‖criticalCross t u N‖ ≤ 4 * ‖MellinFrequency.criticalPoint t‖ *
      ‖MellinFrequency.criticalPoint u‖ := by
  by_cases hN : N = 0
  · subst N
    simpa only [criticalCross, Finset.range_zero, Finset.sum_empty, zero_div, norm_zero]
      using (show 0 ≤ 4 * ‖MellinFrequency.criticalPoint t‖ *
        ‖MellinFrequency.criticalPoint u‖ by positivity)
  have hlog : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    linarith
  rw [criticalCross, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  apply (div_le_iff₀ hlog).2
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖(paretoWeight n : ℂ) * mellinMode (MellinFrequency.criticalPoint t) n *
          star (mellinMode (MellinFrequency.criticalPoint u) n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        (2 * ‖MellinFrequency.criticalPoint t‖ * ‖MellinFrequency.criticalPoint u‖) /
          ((n : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [criticalCross_term_eq, norm_div, norm_mul, powerPhase_norm, one_mul]
      have hc : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
        have he : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by simp
        rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hc]
      exact div_le_div_of_nonneg_right (crossSlope_norm_le t u n) (by positivity)
    _ = (2 * ‖MellinFrequency.criticalPoint t‖ * ‖MellinFrequency.criticalPoint u‖) *
        realHarmonicSum N := by
      simp only [realHarmonicSum, Finset.mul_sum, mul_one_div]
    _ ≤ (2 * ‖MellinFrequency.criticalPoint t‖ * ‖MellinFrequency.criticalPoint u‖) *
        (2 * Real.log ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (realHarmonicSum_le_twice_log N) (by positivity)
    _ = _ := by ring

end RiemannResearch.RH.Pareto.SpectralObstruction

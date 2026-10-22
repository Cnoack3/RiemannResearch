import RiemannResearch.RH.ParetoMellinObstructionTargets
import RiemannResearch.RH.ThresholdHilbertSpace

namespace RiemannResearch.RH.Pareto.CompressedMellin
open scoped BigOperators
noncomputable section

/-- Sharp real-Hilbert to complex-valued weighted Cauchy inequality. The real
carrier causes no factor-two loss: use the real magnitude of the complex kernel. -/
theorem weighted_complex_pairing_norm_bound
    (u : ℕ → ℂ) (hu : Summable (fun n => paretoWeight n * ‖u n‖^2))
    (f : ThresholdHilbert) :
    Summable (fun n => (((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))) ∧
    ‖∑' n, (((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))‖ ≤
      ‖f‖ * Real.sqrt (∑' n, paretoWeight n * ‖u n‖^2) := by
  have hw (n : ℕ) : 0 ≤ paretoWeight n := by unfold paretoWeight; positivity
  have hwpos (n : ℕ) : 0 < paretoWeight n := by unfold paretoWeight; positivity
  let g : ThresholdHilbert := ⟨fun n => Real.sqrt (paretoWeight n) * ‖u n‖, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (hw _)] using hu⟩
  have hc : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hhold := lp.tsum_mul_le_mul_norm
    (p := 2) (q := 2) (by simpa using hc) f g
  have hterm (n : ℕ) :
      ‖(((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))‖ =
        ‖f n‖ * ‖g n‖ := by
    have hsq : Real.sqrt (paretoWeight n) ≠ 0 :=
      (Real.sqrt_pos.mpr (hwpos n)).ne'
    have hquot : paretoWeight n / Real.sqrt (paretoWeight n) =
        Real.sqrt (paretoWeight n) := by
      apply (div_eq_iff hsq).2
      simpa only [pow_two] using (Real.sq_sqrt (hw n)).symm
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      hilbertSequence_succ, abs_mul, abs_div, abs_of_nonneg (hw n),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Real.norm_eq_abs]
    change paretoWeight n * (|f n| / Real.sqrt (paretoWeight n)) * ‖u n‖ =
      |f n| * |Real.sqrt (paretoWeight n) * ‖u n‖|
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (norm_nonneg _)]
    calc
      _ = |f n| * (paretoWeight n / Real.sqrt (paretoWeight n)) * ‖u n‖ := by ring
      _ = _ := by rw [hquot]; ring
  have hsumNorm : Summable (fun n =>
      ‖(((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))‖) := by
    simpa only [hterm] using hhold.1
  have hg : ‖g‖^2 = ∑' n, paretoWeight n * ‖u n‖^2 := by
    rw [hilbert_norm_sq]
    apply tsum_congr
    intro n
    change (Real.sqrt (paretoWeight n) * ‖u n‖)^2 = _
    rw [mul_pow, Real.sq_sqrt (hw n)]
  have hgsqrt : Real.sqrt (∑' n, paretoWeight n * ‖u n‖^2) = ‖g‖ := by
    rw [← hg, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨hsumNorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' n, ‖(((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))‖ :=
      norm_tsum_le_tsum_norm hsumNorm
    _ = ∑' n, ‖f n‖ * ‖g n‖ := tsum_congr hterm
    _ ≤ ‖f‖ * ‖g‖ := hhold.2
    _ = _ := by rw [hgsqrt]

/-- Any real-linear functional with this actual weighted complex kernel has
operator norm bounded by the complete kernel energy. -/
theorem weighted_complex_operator_norm_sq_le
    (L : ThresholdHilbert →L[ℝ] ℂ) (u : ℕ → ℂ)
    (hu : Summable (fun n => paretoWeight n * ‖u n‖^2))
    (hL : ∀ f, L f = ∑' n,
      (((paretoWeight n * hilbertSequence f (n+1) : ℝ) : ℂ) * star (u n))) :
    ‖L‖^2 ≤ ∑' n, paretoWeight n * ‖u n‖^2 := by
  have he : 0 ≤ ∑' n, paretoWeight n * ‖u n‖^2 := by
    apply tsum_nonneg
    intro n
    unfold paretoWeight
    positivity
  have hn : ‖L‖ ≤ Real.sqrt (∑' n, paretoWeight n * ‖u n‖^2) := by
    apply L.opNorm_le_bound (Real.sqrt_nonneg _)
    intro f
    rw [hL f]
    simpa only [mul_comm] using (weighted_complex_pairing_norm_bound u hu f).2
  nlinarith [Real.sq_sqrt he, norm_nonneg L]

end
end RiemannResearch.RH.Pareto.CompressedMellin

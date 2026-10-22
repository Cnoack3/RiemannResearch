import RiemannResearch.RH.MellinModeResiduePairing
import RiemannResearch.Analysis.MellinDifferenceBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FunProp

/-!
# Absolutely convergent residue pairings of compact-frequency mixtures

Source: user-provided compact-frequency rigidity argument, 2026-09-21,
Section 3. The proof keeps the complex density and every signed mixed term.
The summable majorant is `‖a t‖ * (|σ| + T) * (n + 1)^(-σ-1)`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.SpectralObstruction
open RiemannResearch.Analysis.Cesaro

theorem normalizedResidueCoordinate_norm_le (d n : ℕ) (hd : 2 ≤ d) :
    ‖normalizedResidueCoordinate d n‖ ≤ 1 := by
  rw [normalizedResidueCoordinate, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  apply (div_le_one (show (0 : ℝ) < d by exact_mod_cast (by omega : 0 < d))).mpr
  exact_mod_cast (Nat.le_of_lt (Nat.mod_lt (n + 1) (by omega : 0 < d)))

theorem verticalPoint_norm_le_abs (σ t : ℝ) :
    ‖verticalPoint σ t‖ ≤ |σ| + |t| := by
  unfold verticalPoint
  calc
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤
        ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |σ| + |t| := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem vertical_mellinFirst_continuous (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => mellinFirst (verticalPoint σ t) (n + 1)) := by
  have hc : Continuous (fun t : ℝ => -verticalPoint σ t) := by
    unfold verticalPoint
    fun_prop
  have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (n + 1)
  exact (hc.const_cpow (Or.inl h1)).sub (hc.const_cpow (Or.inl h2))

theorem vertical_mellinFirst_residue_norm_le (σ T t : ℝ)
    (hσ : 0 < σ) (ht : |t| ≤ T) (d n : ℕ) (hd : 2 ≤ d) :
    ‖mellinFirst (verticalPoint σ t) (n + 1) * normalizedResidueCoordinate d n‖ ≤
      (|σ| + T) * ((n : ℝ) + 1) ^ (-σ - 1) := by
  have hp : 0 ≤ ((n : ℝ) + 1) ^ (-σ - 1) := Real.rpow_nonneg (by positivity) _
  have hs : ‖verticalPoint σ t‖ ≤ |σ| + T :=
    (verticalPoint_norm_le_abs σ t).trans (add_le_add le_rfl ht)
  have hfirst : ‖mellinFirst (verticalPoint σ t) (n + 1)‖ ≤
      ‖verticalPoint σ t‖ * ((n : ℝ) + 1) ^ (-σ - 1) := by
    simpa only [verticalPoint_re, Nat.cast_add, Nat.cast_one] using
      mellinFirst_norm_le (verticalPoint σ t) (by simpa using hσ)
        (n + 1) (by omega)
  rw [norm_mul]
  calc
    _ ≤ ‖mellinFirst (verticalPoint σ t) (n + 1)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (normalizedResidueCoordinate_norm_le d n hd)
    _ ≤ ‖verticalPoint σ t‖ * ((n : ℝ) + 1) ^ (-σ - 1) := hfirst
    _ ≤ (|σ| + T) * ((n : ℝ) + 1) ^ (-σ - 1) :=
      mul_le_mul_of_nonneg_right hs hp

/-- A direct HasSum on the actual coordinate mixtures, before rewriting the
integrated arithmetic symbol as a Fourier sampling defect. -/
theorem continuumMixture_residue_hasSum_integral
    (σ T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hdata : CompactFrequencyData σ T μ a) (d : ℕ) (hd : 2 ≤ d) :
    HasSum (fun n => (paretoWeight n : ℂ) * continuumMixture σ μ a n *
      normalizedResidueCoordinate d n)
      (∫ t, a t * ((1 / (d : ℂ) - (d : ℂ) ^ (-verticalPoint σ t)) *
        riemannZeta (verticalPoint σ t)) ∂μ) := by
  rcases hdata with ⟨hσlow, hσhi, hT, hfinite, ha, hcompact⟩
  have hσ : 0 < σ := by linarith
  let F : ℕ → ℝ → ℂ := fun n t =>
    a t * (mellinFirst (verticalPoint σ t) (n + 1) * normalizedResidueCoordinate d n)
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-σ - 1)
  have hq : Summable q := by
    have h := (Real.summable_nat_rpow.mpr (by linarith : -σ - 1 < -1))
    simpa only [q, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have hq0 (n : ℕ) : 0 ≤ q n := Real.rpow_nonneg (by positivity) _
  have hdom (n : ℕ) : ∀ᵐ t ∂μ,
      ‖F n t‖ ≤ ‖a t‖ * ((|σ| + T) * q n) := by
    filter_upwards [hcompact] with t ht
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (vertical_mellinFirst_residue_norm_le σ T t hσ ht d n hd) (norm_nonneg _)
  have hi (n : ℕ) : Integrable (F n) μ := by
    apply (ha.norm.mul_const ((|σ| + T) * q n)).mono'
    · exact ha.aestronglyMeasurable.mul
        ((vertical_mellinFirst_continuous σ n).mul continuous_const).aestronglyMeasurable
    · exact hdom n
  have hb (n : ℕ) : (∫ t, ‖F n t‖ ∂μ) ≤
      ((|σ| + T) * (∫ t, ‖a t‖ ∂μ)) * q n := by
    calc
      _ ≤ ∫ t, ‖a t‖ * ((|σ| + T) * q n) ∂μ :=
        integral_mono_ae (hi n).norm (ha.norm.mul_const _) (hdom n)
      _ = _ := by rw [integral_mul_const]; ring
  have hsum : Summable (fun n => ∫ t, ‖F n t‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hb
      (hq.mul_left ((|σ| + T) * (∫ t, ‖a t‖ ∂μ)))
  have hswap := hasSum_integral_of_summable_integral_norm hi hsum
  have hterm (n : ℕ) : (∫ t, F n t ∂μ) =
      (paretoWeight n : ℂ) * continuumMixture σ μ a n *
        normalizedResidueCoordinate d n := by
    rw [continuumMixture, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [F]
    rw [← weighted_mellinMode_eq]
    ring
  have hpoint (t : ℝ) : (∑' n, F n t) =
      a t * ((1 / (d : ℂ) - (d : ℂ) ^ (-verticalPoint σ t)) *
        riemannZeta (verticalPoint σ t)) := by
    have hs0 : 0 < (verticalPoint σ t).re := by simpa using hσ
    have hs1 : verticalPoint σ t ≠ 1 := by
      intro h
      have he := congrArg Complex.re h
      simp only [verticalPoint_re, Complex.one_re] at he
      linarith
    have h := (mellinMode_residue_hasSum (verticalPoint σ t) hs0 hs1 d hd).mul_left (a t)
    simpa only [weighted_mellinMode_eq, F] using h.tsum_eq
  simpa only [hterm, hpoint] using hswap

end RiemannResearch.RH.Pareto.SpectralObstruction

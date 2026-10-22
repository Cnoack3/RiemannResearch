import RiemannResearch.RH.CriticalMellinGramLimits
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

/-!
# Countable critical Mellin energy from the actual Gram limits

Source: user-provided countable critical-line mixture argument, 2026-09-21,
Section 5. Tannery's theorem is applied to the complete double series of
mixed terms, with summable majorant `4 * ‖a_j s_j‖ * ‖a_k s_k‖`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem mul_star_eq_complex_norm_sq (z : ℂ) :
    z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' z

theorem criticalMixture_coordinate_norm_summable (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) (n : ℕ) :
    Summable (fun j => ‖a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _
    ((coefficient_norm_summable a γ ha).mul_right (criticalModeBound n))
  intro j
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (criticalMode_norm_le (γ j) n) (norm_nonneg _)

private theorem amplitude_pair_norm_summable (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) :
    Summable (fun p : ℕ × ℕ =>
      ‖criticalAmplitude a γ p.1‖ * ‖criticalAmplitude a γ p.2‖) := by
  apply summable_mul_of_summable_norm
    (f := fun j : ℕ => ‖criticalAmplitude a γ j‖)
    (g := fun j : ℕ => ‖criticalAmplitude a γ j‖)
  · simpa only [norm_norm] using ha
  · simpa only [norm_norm] using ha

/-- The entire mixed coefficient series has the diagonal energy limit.
No exchange of a conditionally convergent double series is used. -/
theorem criticalCross_coefficient_series_tendsto (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (hγ : Function.Injective γ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) :
    Tendsto (fun N => ∑' p : ℕ × ℕ,
      a p.1 * star (a p.2) * criticalCross (γ p.1) (γ p.2) N)
      atTop (𝓝 (coefficientEnergy a γ : ℂ)) := by
  classical
  let F : ℕ → (ℕ × ℕ) → ℂ := fun N p =>
    a p.1 * star (a p.2) * criticalCross (γ p.1) (γ p.2) N
  let G : (ℕ × ℕ) → ℂ := fun p =>
    if p.1 = p.2 then ((‖criticalAmplitude a γ p.1‖ ^ 2 : ℝ) : ℂ) else 0
  let r : (ℕ × ℕ) → ℝ := fun p =>
    ‖criticalAmplitude a γ p.1‖ * ‖criticalAmplitude a γ p.2‖
  have hr : Summable r := amplitude_pair_norm_summable a γ ha
  have hdom : ∀ N p, ‖F N p‖ ≤ 4 * r p := by
    intro N p
    dsimp only [F, r]
    rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ ‖a p.1‖ * ‖a p.2‖ *
          (4 * ‖MellinFrequency.criticalPoint (γ p.1)‖ *
            ‖MellinFrequency.criticalPoint (γ p.2)‖) :=
        mul_le_mul_of_nonneg_left (criticalCross_norm_le _ _ N) (by positivity)
      _ = _ := by simp only [criticalAmplitude, norm_mul]; ring
  have hpoint (p : ℕ × ℕ) : Tendsto (fun N => F N p) atTop (𝓝 (G p)) := by
    rcases p with ⟨j, k⟩
    have ht := (tendsto_const_nhds (x := a j * star (a k))).mul
      (criticalCross_tendsto (γ j) (γ k))
    by_cases hjk : j = k
    · subst k
      have he : a j * star (a j) *
          (MellinFrequency.criticalPoint (γ j) * star (MellinFrequency.criticalPoint (γ j))) =
            ((‖criticalAmplitude a γ j‖ ^ 2 : ℝ) : ℂ) := by
        calc
          _ = criticalAmplitude a γ j * star (criticalAmplitude a γ j) := by
            simp only [criticalAmplitude, star_mul]
            ring
          _ = _ := mul_star_eq_complex_norm_sq _
      simpa only [F, G, if_pos rfl, ite_true, he] using ht
    · have hneq : γ j ≠ γ k := fun h => hjk (hγ h)
      simpa only [F, G, if_neg hjk, if_neg hneq, mul_zero] using ht
  have hGbound (p : ℕ × ℕ) : ‖G p‖ ≤ r p := by
    by_cases hp : p.1 = p.2
    · dsimp only [G]
      rw [if_pos hp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg ‖criticalAmplitude a γ p.1‖)]
      dsimp only [r]
      rw [hp, pow_two]
    · simp only [G, if_neg hp, norm_zero]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hGs : Summable G := Summable.of_norm
    (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hGbound hr)
  have hGsum : (∑' p, G p) = (coefficientEnergy a γ : ℂ) := by
    calc
      _ = ∑' j, ((‖criticalAmplitude a γ j‖ ^ 2 : ℝ) : ℂ) := by
        rw [hGs.tsum_prod]
        apply tsum_congr
        intro j
        simp [G]
      _ = _ := (Complex.ofReal_tsum _).symm
  have ht := tendsto_tsum_of_dominated_convergence (hr.mul_left 4) hpoint
    (Filter.Eventually.of_forall hdom)
  simpa only [F, hGsum] using ht

private theorem criticalMixture_norm_sq_expansion (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) (n : ℕ) :
    ((‖criticalMixture a γ n‖ ^ 2 : ℝ) : ℂ) =
      ∑' p : ℕ × ℕ,
        (a p.1 * mellinMode (MellinFrequency.criticalPoint (γ p.1)) n) *
          star (a p.2 * mellinMode (MellinFrequency.criticalPoint (γ p.2)) n) := by
  have hn := criticalMixture_coordinate_norm_summable a γ ha n
  have hnstar : Summable (fun j =>
      ‖star (a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n)‖) := by
    simpa only [norm_star] using hn
  rw [← mul_star_eq_complex_norm_sq]
  simp only [criticalMixture, tsum_star]
  exact tsum_mul_tsum_of_summable_norm hn hnstar

/-- Exact infinite mixed-term expansion at each fixed finite spatial window. -/
theorem criticalMixture_logEnergy_eq_cross_series (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) (N : ℕ) :
    (logEnergy (criticalMixture a γ) N : ℂ) =
      ∑' p : ℕ × ℕ,
        a p.1 * star (a p.2) * criticalCross (γ p.1) (γ p.2) N := by
  classical
  let V : ℕ → ℕ → ℂ := fun j n =>
    a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n
  let R : ℕ → (ℕ × ℕ) → ℂ := fun n p =>
    (paretoWeight n : ℂ) * (V p.1 n * star (V p.2 n))
  have hrow (n : ℕ) : Summable (R n) := by
    have hn : Summable (fun j => ‖V j n‖) :=
      criticalMixture_coordinate_norm_summable a γ ha n
    have hnstar : Summable (fun j => ‖star (V j n)‖) := by simpa only [norm_star] using hn
    exact (summable_mul_of_summable_norm hn hnstar).mul_left (paretoWeight n : ℂ)
  have hcomm : (∑' p, ∑ n ∈ Finset.range N, R n p) =
      ∑ n ∈ Finset.range N, ∑' p, R n p :=
    Summable.tsum_finsetSum (fun n _ => hrow n)
  calc
    _ = (∑ n ∈ Finset.range N, (paretoWeight n : ℂ) *
        ((‖criticalMixture a γ n‖ ^ 2 : ℝ) : ℂ)) /
          (Real.log ((N : ℝ) + 1) : ℂ) := by
      simp only [logEnergy, partialEnergy, Complex.ofReal_div, Complex.ofReal_sum,
        Complex.ofReal_mul]
    _ = (∑ n ∈ Finset.range N, ∑' p, R n p) /
        (Real.log ((N : ℝ) + 1) : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [criticalMixture_norm_sq_expansion a γ ha n, ← tsum_mul_left]
    _ = (∑' p, ∑ n ∈ Finset.range N, R n p) /
        (Real.log ((N : ℝ) + 1) : ℂ) := by rw [hcomm]
    _ = ∑' p, (∑ n ∈ Finset.range N, R n p) /
        (Real.log ((N : ℝ) + 1) : ℂ) := tsum_div_const.symm
    _ = _ := by
      apply tsum_congr
      intro p
      unfold criticalCross
      rw [← mul_div_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [R, V]
      rw [star_mul]
      ring

/-- The actual countable logarithmic-energy theorem. Its sole inputs are
distinct ordinates and the stipulated absolute coefficient-moment control. -/
theorem criticalPurePointEnergyProvider_proved : CriticalPurePointEnergyProvider := by
  intro a γ hγ ha
  have ht := criticalCross_coefficient_series_tendsto a γ hγ ha
  have he : (fun N => (logEnergy (criticalMixture a γ) N : ℂ)) =
      (fun N => ∑' p : ℕ × ℕ,
        a p.1 * star (a p.2) * criticalCross (γ p.1) (γ p.2) N) :=
    funext (criticalMixture_logEnergy_eq_cross_series a γ ha)
  rw [← he] at ht
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto (coefficientEnergy a γ : ℂ)).comp ht

/-- Positive coefficient energy excludes finite Pareto energy for the actual
countable critical mixture, with the analytic provider now discharged. -/
theorem criticalMixture_not_summable
    (a : ℕ → ℂ) (γ : ℕ → ℝ) (hγ : Function.Injective γ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖))
    (hpos : 0 < coefficientEnergy a γ) :
    ¬ Summable (fun n => paretoWeight n * ‖criticalMixture a γ n‖ ^ 2) :=
  criticalMixture_not_summable_of_provider criticalPurePointEnergyProvider_proved
    a γ hγ ha hpos

/-- Any nonzero coefficient rules out finite energy under the stated absolute
first-moment control. No zeta-zero or unproved analytic premise is required. -/
theorem nonzero_criticalMixture_not_summable
    (a : ℕ → ℂ) (γ : ℕ → ℝ) (hγ : Function.Injective γ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖))
    (hne : ∃ j, a j ≠ 0) :
    ¬ Summable (fun n => paretoWeight n * ‖criticalMixture a γ n‖ ^ 2) :=
  nonzero_criticalMixture_not_summable_of_provider criticalPurePointEnergyProvider_proved
    a γ hγ ha hne

end RiemannResearch.RH.Pareto.SpectralObstruction

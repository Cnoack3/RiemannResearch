import RiemannResearch.RH.CompactFrequencyMellinRigidity
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Uniqueness for entire exponential-type functions sampled at logarithmic integers

Source: user-provided compact-frequency rigidity argument, 2026-09-21.
The proof uses Mathlib's Jensen zero-count estimate. Counting `n²` logarithmic
samples inside a ball of radius `2n + O(1)` gives a quadratic versus linear
contradiction, so no asymptotic counting or interchange of limits is required.
-/

noncomputable section
open Set Metric MeromorphicOn
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

private theorem logSample_injective :
    Function.Injective (fun k : ℕ => (Real.log ((k : ℝ) + 2) : ℂ)) := by
  intro i j h
  have he : Real.log ((i : ℝ) + 2) = Real.log ((j : ℝ) + 2) := by
    have hc := congrArg Complex.re h
    simpa only [Complex.ofReal_re] using hc
  have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hc := Real.log_injOn_pos hi hj he
  have : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast this

private theorem logSample_norm_le (n k : ℕ) (hk : k < n ^ 2) :
    ‖(Real.log ((k : ℝ) + 2) : ℂ)‖ ≤ 2 * (n : ℝ) := by
  have hk' : (k : ℝ) + 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    have hkn : (k : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hk
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1 : 1 ≤ n := by nlinarith [Nat.zero_le k]
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hlog : Real.log ((k : ℝ) + 2) ≤
      Real.log (((n : ℝ) + 1) ^ 2) :=
    Real.log_le_log (by positivity) hk'
  have hl : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)
  rw [Real.log_pow] at hlog
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by have hkn0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith : (1 : ℝ) ≤ (k : ℝ) + 2))]
  norm_num at hlog
  linarith

private theorem divisor_pos_at_zero
    (f : ℂ → ℂ) (U : Set ℂ) (hf : AnalyticOnNhd ℂ f U)
    (z : ℂ) (hz : z ∈ U) (hzero : f z = 0)
    (hfinite : analyticOrderAt f z ≠ ⊤) :
    1 ≤ divisor f U z := by
  let m : ℕ := (analyticOrderAt f z).toNat
  have hm : (m : ℕ∞) = analyticOrderAt f z := ENat.natCast_toNat hfinite
  have hm0 : m ≠ 0 := by
    intro h
    have ho : analyticOrderAt f z = 0 := by simpa [h] using hm.symm
    exact ((hf z hz).analyticOrderAt_eq_zero.mp ho) hzero
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz, ← hm]
  change (1 : ℤ) ≤ (m : ℤ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)

private theorem sample_count_le_divisor
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (c : ℂ) (hfinite : ∀ z, analyticOrderAt f z ≠ ⊤)
    (hsamples : ∀ d : ℕ, 2 ≤ d → f (Real.log (d : ℝ)) = 0) (n : ℕ) :
    (n ^ 2 : ℤ) ≤ ∑ᶠ z, divisor f (closedBall c (2 * (n : ℝ) + ‖c‖ + 1)) z := by
  classical
  let D := divisor f (closedBall c (2 * (n : ℝ) + ‖c‖ + 1))
  have hDfin := D.finiteSupport (isCompact_closedBall c _)
  let S : Finset ℂ := hDfin.toFinset
  let I : Finset ℂ := (Finset.range (n ^ 2)).image
    (fun k : ℕ => (Real.log ((k : ℝ) + 2) : ℂ))
  have hIc : I.card = n ^ 2 := by
    simp only [I, Finset.card_image_of_injective _ logSample_injective, Finset.card_range]
  have hDpos : ∀ z ∈ I, 1 ≤ D z := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hk' : k < n ^ 2 := Finset.mem_range.mp hk
    apply divisor_pos_at_zero f _ (hf.mono (subset_univ _)) _ _ _ (hfinite _)
    · rw [mem_closedBall, dist_eq_norm]
      calc
        _ ≤ ‖(Real.log ((k : ℝ) + 2) : ℂ)‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ 2 * (n : ℝ) + ‖c‖ + 1 := by linarith [logSample_norm_le n k hk']
    · convert hsamples (k + 2) (by omega) using 1
      norm_cast
  have hIS : I ⊆ S := by
    intro z hz
    have hp := hDpos z hz
    have hn : D z ≠ 0 := by omega
    simpa [S, Function.mem_support] using hn
  have hnonneg : ∀ z, 0 ≤ D z := (hf.mono (subset_univ _)).divisor_nonneg
  calc
    _ = ∑ z ∈ I, (1 : ℤ) := by simp [hIc]
    _ ≤ ∑ z ∈ I, D z := Finset.sum_le_sum hDpos
    _ ≤ ∑ z ∈ S, D z := Finset.sum_le_sum_of_subset_of_nonneg hIS
      (fun z _ _ => hnonneg z)
    _ = ∑ᶠ z, D z := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro z hz
      simpa [S] using hz

/-- Jensen's inequality rules out the oversampled zero set `log d` for a
nonzero entire function of exponential type. This closes the general sampling
provider used by compact-frequency Mellin rigidity. -/
theorem logIntegerSamplingUniqueness_proved : LogIntegerSamplingUniqueness := by
  intro f hf hsamples
  obtain ⟨hdiff, A, K, hA, hK, hbound⟩ := hf
  have han : AnalyticOnNhd ℂ f Set.univ := by
    intro z _
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Filter.Eventually.of_forall hdiff
  by_contra hnzero
  push Not at hnzero
  obtain ⟨c, hc⟩ := hnzero
  have hordc : analyticOrderAt f c = 0 :=
    (han c (mem_univ c)).analyticOrderAt_eq_zero.mpr hc
  have hfinite : ∀ z, analyticOrderAt f z ≠ ⊤ := by
    have h := (han.exists_analyticOrderAt_ne_top_iff_forall isConnected_univ).mp
      (show ∃ z : (Set.univ : Set ℂ), analyticOrderAt f z ≠ ⊤ from
        ⟨⟨c, mem_univ c⟩, by simp [hordc]⟩)
    exact fun z => h ⟨z, mem_univ z⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquadratic : ∀ n : ℕ,
      (n : ℝ) ^ 2 * Real.log 2 ≤
        4 * K * (n : ℝ) +
          (|Real.log A| + K * (3 * ‖c‖ + 2) - Real.log ‖f c‖) := by
    intro n
    let r : ℝ := 2 * (n : ℝ) + ‖c‖ + 1
    have hr : 0 < r := by dsimp [r]; positivity
    let E : ℝ := |Real.log A| + K * (2 * r + ‖c‖)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hball : AnalyticOnNhd ℂ f (closedBall c |2 * r|) := han.mono (subset_univ _)
    have hM : 1 ≤ Real.exp E := Real.one_le_exp_iff.mpr hE
    have hb : ∀ z ∈ sphere c |2 * r|, ‖f z‖ ≤ Real.exp E := by
      intro z hz
      have hz' : ‖z‖ ≤ 2 * r + ‖c‖ := by
        have he : ‖z - c‖ = 2 * r := by
          simpa [mem_sphere, dist_eq_norm, abs_of_pos (by positivity : 0 < 2 * r)] using hz
        calc
          _ = ‖(z - c) + c‖ := by congr 1; ring
          _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
          _ = _ := by rw [he]
      calc
        ‖f z‖ ≤ A * Real.exp (K * ‖z‖) := hbound z
        _ = Real.exp (Real.log A + K * ‖z‖) := by rw [Real.exp_add, Real.exp_log hA]
        _ ≤ Real.exp E := Real.exp_le_exp.mpr
          (add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left hz' hK))
    have hj := AnalyticOnNhd.sum_divisor_le (r := r) (R := 2 * r) (M := Real.exp E)
      (by simpa [abs_of_pos hr]) (by simp [abs_of_pos hr, abs_of_pos (by positivity : 0 < 2 * r)]; linarith)
      hM hball hc hb
    have hratio : 2 * r / r = 2 := by field_simp
    have hnorm : ‖f c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    rw [abs_of_pos hr, hratio, Real.log_div (Real.exp_ne_zero _) hnorm, Real.log_exp] at hj
    have hlow := sample_count_le_divisor f han c hfinite hsamples n
    have hlow' : (n : ℝ) ^ 2 ≤
        ((∑ᶠ z, divisor f (closedBall c r) z : ℤ) : ℝ) := by
      exact_mod_cast hlow
    have h := (le_div_iff₀ hlog2).mp (le_trans hlow' hj)
    dsimp [E, r] at h
    nlinarith
  let C : ℝ := |Real.log A| + K * (3 * ‖c‖ + 2) - Real.log ‖f c‖
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((4 * K + |C| + 1) / Real.log 2))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hng : (4 * K + |C| + 1) / Real.log 2 < n :=
    lt_of_le_of_lt (le_max_right _ _) hn
  have hp := (div_lt_iff₀ hlog2).mp hng
  have hp' := mul_lt_mul_of_pos_right hp (by linarith : (0 : ℝ) < n)
  have hb := hquadratic n
  change (n : ℝ) ^ 2 * Real.log 2 ≤ 4 * K * (n : ℝ) + C at hb
  nlinarith [abs_nonneg C, le_abs_self C, mul_nonneg (abs_nonneg C) (by linarith : 0 ≤ (n : ℝ) - 1)]

/-- Assembly after discharging the general sampling input. The actual
Mellin/Fubini, entire-defect, and Fourier-uniqueness input is supplied by
`compactMixtureAnalyticProvider_proved` in `CompactFrequencyRigidity`. -/
theorem compactFrequencyRigidity_of_analyticProvider
    (h : CompactMixtureAnalyticProvider) : CompactFrequencyRigidityTarget :=
  compactFrequencyRigidity_of_providers h logIntegerSamplingUniqueness_proved

end RiemannResearch.RH.Pareto.SpectralObstruction

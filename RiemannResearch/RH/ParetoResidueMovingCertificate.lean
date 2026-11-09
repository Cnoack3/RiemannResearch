/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueCriticalNormalLimit
import RiemannResearch.RH.ParetoResidueMicroscopicGram
import RiemannResearch.Analysis.FiniteHilbertGramRowBounds

/-!
# Real grouped Gram and moving zero certificates

The positive and negative ordinate differences both enter the real Gram.
Normalizing each row by its critical-point norm makes its target diagonal
one half. Absolute row sums give an energy sandwich for varying families.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.FiniteHilbertGram
open MellinFrequency (criticalPoint criticalPoint_ne_one)
open SpectralObstruction (logPhaseKernel)

private theorem abs_crossPart_le (b c : Bool) (x y : ℂ) :
    |crossPart b c (x, y)| ≤ (‖x‖ + ‖y‖) / 2 := by
  have hr := add_le_add (Complex.abs_re_le_norm x) (Complex.abs_re_le_norm y)
  have hi := add_le_add (Complex.abs_im_le_norm x) (Complex.abs_im_le_norm y)
  have hr₁ := (abs_add_le x.re y.re).trans hr
  have hr₂ := (abs_sub x.re y.re).trans hr
  have hi₁ := (abs_add_le x.im y.im).trans hi
  have hi₂ := (abs_sub y.im x.im).trans (by simpa only [add_comm] using hi)
  cases b <;> cases c
  · change |(1 / 2 : ℝ) * (x.re + y.re)| ≤ _
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith only [hr₁]
  · change |(1 / 2 : ℝ) * (y.im - x.im)| ≤ _
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith only [hi₂]
  · change |(1 / 2 : ℝ) * (x.im + y.im)| ≤ _
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith only [hi₁]
  · change |(1 / 2 : ℝ) * (x.re - y.re)| ≤ _
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith only [hr₂]

private theorem norm_criticalPoint_neg (t : ℝ) : ‖criticalPoint (-t)‖ = ‖criticalPoint t‖ := by
  have h : criticalPoint (-t) = star (criticalPoint t) := by
    apply Complex.ext <;> simp [MellinFrequency.criticalPoint, Complex.mul_re, Complex.mul_im]
  rw [h, norm_star]

private theorem criticalLog_pos {N : ℕ} (hN : 0 < N) : 0 < Real.log ((N : ℝ) + 1) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  exact Real.log_pos (by linarith)

variable {ι : Type*}

def relativeCriticalGram (γ : ι → ℝ) (N : ℕ) (i j : ι × Bool) : ℝ :=
  normalizedCriticalGram γ N i j / (‖criticalPoint (γ i.1)‖ * ‖criticalPoint (γ j.1)‖)

private theorem classCross_sub_microscopic_le (t u : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖classCross t u N - criticalPoint t * star (criticalPoint u) *
      logPhaseKernel ((t - u) * Real.log ((N : ℝ) + 1))‖ ≤
    (‖criticalPoint t‖ * ‖criticalPoint u‖) *
      (microscopicCrossBudget t u / Real.log ((N : ℝ) + 1)) := by
  let a := criticalPoint t * star (criticalPoint u)
  let K := logPhaseKernel ((t - u) * Real.log ((N : ℝ) + 1))
  have ha : a ≠ 0 := mul_ne_zero (MellinFrequency.criticalPoint_ne_zero t)
    (by simp [MellinFrequency.criticalPoint_ne_zero])
  change ‖classCross t u N - a * K‖ ≤ _
  rw [show classCross t u N - a * K = a * (phaseStrippedCross t u N - K) by
    change _ = a * (classCross t u N / a - K)
    field_simp [ha]]
  rw [norm_mul, show ‖a‖ = ‖criticalPoint t‖ * ‖criticalPoint u‖ by simp [a]]
  exact mul_le_mul_of_nonneg_left (phaseStrippedCross_sub_logPhaseKernel_le t u N hN)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The two complex coefficients that contribute to a real Gram entry. -/
def criticalKernelPair (t u : ℝ) (N : ℕ) : ℂ × ℂ :=
  (criticalPoint t * star (criticalPoint u) *
      logPhaseKernel ((t - u) * Real.log ((N : ℝ) + 1)),
   criticalPoint t * star (criticalPoint (-u)) *
      logPhaseKernel ((t - (-u)) * Real.log ((N : ℝ) + 1)))

theorem relativeCriticalGram_sub_kernel_le (γ : ι → ℝ) (N : ℕ) (hN : 0 < N)
    (i j : ι × Bool) :
    |relativeCriticalGram γ N i j -
      crossPart i.2 j.2 (criticalKernelPair (γ i.1) (γ j.1) N) /
        (‖criticalPoint (γ i.1)‖ * ‖criticalPoint (γ j.1)‖)| ≤
      (microscopicCrossBudget (γ i.1) (γ j.1) + microscopicCrossBudget (γ i.1) (-γ j.1)) /
        (2 * Real.log ((N : ℝ) + 1)) := by
  let t := γ i.1
  let u := γ j.1
  let w := ‖criticalPoint t‖ * ‖criticalPoint u‖
  have hw : 0 < w := mul_pos
    (norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero t))
    (norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero u))
  have h₁ := classCross_sub_microscopic_le t u N hN
  have h₂ := classCross_sub_microscopic_le t (-u) N hN
  rw [norm_criticalPoint_neg] at h₂
  rw [relativeCriticalGram, normalizedCriticalGram_entry, ← sub_div, ← map_sub,
    abs_div, abs_of_pos hw]
  refine (div_le_div_of_nonneg_right
    (abs_crossPart_le i.2 j.2 _ _) hw.le).trans ?_
  change (‖classCross t u N - (criticalKernelPair t u N).1‖ +
    ‖classCross t (-u) N - (criticalKernelPair t u N).2‖) / 2 / w ≤ _
  refine (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (add_le_add h₁ h₂) (by norm_num : (0 : ℝ) ≤ 2))
    hw.le).trans_eq ?_
  have hlog := criticalLog_pos hN
  change (w * (microscopicCrossBudget t u / _) +
    w * (microscopicCrossBudget t (-u) / _)) / 2 / w = _
  field_simp [hw.ne', hlog.ne']
  rfl

/-- The separated regime has the scalar comparison diagonal in relative coordinates. -/
theorem relativeCriticalGram_sub_diag_le [DecidableEq ι] (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i) (N : ℕ) (hN : 0 < N)
    (i j : ι × Bool) :
    |relativeCriticalGram γ N i j - (if i = j then 1 / 2 else 0)| ≤
      (criticalCrossBudget (γ i.1) (γ j.1) + criticalCrossBudget (γ i.1) (-γ j.1)) /
        (2 * Real.log ((N : ℝ) + 1)) := by
  let t := γ i.1
  let u := γ j.1
  let w := ‖criticalPoint t‖ * ‖criticalPoint u‖
  let D : ℂ := if t = u then criticalPoint t * star (criticalPoint u) else 0
  have hw : 0 < w := mul_pos
    (norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero t))
    (norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero u))
  have hlog := criticalLog_pos hN
  have hn : t ≠ -u := by
    dsimp only [t, u]
    linarith [hpos i.1, hpos j.1]
  have h₁ := classCross_error_le t u N hN
  change ‖classCross t u N - D‖ ≤ _ at h₁
  have h₂ := classCross_error_le t (-u) N hN
  rw [if_neg hn, norm_criticalPoint_neg] at h₂
  have hd : crossPart i.2 j.2 (D, 0) = (if i = j then 1 / 2 else 0) * w := by
    rcases i with ⟨i, b⟩
    rcases j with ⟨j, c⟩
    by_cases hij : i = j
    · subst j
      have hv : D = ((‖criticalPoint (γ i)‖ ^ 2 : ℝ) : ℂ) := by
        simp [D, t, u, Complex.sq_norm, Complex.mul_conj]
      rw [hv, crossPart_zero_right]
      by_cases hbc : b = c
      · simp [w, t, u, hbc, pow_two]
        ring
      · simp [w, t, u, hbc]
    · have hne : t ≠ u := fun h => hij (hγ h)
      have hne' : (i, b) ≠ (j, c) := fun h => hij (congrArg Prod.fst h)
      rw [if_neg hne']
      simp only [D, if_neg hne, zero_mul]
      exact map_zero _
  have hcomp : (if i = j then 1 / 2 else 0) = crossPart i.2 j.2 (D, 0) / w := by
    rw [hd, mul_div_cancel_right₀ _ hw.ne']
  rw [relativeCriticalGram, normalizedCriticalGram_entry, hcomp, ← sub_div, ← map_sub,
    abs_div, abs_of_pos hw]
  refine (div_le_div_of_nonneg_right (abs_crossPart_le i.2 j.2 _ _) hw.le).trans ?_
  change (‖classCross t u N - D‖ + ‖classCross t (-u) N - 0‖) / 2 / w ≤ _
  refine (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (add_le_add h₁ h₂) (by norm_num : (0 : ℝ) ≤ 2))
    hw.le).trans_eq ?_
  change (w * criticalCrossBudget t u / _ + w * criticalCrossBudget t (-u) / _) / 2 / w = _
  field_simp [hw.ne', hlog.ne']
  rfl

variable [Fintype ι]

/-- Relative source energy of the finite real normal equations. -/
def relativeCriticalSourceSq (γ : ι → ℝ) (N : ℕ) : ℝ :=
  ∑ i : ι × Bool, (source N (fun j => criticalPoint (γ j)) i /
    ‖criticalPoint (γ i.1)‖) ^ 2

theorem critical_certificate_energy_bounds [DecidableEq ι] (γ : ι → ℝ) (N : ℕ) (hN : 0 < N)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) (d : ℝ) (hd : 0 ≤ d)
    (hd' : d < 1 / 2)
    (hrow : ∀ i, (∑ j, |relativeCriticalGram γ N i j - (if i = j then 1 / 2 else 0)|) ≤ d) :
    relativeCriticalSourceSq γ N / (1 / 2 + d) ≤
      Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) ∧
    Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) ≤
      relativeCriticalSourceSq γ N / (1 / 2 - d) := by
  let z := fun i => criticalPoint (γ i)
  let l := Real.log ((N : ℝ) + 1)
  let r := Real.sqrt l
  let w := fun i : ι × Bool => ‖z i.1‖
  let v := fun i : ι × Bool => (r * w i)⁻¹ • rowVector N z i
  let y := r • certificateVector N z
  have hs : ∀ i, 0 < (z i).re := fun _ => by
    simp [z, MellinFrequency.criticalPoint, Complex.mul_re]
  have hs₁ : ∀ i, z i ≠ 1 := fun i => criticalPoint_ne_one (γ i)
  have hr : 0 < r := Real.sqrt_pos.mpr (criticalLog_pos hN)
  have hr₂ : r ^ 2 = l := Real.sq_sqrt (criticalLog_pos hN).le
  have hw (i : ι × Bool) : 0 < w i := norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero _)
  obtain ⟨a, ha⟩ := exists_zero_normal N z hs hs₁ hz
  have ha₀ := certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs₁ hz a ha
  change Fintype.linearCombination ℝ (rowVector N z) a = certificateVector N z at ha₀
  have hy : y ∈ synthesisSpan v := by
    let c (i : ι × Bool) := (r * w i) * (r * a i)
    have hc : Fintype.linearCombination ℝ v c = y := by
      dsimp only [y]
      rw [← ha₀, Fintype.linearCombination_apply, Fintype.linearCombination_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [v, c]
      rw [smul_smul, smul_smul]
      congr 1
      field_simp [hr.ne', (hw i).ne']
    rw [← hc]
    exact synthesis_mem _ _
  have hg (i j : ι × Bool) : gramMatrix v i j = relativeCriticalGram γ N i j := by
    change inner ℝ ((r * w i)⁻¹ • rowVector N z i) ((r * w j)⁻¹ • rowVector N z j) =
      l⁻¹ * inner ℝ (rowVector N z i) (rowVector N z j) / (w i * w j)
    rw [real_inner_smul_left, real_inner_smul_right, ← hr₂]
    field_simp [hr.ne', (hw i).ne', (hw j).ne']
  have hb (i : ι × Bool) : cross v y i = source N z i / w i := by
    rw [gramMatrix_mulVec] at ha
    have hi := congrFun ha i
    change inner ℝ (rowVector N z i) (Fintype.linearCombination ℝ (rowVector N z) a) =
      source N z i at hi
    rw [ha₀] at hi
    change inner ℝ ((r * w i)⁻¹ • rowVector N z i) (r • certificateVector N z) = _
    rw [real_inner_smul_left, real_inner_smul_right, hi]
    field_simp [hr.ne', (hw i).ne']
  have hyn : ‖y‖ ^ 2 = l * certificateEnergy N z := by
    dsimp only [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow, hr₂, certificateEnergy]
  have h := synthesis_energy_bounds_of_rowDefect v y hy (1 / 2) d hd hd' (by
    simpa only [hg] using hrow)
  simpa only [hb, hyn, relativeCriticalSourceSq] using h

/-- The row bound retains each ordinate gap separately. -/
def criticalRowBudget (γ : ι → ℝ) (N : ℕ) (i : ι) : ℝ :=
  (∑ j, (criticalCrossBudget (γ i) (γ j) + criticalCrossBudget (γ i) (-γ j))) /
    Real.log ((N : ℝ) + 1)

theorem relativeCriticalGram_row_defect_le [DecidableEq ι] (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i) (N : ℕ) (hN : 0 < N) (i : ι × Bool) :
    (∑ j, |relativeCriticalGram γ N i j - (if i = j then 1 / 2 else 0)|) ≤
      criticalRowBudget γ N i.1 := by
  refine (Finset.sum_le_sum fun j _ =>
    relativeCriticalGram_sub_diag_le γ hγ hpos N hN i j).trans_eq ?_
  rw [Fintype.sum_prod_type, criticalRowBudget, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool]
  field_simp [(criticalLog_pos hN).ne']
  ring

/-- The normalized source differs from its limiting source by a uniform
multiples-class estimate, even when the ordinates move. -/
def criticalSourceError (N : ℕ) : ℝ :=
  (1 + criticalTailMass) * criticalScale ((N + 1 : ℕ) : ℝ)

theorem relativeCriticalSourceSq_eq (γ : ι → ℝ) (N : ℕ) :
    relativeCriticalSourceSq γ N =
      ∑ i, ‖1 - classMellin N (criticalPoint (γ i)) (Fin.last N)‖ ^ 2 /
        ‖criticalPoint (γ i)‖ ^ 2 := by
  rw [relativeCriticalSourceSq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_bool]
  let x : ℂ := 1 - classMellin N (criticalPoint (γ i)) (Fin.last N)
  let w : ℝ := ‖criticalPoint (γ i)‖
  change (x.im / w) ^ 2 + (x.re / w) ^ 2 = ‖x‖ ^ 2 / w ^ 2
  rw [div_pow, div_pow, ← add_div, Complex.sq_norm x, Complex.normSq_apply]
  congr 1
  ring

theorem relativeCriticalSourceSq_error (γ : ι → ℝ) (N : ℕ) :
    |relativeCriticalSourceSq γ N - ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2| ≤
      (Fintype.card ι : ℝ) * (criticalSourceError N * (4 + criticalSourceError N)) := by
  rw [relativeCriticalSourceSq_eq, ← Finset.sum_sub_distrib]
  let e := criticalSourceError N
  have he : 0 ≤ e := by
    have ht : 0 ≤ criticalTailMass := tsum_nonneg (fun _ => by unfold criticalScale; positivity)
    dsimp only [e, criticalSourceError]
    unfold criticalScale
    positivity
  have hpoint (i : ι) :
      |‖1 - classMellin N (criticalPoint (γ i)) (Fin.last N)‖ ^ 2 /
        ‖criticalPoint (γ i)‖ ^ 2 - 1 / ‖criticalPoint (γ i)‖ ^ 2| ≤ e * (4 + e) := by
    let w := ‖criticalPoint (γ i)‖
    let M := classMellin N (criticalPoint (γ i)) (Fin.last N)
    have hw : 0 < w := norm_pos_iff.mpr (MellinFrequency.criticalPoint_ne_zero _)
    have hw₂ : 1 / w ≤ 2 := by
      have h := Complex.abs_re_le_norm (criticalPoint (γ i))
      rw [MellinFrequency.criticalPoint_re, abs_of_nonneg (by norm_num)] at h
      exact (div_le_iff₀ hw).mpr (by change (1 : ℝ) ≤ 2 * ‖criticalPoint (γ i)‖; linarith)
    let x := ‖1 - M‖ / w
    let y := 1 / w
    have hx : 0 ≤ x := div_nonneg (norm_nonneg _) hw.le
    have hy : 0 ≤ y := div_nonneg (by norm_num) hw.le
    have hxy : |x - y| ≤ e := by
      dsimp only [x, y]
      rw [← sub_div, abs_div, abs_of_pos hw]
      apply (div_le_iff₀ hw).mpr
      have hh := abs_norm_sub_norm_le (1 - M) 1
      rw [norm_one, show 1 - M - 1 = -M by ring, norm_neg] at hh
      exact hh.trans ((critical_class_multiples_bound (γ i) N).trans_eq (by
        dsimp only [w, e, criticalSourceError]
        ring))
    have hsum : x + y ≤ 4 + e := by
      change y ≤ 2 at hw₂
      linarith only [hw₂, le_abs_self (x - y), hxy]
    change |‖1 - M‖ ^ 2 / w ^ 2 - 1 / w ^ 2| ≤ _
    have hyform : y ^ 2 = 1 / w ^ 2 := by simp [y]
    rw [← hyform, ← div_pow]
    change |x ^ 2 - y ^ 2| ≤ _
    rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul,
      abs_of_nonneg (add_nonneg hx hy)]
    exact mul_le_mul hxy hsum (add_nonneg hx hy) he
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i)

theorem critical_certificate_energy_sub_source_le [DecidableEq ι] (γ : ι → ℝ)
    (N : ℕ) (hN : 0 < N) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (d : ℝ) (hd : 0 ≤ d) (hd' : d ≤ 1 / 4)
    (hrow : ∀ i, (∑ j, |relativeCriticalGram γ N i j - (if i = j then 1 / 2 else 0)|) ≤ d) :
    |Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) -
      2 * relativeCriticalSourceSq γ N| ≤ 8 * d * relativeCriticalSourceSq γ N := by
  let S := relativeCriticalSourceSq γ N
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have ⟨h₁, h₂⟩ := critical_certificate_energy_bounds γ N hN hz d hd (by linarith) hrow
  have h₃ : (2 - 8 * d) * S ≤ S / (1 / 2 + d) :=
    (le_div_iff₀ (by linarith)).mpr (by
      nlinarith only [mul_nonneg hd hS, mul_nonneg (sq_nonneg d) hS])
  have h₄ : S / (1 / 2 - d) ≤ (2 + 8 * d) * S :=
    (div_le_iff₀ (by linarith)).mpr (by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hd') (mul_nonneg hd hS)])
  change (2 - 8 * d) * S ≤ _ at h₃
  change |Real.log ((N : ℝ) + 1) * certificateEnergy N (fun i => criticalPoint (γ i)) -
      2 * S| ≤ 8 * d * S
  exact abs_le.mpr ⟨by linarith only [h₃.trans h₁], by linarith only [h₂.trans h₄]⟩

/-- A moving family may use the actual row bounds and the actual source error.
Only the tested points are required to be zeros. -/
theorem moving_critical_certificate_tendsto (κ : ℕ → Type*) [∀ j, Fintype (κ j)]
    (γ : ∀ j, κ j → ℝ) (N : ℕ → ℕ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hinj : ∀ j, Function.Injective (γ j)) (hpos : ∀ j i, 0 < γ j i)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j) (hd₀ : Tendsto d atTop (𝓝 0))
    (hrow : ∀ᶠ j in atTop, ∀ i, criticalRowBudget (γ j) (N j) i ≤ d j)
    (hsource : Tendsto (fun j => (Fintype.card (κ j) : ℝ) *
      (criticalSourceError (N j) * (4 + criticalSourceError (N j)))) atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, (∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2) ≤ B) :
    Tendsto (fun j => Real.log ((N j : ℝ) + 1) *
      certificateEnergy (N j) (fun i => criticalPoint (γ j i)) -
      2 * ∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2) atTop (𝓝 0) := by
  classical
  let e j := (Fintype.card (κ j) : ℝ) *
    (criticalSourceError (N j) * (4 + criticalSourceError (N j)))
  have hd' : ∀ᶠ j in atTop, d j < 1 / 4 := hd₀.eventually (gt_mem_nhds (by norm_num))
  have he' : ∀ᶠ j in atTop, e j < 1 := hsource.eventually (gt_mem_nhds (by norm_num))
  have hbnd : ∀ᶠ j in atTop,
      ‖Real.log ((N j : ℝ) + 1) * certificateEnergy (N j) (fun i => criticalPoint (γ j i)) -
        2 * ∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2‖ ≤ 8 * d j * (B + 1) + 2 * e j := by
    filter_upwards [hN, hrow, hd', he'] with j hj hjr hjd hje
    have hq := critical_certificate_energy_sub_source_le (γ j) (N j) hj (hz j) (d j)
      (hd j) hjd.le (fun i =>
        (relativeCriticalGram_row_defect_le (γ j) (hinj j) (hpos j) (N j) hj i).trans (hjr i.1))
    have he := relativeCriticalSourceSq_error (γ j) (N j)
    have hS : relativeCriticalSourceSq (γ j) (N j) ≤ B + 1 :=
      by linarith only [(abs_le.mp he).2, hje, hB j]
    rw [Real.norm_eq_abs]
    refine (abs_sub_le _ (2 * relativeCriticalSourceSq (γ j) (N j)) _).trans ?_
    have h₂ : |2 * relativeCriticalSourceSq (γ j) (N j) -
        2 * ∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2| ≤ 2 * e j := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left he (by norm_num)
    exact add_le_add (hq.trans (mul_le_mul_of_nonneg_left hS (by positivity [hd j]))) h₂
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbnd ?_
  simpa only [mul_zero, zero_mul, add_zero] using
    (((tendsto_const_nhds (x := (8 : ℝ))).mul hd₀).mul
      (tendsto_const_nhds (x := B + 1))).add ((tendsto_const_nhds (x := (2 : ℝ))).mul hsource)

end RiemannResearch.RH.Pareto.ResidueMellin

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeBandlimitedGamma
import RiemannResearch.Analysis.SechGammaMatrix
import RiemannResearch.Analysis.AffineWindowIntegral
import RiemannResearch.RH.WeilGammaSymmetry
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # The actual-zero matrix and the cubic spatial estimate

The all-zero Guinand--Weil matrix, with analytic multiplicities and both signs
of the ordinates, is identified exactly with the spatial gamma matrix after
its scalar diagonal is subtracted. Both poles vanish by the window's actual
zero moment, and prime resonances vanish on the homogeneous integer block.

The final coefficient-sensitive constant72 bound therefore applies to the
actual centered zero sum. No RH is assumed. This is a smooth-height analytic
zero-coordinate matrix, not a hard-cutoff raw pair-correlation limit.

Source: user-provided MontgomeryGammaAudit20261110.md, Sections1--5.
The underlying explicit formula is the repository's checked Guinand--Weil
theorem; the shifted spatial identification is proved here.
-/
open MeasureTheory Set Complex
open scoped BigOperators ComplexConjugate
noncomputable section
namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open RiemannResearch.RH.SignedWeilCorrelation

theorem real_window_contDiff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (fun x => (F x : ℂ)) :=
  (Complex.ofRealCLM.contDiff : ContDiff ℝ 2 Complex.ofRealCLM).comp hF

theorem real_window_support {F : ℝ → ℝ}
    (hF : Function.support F ⊆ Icc (-1 : ℝ) 1) :
    Function.support (fun x => (F x : ℂ)) ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  apply hF
  simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hx

theorem gammaContribution_pos_spatial {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    {T u : ℝ} (hT : 0 < T) (hu : 1 / T < u) :
    gammaContribution (fun x => (F x : ℂ)) T u =
      (-(1 / (2 * Real.pi)) *
        ∫ x in Icc (-1 : ℝ) 1, F x * sechGammaKernel (u+x/T) : ℝ) := by
  have hk := frequencyTest_contDiff (real_window_contDiff hFd) T u
  have hc := frequencyTest_compact (real_window_support hF) hT u
  have hr : ∀ t, (frequencyTest (fun x => (F x : ℂ)) T u t).im = 0 := by
    intro t
    simp only [frequencyTest, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_mul, add_zero]
  have hz : ∀ t : ℝ, t ≤ 0 → frequencyTest (fun x => (F x : ℂ)) T u t = 0 := by
    intro t ht
    have hTu : 1 < T*u := by
      have h := (div_lt_iff₀ hT).mp hu
      nlinarith
    have hFt : F (T*(t-u)) = 0 := by
      by_contra hn
      have hh := (hF (Function.mem_support.mpr hn)).1
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hT.le ht]
    simp [frequencyTest, hFt]
  change gammaFunctional (frequencyTest (fun x => (F x : ℂ)) T u) = _
  rw [gammaFunctional_of_positive_support hk hc hr hz]
  have he : (fun t => weilGammaKernel t *
      (frequencyTest (fun x => (F x : ℂ)) T u t).re) =
      (fun t => (T/(2*Real.pi)) * (F (T*(t-u)) * sechGammaKernel t)) := by
    funext t
    simp only [frequencyTest, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    unfold sechGammaKernel
    ring
  rw [he, integral_const_mul, integral_affine_window F sechGammaKernel hT u,
    integral_window_restrict F (fun x => sechGammaKernel (u+x/T)) hF]
  congr 1
  field_simp [hT.ne', Real.pi_ne_zero]

theorem frequencyTest_reflect {F : ℝ → ℂ} (hFe : ∀ x, F (-x) = F x)
    (T u v : ℝ) : frequencyTest F T (-u) v = frequencyTest F T u (-v) := by
  have he : T * (-v-u) = -(T*(v- -u)) := by ring
  simp only [frequencyTest, he, hFe, neg_div, Real.cosh_neg]

theorem gammaContribution_neg {F : ℝ → ℂ} (hFe : ∀ x, F (-x) = F x)
    (T u : ℝ) : gammaContribution F T (-u) = gammaContribution F T u := by
  change gammaFunctional (frequencyTest F T (-u)) = gammaFunctional (frequencyTest F T u)
  have he : frequencyTest F T (-u) = fun v => frequencyTest F T u (-v) :=
    funext (frequencyTest_reflect hFe T u)
  rw [he, gammaFunctional_reflect]

theorem gammaContribution_im_real {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    {T : ℝ} (hT : 0 < T) (u : ℝ) :
    (gammaContribution (fun x => (F x : ℂ)) T u).im = 0 := by
  apply gammaFunctional_im_eq_zero
    (frequencyTest_contDiff (real_window_contDiff hFd) T u)
    (frequencyTest_compact (real_window_support hF) hT u)
  intro t
  simp only [frequencyTest, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_mul, add_zero]
end RiemannResearch.Analysis.PrimeBandlimitedWeil

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open Zeta23 SechGammaBounds

theorem gammaContribution_abs_spatial {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) {T u : ℝ} (hT : 0 < T) (hu : 1 / T < |u|) :
    gammaContribution (fun x => (F x : ℂ)) T u =
      (-(1 / (2 * Real.pi)) * windowSample F T |u| : ℝ) := by
  have heven : ∀ x, (F (-x) : ℂ) = (F x : ℂ) := by intro x; rw [hFe]
  have hg : gammaContribution (fun x => (F x : ℂ)) T u =
      gammaContribution (fun x => (F x : ℂ)) T |u| := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · simpa only [abs_of_nonpos h] using (gammaContribution_neg heven T u).symm
  rw [hg, gammaContribution_pos_spatial hFd hF hT hu]
  have he : (∫ x in Icc (-1 : ℝ) 1, F x * sechGammaKernel (|u|+x/T)) =
      windowSample F T |u| := by
    unfold windowSample
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hp : 0 < |u|+x/T := by
      have hb := div_le_div_of_nonneg_right hx.1 hT.le
      have ha : (-1 : ℝ)/T = -(1/T) := by ring
      rw [ha] at hb
      linarith
    rw [sechGammaKernel_split hp]
    rfl
  rw [he]

theorem poleContribution_eq_zero_of_windowMoment {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (h0 : windowMoment F 0 = 0) :
    poleContribution (fun x => (F x : ℂ)) = 0 := by
  have hc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hF
  have hi : Integrable F := hFd.continuous.integrable_of_hasCompactSupport hc
  have hcast := Complex.ofRealCLM.integral_comp_comm hi
  change (∫ x : ℝ, (F x : ℂ)) = ((∫ x : ℝ, F x : ℝ) : ℂ) at hcast
  have hwhole : (∫ x : ℝ, F x) = 0 := by
    have hh := integral_window_restrict F (fun _ => 1) hF
    simp only [mul_one] at hh
    rw [hh]
    simpa only [windowMoment, pow_zero, one_mul] using h0
  simp only [poleContribution, hcast, hwhole, Complex.ofReal_zero, mul_zero]

def actualZeroEntry (F : ℝ → ℝ) (T : ℝ) (n m : ℕ) : ℂ :=
  ∑' ρ : (zetaZeros zetaSeam).carrier, ((zetaZeros zetaSeam).mult ρ : ℂ) *
    paperFT (frequencyTest (fun x => (F x : ℂ)) T (logRatio n m)) (gammaOf ρ)

def zeroNormalizer (T : ℝ) : ℝ := T * Real.log T / (2 * Real.pi)

def normalizedDiagonal (F : ℝ → ℝ) (T : ℝ) : ℂ :=
  actualZeroEntry F T 1 1 / (zeroNormalizer T : ℂ)

def centeredZeroEntry (F : ℝ → ℝ) (T : ℝ) (n m : ℕ) : ℂ :=
  actualZeroEntry F T n m / (zeroNormalizer T : ℂ) -
    if n = m then normalizedDiagonal F T else 0

theorem actualZeroEntry_self (F : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    actualZeroEntry F T n n = actualZeroEntry F T 1 1 := by
  simp only [actualZeroEntry, logRatio, sub_self]

theorem actualZeroEntry_eq_gamma {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (h0 : windowMoment F 0 = 0) {T : ℝ} {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hdeg : ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m)
    (hTn : (n : ℝ) + 1 < T) (hTm : (m : ℝ) + 1 < T) :
    actualZeroEntry F T n m =
      gammaContribution (fun x => (F x : ℂ)) T (logRatio n m) := by
  have h := actual_zero_sum_homogeneous_complete (real_window_contDiff hFd)
    (real_window_support hF) hn hm hdeg hTn hTm
  rw [poleContribution_eq_zero_of_windowMoment hFd hF h0, zero_add] at h
  exact h

theorem centeredZeroEntry_eq_spatial {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    {T : ℝ} {D n m : ℕ} (hT : 4 ≤ T) (hTD : 2 * (D : ℝ) ≤ T)
    (hn : 0 < n) (hm : 0 < m) (hnD : n ≤ D) (hmD : m ≤ D)
    (hdeg : ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m) :
    centeredZeroEntry F T n m = (SechGammaMatrix.entry F T n m : ℂ) := by
  by_cases hne : n = m
  · subst m
    simp [centeredZeroEntry, normalizedDiagonal, actualZeroEntry_self,
      SechGammaMatrix.entry]
  have hT0 : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hiso (k : ℕ) (hk : 0 < k) (hkD : k ≤ D) : (k : ℝ)+1 < T := by
    have hkDR : (k : ℝ) ≤ D := by exact_mod_cast hkD
    by_cases hk1 : k = 1
    · subst k; norm_num; linarith
    · have hk2 : 2 ≤ k := by omega
      have hk2R : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      nlinarith
  have hgap := SechGammaMatrix.log_gap_mul_bound
    (show 0 < (n : ℝ) by exact_mod_cast hn) (show 0 < (m : ℝ) by exact_mod_cast hm)
    (show (n : ℝ) ≤ (D : ℝ) by exact_mod_cast hnD)
    (show (m : ℝ) ≤ (D : ℝ) by exact_mod_cast hmD)
  have hd := SechGammaMatrix.nat_gap_one_le hne
  have hu : 1/T < |logRatio n m| := by
    apply (div_lt_iff₀ hT0).mpr
    have hp := mul_le_mul_of_nonneg_right hTD (abs_nonneg (logRatio n m))
    unfold logRatio at *
    nlinarith
  rw [centeredZeroEntry, if_neg hne, sub_zero,
    actualZeroEntry_eq_gamma hFd hF h0 hn hm hdeg (hiso n hn hnD) (hiso m hm hmD),
    gammaContribution_abs_spatial hFd hF hFe hT0 hu]
  simp only [SechGammaMatrix.entry, if_neg hne]
  unfold zeroNormalizer logRatio
  push_cast
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hLc : (Real.log T : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hT1).ne'
  have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hTc, hLc, hpc]
end RiemannResearch.Analysis.PrimeBandlimitedWeil

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open SechGammaBounds
theorem actual_zero_centered_quadratic_bound {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    (s : Finset ℕ) (c : ℕ → ℂ) {T : ℝ} {D : ℕ}
    (hT : 4 ≤ T) (hTD : 2 * (D : ℝ) ≤ T)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ D)
    (hdeg : ∀ n ∈ s, ∀ m ∈ s,
      ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m) :
    ‖∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * centeredZeroEntry F T n m‖ ≤
      (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T) *
        ∑ n ∈ s, ‖c n‖^2 := by
  have he : (∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * centeredZeroEntry F T n m) =
      ∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * (SechGammaMatrix.entry F T n m : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    rw [centeredZeroEntry_eq_spatial hFd hF hFe h0 hT hTD
      (hs n hn).1 (hs m hm).1 (hs n hn).2 (hs m hm).2 (hdeg n hn m hm)]
  rw [he]
  exact SechGammaMatrix.quadratic_bound F hFd.continuous hFe h0 s c
    (by linarith) hTD hs

theorem normalizedDiagonal_eq_real_gamma {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (h0 : windowMoment F 0 = 0) {T : ℝ} (hT : 2 < T) :
    normalizedDiagonal F T =
      ((gammaContribution (fun x => (F x : ℂ)) T 0).re / zeroNormalizer T : ℝ) := by
  unfold normalizedDiagonal
  rw [actualZeroEntry_eq_gamma hFd hF h0 (by norm_num) (by norm_num) rfl
    (by norm_num; exact hT) (by norm_num; exact hT)]
  simp only [logRatio, sub_self]
  have hg := gammaContribution_im_real hFd hF (by linarith : 0 < T) 0
  have he : gammaContribution (fun x => (F x : ℂ)) T 0 =
      ((gammaContribution (fun x => (F x : ℂ)) T 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hg
  rw [he]
  push_cast
  rfl
end RiemannResearch.Analysis.PrimeBandlimitedWeil

namespace RiemannResearch.Analysis.PrimeBandlimitedWeil
open SechGammaBounds

private theorem scalar_diagonal_quadratic (s : Finset ℕ) (c : ℕ → ℂ) (a : ℂ) :
    (∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * (if n = m then a else 0)) =
      a * ((∑ n ∈ s, ‖c n‖^2 : ℝ) : ℂ) := by
  calc
    _ = ∑ n ∈ s, c n * conj (c n) * a := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_eq_single n]
      · simp
      · intro m hm hmn
        simp [Ne.symm hmn]
      · intro hnn
        exact (hnn hn).elim
    _ = _ := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      ring

theorem centered_quadratic_exact (F : ℝ → ℝ) (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) * centeredZeroEntry F T n m) =
      (∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) *
        (actualZeroEntry F T n m / (zeroNormalizer T : ℂ))) -
      normalizedDiagonal F T * ((∑ n ∈ s, ‖c n‖^2 : ℝ) : ℂ) := by
  simp only [centeredZeroEntry, mul_sub, Finset.sum_sub_distrib]
  rw [scalar_diagonal_quadratic]

theorem actual_zero_quadratic_error_le_of_diagonal_bound {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 F) (hF : Function.support F ⊆ Icc (-1 : ℝ) 1)
    (hFe : ∀ x, F (-x) = F x) (h0 : windowMoment F 0 = 0)
    (s : Finset ℕ) (c : ℕ → ℂ) {T : ℝ} {D : ℕ}
    (hT : 4 ≤ T) (hTD : 2 * (D : ℝ) ≤ T)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ D)
    (hdeg : ∀ n ∈ s, ∀ m ∈ s,
      ArithmeticFunction.cardFactors n = ArithmeticFunction.cardFactors m)
    (mu delta : ℝ) (hdiag : ‖normalizedDiagonal F T - (mu : ℂ)‖ ≤ delta) :
    ‖(∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) *
        (actualZeroEntry F T n m / (zeroNormalizer T : ℂ))) -
      (mu : ℂ) * ((∑ n ∈ s, ‖c n‖^2 : ℝ) : ℂ)‖ ≤
      (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T + delta) *
        ∑ n ∈ s, ‖c n‖^2 := by
  have hmain := actual_zero_centered_quadratic_bound hFd hF hFe h0 s c hT hTD hs hdeg
  rw [centered_quadratic_exact] at hmain
  let Q := ∑ n ∈ s, ∑ m ∈ s, c n * conj (c m) *
    (actualZeroEntry F T n m / (zeroNormalizer T : ℂ))
  let M : ℝ := ∑ n ∈ s, ‖c n‖^2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change ‖Q - (mu : ℂ) * (M : ℂ)‖ ≤
    (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T + delta) * M
  change ‖Q - normalizedDiagonal F T * (M : ℂ)‖ ≤
    (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T) * M at hmain
  calc
    _ = ‖(Q - normalizedDiagonal F T * (M : ℂ)) +
        (normalizedDiagonal F T - (mu : ℂ)) * (M : ℂ)‖ := by congr 1; ring
    _ ≤ ‖Q - normalizedDiagonal F T * (M : ℂ)‖ +
        ‖(normalizedDiagonal F T - (mu : ℂ)) * (M : ℂ)‖ := norm_add_le _ _
    _ ≤ (72 * absoluteSecondMoment F * ((D : ℝ)/T)^3 / Real.log T) * M + delta * M := by
      apply add_le_add hmain
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right hdiag hM
    _ = _ := by ring
end RiemannResearch.Analysis.PrimeBandlimitedWeil

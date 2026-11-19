/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryReflectedGramKernel
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import Mathlib.Tactic.FinCases

/-! # Reflected Gram identity for the horizontal form-factor defect

The central difference has three components with coefficients one half, one
half and minus one. Both differences remain inside each Gram entry before
the pair estimate and Schur's inequality are applied. -/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace RiemannResearch.Analysis.MontgomeryReflectedDefect
open MontgomeryCentralDifference MontgomeryComplexGram MontgomeryLocalMass
open MontgomeryHorizontalTransfer MontgomeryPoisson ZeroOrdinate ActualZeroOrdinate
open MontgomeryFormFactor

private def offset (a : ℝ) : Fin 3 → ℝ := ![a, -a, 0]
private def coeff : Fin 3 → ℝ := ![1 / 2, 1 / 2, -1]

private theorem central_sum (a : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    central a f x = ∑ k : Fin 3, (coeff k : ℂ) * f (x + offset a k) := by
  simp [central, coeff, offset, Fin.sum_univ_succ, sub_eq_add_neg]
  ring

private def componentExponent (x t : ℝ) : ℂ := (x:ℂ) + Complex.I * (t:ℂ)
private def componentAmplitude (b : ℂ) (h u x : ℝ) : ℂ :=
  b * ((h * Real.exp (u*x) : ℝ) : ℂ)

private theorem component_gram_entry (b b' : ℂ) (h h' u x y t t' : ℝ) :
    componentAmplitude b h u x * conj (componentAmplitude b' h' u y) *
      (4 / (4-(componentExponent x t + conj (componentExponent y t'))^2)) =
    (b * conj b') * ((h:ℂ) * ((h':ℂ) * phaseKernel u (t-t') ((x+y:ℝ):ℂ))) := by
  have hden : componentExponent x t + conj (componentExponent y t') =
      ((x+y:ℝ):ℂ) + Complex.I*((t-t':ℝ):ℂ) := by
    simp only [componentExponent, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hex : Complex.exp ((u:ℂ)*((x+y:ℝ):ℂ)) =
      (Real.exp (u*x) : ℂ) * (Real.exp (u*y) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_add, Real.exp_add, Complex.ofReal_mul]
  rw [hden, phaseKernel, hex]
  simp only [componentAmplitude, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

private theorem component_signal (b : ℂ) (h u s x t : ℝ) :
    componentAmplitude b h u x * Complex.exp ((s:ℂ) * componentExponent x t) =
      (b * phase s t) * ((h:ℂ) * (Real.exp ((u+s)*x):ℂ)) := by
  have hz : (s:ℂ) * componentExponent x t = ((s*x:ℝ):ℂ) + ((s*t:ℝ):ℂ)*Complex.I := by
    simp only [componentExponent, Complex.ofReal_mul]
    ring
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp]
  simp only [componentAmplitude, phase, add_mul, Real.exp_add, Complex.ofReal_mul]
  ring

private theorem component_cosh (u a : ℝ) :
    (∑ k : Fin 3, (coeff k:ℂ) * (Real.exp (u * offset a k):ℂ)) =
      (Real.cosh (u*a):ℂ) - 1 := by
  simp [coeff, offset, Fin.sum_univ_succ, Real.cosh_eq, mul_neg]
  ring

private theorem expanded_gram {ι : Type*} [Fintype ι]
    (a t : ι → ℝ) (b : ι → ℂ) (u : ℝ) :
    complexKernel (fun e : ι × Fin 3 => componentExponent (offset (a e.1) e.2) (t e.1))
      (fun e => componentAmplitude (b e.1) (coeff e.2) u (offset (a e.1) e.2)) =
      ∑ i, ∑ j, (b i * conj (b j)) * reflectedPairKernel u (a i) (a j) (t i-t j) := by
  classical
  simp only [complexKernel, Fintype.sum_prod_type, component_gram_entry]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [reflectedPairKernel, central_sum, zero_add, Finset.mul_sum, mul_assoc]

private theorem expanded_signal {ι : Type*} [Fintype ι]
    (a t : ι → ℝ) (b : ι → ℂ) (u s : ℝ) :
    complexSignal (fun e : ι × Fin 3 => componentExponent (offset (a e.1) e.2) (t e.1))
      (fun e => componentAmplitude (b e.1) (coeff e.2) u (offset (a e.1) e.2)) s =
      ∑ i, (b i * phase s (t i)) * ((Real.cosh ((u+s)*a i):ℂ) - 1) := by
  simp only [complexSignal, Fintype.sum_prod_type, component_signal]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, component_cosh]

/-- Exact Gram identity for arbitrary labels. The reflected rows retain the
phase and all nine signed component pairings. -/
theorem reflected_gram {ι : Type*} [Fintype ι] (a t : ι → ℝ) (b : ι → ℂ) (u : ℝ)
    (ha : ∀ i, |a i| ≤ 1 / 2) :
    (∫ s : ℝ, Real.exp (-2* |s|) *
      ‖∑ i, (b i * phase s (t i)) * ((Real.cosh ((u+s)*a i):ℂ) - 1)‖^2) =
      (∑ i, ∑ j, (b i * conj (b j)) * reflectedPairKernel u (a i) (a j) (t i-t j)).re := by
  let z := fun e : ι × Fin 3 => componentExponent (offset (a e.1) e.2) (t e.1)
  let c := fun e : ι × Fin 3 => componentAmplitude (b e.1) (coeff e.2) u (offset (a e.1) e.2)
  have hz (e : ι × Fin 3) : |(z e).re| < 1 := by
    obtain ⟨i,k⟩ := e
    have hi : |a i| < 1 := by linarith [ha i]
    fin_cases k <;> simp [z, componentExponent, offset, hi]
  have h := complex_gram_re z c hz
  simpa only [z, c, expanded_signal, expanded_gram] using h

/-- Exact complete pair sum for the actual positive-height defect integral. -/
theorem defectIntegral_reflected_gram (T u : ℝ) :
    defectIntegral T u =
      (∑ i : Copies T, ∑ j : Copies T,
        (phase u (copyOrdinate T i) * conj (phase u (copyOrdinate T j))) *
        reflectedPairKernel u (i.1.1.re-1 / 2) (j.1.1.re-1 / 2)
          (copyOrdinate T i-copyOrdinate T j)).re := by
  have h := reflected_gram (fun i : Copies T => i.1.1.re-1 / 2) (copyOrdinate T)
    (fun i => phase u (copyOrdinate T i)) u (fun i => (displacement_lt_half i.1.2).le)
  simpa only [defectIntegral, coshCorrection, sum_eq_copies, phase_add, copyOrdinate] using h

/-- Schur's inequality after the two central differences. The row bound is
for the complete Cauchy matrix, with repeated ordinates included. -/
theorem reflected_pair_sum_re_le {ι : Type*} [Fintype ι]
    (a t : ι → ℝ) (u D : ℝ) (ha : ∀ i, |a i| ≤ 1 / 2)
    (hrow : ∀ i, (∑ j, cauchyWeight (t i-t j)) ≤ D) :
    (∑ i, ∑ j, (phase u (t i) * conj (phase u (t j))) *
      reflectedPairKernel u (a i) (a j) (t i-t j)).re ≤
      (1536*Real.exp 1)*(1 + |u|) ^ 4 * D *
        ∑ i, (a i) ^ 4 * Real.exp (2* |u| * |a i|) := by
  let H := (1536*Real.exp 1)*(1 + |u|) ^ 4
  let v (i : ι) := (a i)^2 * Real.exp (|u| * |a i|)
  let K (i j : ι) := cauchyWeight (t i-t j)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hs (i j : ι) : K i j = K j i := by
    dsimp [K]
    rw [show t i-t j = -(t j-t i) by ring, cauchyWeight_neg]
  have hdiag (i : ι) : v i ^ 2 = (a i) ^ 4 * Real.exp (2* |u| * |a i|) := by
    rw [show 2* |u| * |a i| = |u| * |a i|+|u| * |a i| by ring, Real.exp_add]
    dsimp only [v]
    ring
  have he (i j : ι) : ‖(phase u (t i) * conj (phase u (t j))) *
      reflectedPairKernel u (a i) (a j) (t i-t j)‖ ≤ H*(K i j*v i*v j) := by
    rw [norm_mul, norm_mul, Complex.norm_conj, phase_norm, phase_norm, one_mul, one_mul]
    apply (reflectedPairKernel_norm_le u (a i) (a j) (t i-t j) (ha i) (ha j)).trans_eq
    dsimp only [H,K,v]
    rw [mul_add, Real.exp_add]
    ring
  have hschur := MarkedFourierTail.symmetric_kernel_quadratic_le_row_bound
    Finset.univ v K D (fun i _ j _ => cauchyWeight_nonneg _)
    (fun i _ j _ => hs i j) (fun i _ => hrow i)
  calc
    _ ≤ ‖∑ i, ∑ j, (phase u (t i) * conj (phase u (t j))) *
        reflectedPairKernel u (a i) (a j) (t i-t j)‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ‖∑ j, (phase u (t i) * conj (phase u (t j))) *
        reflectedPairKernel u (a i) (a j) (t i-t j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, H*(K i j*v i*v j) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ j, ‖(phase u (t i) * conj (phase u (t j))) *
            reflectedPairKernel u (a i) (a j) (t i-t j)‖ := norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum (fun j _ => he i j)
    _ = H*(∑ i, ∑ j, K i j*v i*v j) := by simp only [Finset.mul_sum]
    _ ≤ H*(D*∑ i, v i^2) := mul_le_mul_of_nonneg_left hschur hH
    _ = _ := by simp only [H, hdiag, mul_assoc]

/-- Unconditional fourth-order defect estimate in terms of actual horizontal
displacements. The constant is independent of height and frequency. -/
theorem exists_defectIntegral_le_reflected_quartic :
    ∃ A : ℝ, 0 < A ∧ ∀ T u : ℝ, 0 ≤ T →
      defectIntegral T u ≤ A * Real.log (T+3) * (1 + |u|) ^ 4 *
        ∑ i : Copies T, (i.1.1.re-1 / 2) ^ 4 * Real.exp (2* |u| * |i.1.1.re-1 / 2|) := by
  obtain ⟨C,hC,hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨(1536*Real.exp 1)*C, by positivity, ?_⟩
  intro T u hT
  rw [defectIntegral_reflected_gram]
  apply (reflected_pair_sum_re_le (fun i : Copies T => i.1.1.re-1 / 2) (copyOrdinate T)
    u (C*Real.log (T+3)) (fun i => (displacement_lt_half i.1.2).le)
    (fun i => hrow T hT _)).trans_eq
  ring

/-- The normalization removes the row logarithm and leaves the fourth
exponential moment divided by height. -/
theorem exists_horizontalDefect_le_reflected_quartic :
    ∃ A : ℝ, 0 < A ∧ ∀ T α : ℝ, 9 ≤ T →
      horizontalDefect T α ≤ A*(1 + |α*Real.log T|) ^ 4*
        ((∑ i : Copies T, (i.1.1.re-1 / 2) ^ 4 *
          Real.exp (2* |α*Real.log T| * |i.1.1.re-1 / 2|))/T) := by
  obtain ⟨A,hA,ha⟩ := exists_defectIntegral_le_reflected_quartic
  refine ⟨4*Real.pi*A, by positivity, ?_⟩
  intro T α hT
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log (T+3) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul ht.ne' ht.ne']; ring
  let u := α*Real.log T
  let E := ∑ i : Copies T, (i.1.1.re-1 / 2) ^ 4 * Real.exp (2* |u| * |i.1.1.re-1 / 2|)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun i _ => by positivity)
  unfold horizontalDefect
  apply (div_le_iff₀ (by positivity : 0 < T*Real.log T/(2*Real.pi))).mpr
  calc
    _ ≤ A*Real.log (T+3)*(1 + |u|) ^ 4*E := ha T u ht.le
    _ ≤ A*(2*Real.log T)*(1 + |u|) ^ 4*E := by gcongr
    _ = (4*Real.pi*A*(1 + |u|) ^ 4*(E/T))*(T*Real.log T/(2*Real.pi)) := by
      field_simp [ht.ne', Real.pi_ne_zero]
      ring

end RiemannResearch.Analysis.MontgomeryReflectedDefect

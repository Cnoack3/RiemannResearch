/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.EuclideanOperatorCoordinates
import RiemannResearch.Analysis.ZeroSamplingQuadratic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic.NormNum

/-!
# Centered hyperbolic analysis and finite frame estimates

Source: user-provided `Landau_Density_Providers_and_Stronger_Frames.tex`,
Lemma 6.1 (centered hyperbolic factorization). This module formalizes finite
operator algebra and the dimension-free centered-even-series estimate. Its
abstract frame transfer explicitly assumes the hyperbolic factorization and
its finite form bounds. It assumes no zeta density estimate or RH statement.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.CenteredHyperbolicFrames

section FiniteFactorization
variable {ι κ : Type*}

/-- The complete cosh kernel, with arbitrary repeated sample copies and all
frequency coordinates retained. No positivity premise is needed for identity. -/
def hyperbolicKernel (samples : Finset κ) (weight shift : κ → ℝ)
    (coordinate : ι → ℝ) (phase : κ → ι → ℂ) (i j : ι) : ℂ :=
  ∑ s ∈ samples, (weight s : ℂ) *
    (Real.cosh (shift s*(coordinate i-coordinate j)) : ℂ) *
      phase s i * star (phase s j)

def cosineRow (shift : κ → ℝ) (coordinate : ι → ℝ)
    (phase : κ → ι → ℂ) (s : κ) (i : ι) : ℂ :=
  (Real.cosh (shift s*coordinate i) : ℂ)*phase s i

def sineRow (shift : κ → ℝ) (coordinate : ι → ℝ)
    (phase : κ → ι → ℂ) (s : κ) (i : ι) : ℂ :=
  (Real.sinh (shift s*coordinate i) : ℂ)*phase s i

/-- Exact C* C - S* S entry factorization. The negative sinh contribution
is preserved, with both copies and weights unchanged. -/
theorem hyperbolicKernel_factorization
    (samples : Finset κ) (weight shift : κ → ℝ)
    (coordinate : ι → ℝ) (phase : κ → ι → ℂ) (i j : ι) :
    hyperbolicKernel samples weight shift coordinate phase i j =
      ZeroSamplingQuadratic.samplingGram samples weight
        (cosineRow shift coordinate phase) i j -
      ZeroSamplingQuadratic.samplingGram samples weight
        (sineRow shift coordinate phase) i j := by
  unfold hyperbolicKernel ZeroSamplingQuadratic.samplingGram
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show shift s*(coordinate i-coordinate j) =
    shift s*coordinate i-shift s*coordinate j by ring, Real.cosh_sub]
  simp only [cosineRow, sineRow, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  ring

/-- Exact finite quadratic hyperbolic factorization, before any estimates. -/
theorem hyperbolic_form_factorization
    (frequencies : Finset ι) (samples : Finset κ) (weight shift : κ → ℝ)
    (coordinate : ι → ℝ) (phase : κ → ι → ℂ) (f : ι → ℂ) :
    ZeroSamplingQuadratic.form frequencies
      (hyperbolicKernel samples weight shift coordinate phase) f =
    ∑ s ∈ samples, (weight s : ℂ)*
      (((‖∑ i ∈ frequencies, f i*cosineRow shift coordinate phase s i‖^2 : ℝ) : ℂ) -
       ((‖∑ i ∈ frequencies, f i*sineRow shift coordinate phase s i‖^2 : ℝ) : ℂ)) := by
  have hkernel : hyperbolicKernel samples weight shift coordinate phase =
      (fun i j => ZeroSamplingQuadratic.samplingGram samples weight
        (cosineRow shift coordinate phase) i j -
      ZeroSamplingQuadratic.samplingGram samples weight
        (sineRow shift coordinate phase) i j) := by
    funext i j
    exact hyperbolicKernel_factorization samples weight shift coordinate phase i j
  rw [hkernel, ZeroSamplingQuadratic.form_sub,
    ZeroSamplingQuadratic.form_samplingGram,
    ZeroSamplingQuadratic.form_samplingGram, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Complex.star_def, Complex.mul_conj, Complex.sq_norm]
  ring

/-- Real cosine-hyperbolic weights give a Hermitian finite kernel. -/
theorem hyperbolicKernel_star {ι κ : Type*} (samples : Finset κ)
    (weight shift : κ → ℝ) (coordinate : ι → ℝ)
    (phase : κ → ι → ℂ) (i j : ι) :
    star (hyperbolicKernel samples weight shift coordinate phase i j) =
      hyperbolicKernel samples weight shift coordinate phase j i := by
  simp only [hyperbolicKernel, star_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [show shift s*(coordinate j-coordinate i) =
    -(shift s*(coordinate i-coordinate j)) by ring, Real.cosh_neg]
  simp only [star_mul, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end FiniteFactorization

/-- The exact scalar row expansion identifies the operator centered-even
series with the concrete cosh entries. Both constants are retained. -/
theorem centered_cosh_tsum (a x b : ℝ) :
    (∑' j : ℕ, a^(2*(j+1))*(x^(2*(j+1))-b^(2*(j+1))/2) /
      (Nat.factorial (2*(j+1)) : ℝ)) =
      Real.cosh (a*x)-(1+Real.cosh (a*b))/2 := by
  have hx := HorizontalPhaseBootstrap.cosh_tail_summable (a*x)
  have hb := (HorizontalPhaseBootstrap.cosh_tail_summable (a*b)).div_const 2
  have heq (j : ℕ) :
      a^(2*(j+1))*(x^(2*(j+1))-b^(2*(j+1))/2) /
        (Nat.factorial (2*(j+1)) : ℝ) =
      (a*x)^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℝ) -
        ((a*b)^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℝ))/2 := by
    rw [mul_pow, mul_pow]
    ring
  simp_rw [heq]
  rw [hx.tsum_sub hb, tsum_div_const,
    HorizontalPhaseBootstrap.cosh_tail_tsum,
    HorizontalPhaseBootstrap.cosh_tail_tsum]
  ring

section Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonalCLM_pow_apply (r : ι → ℂ) (j : ℕ)
    (x : EuclideanSpace ℂ ι) (i : ι) :
    (((EuclideanSpace.diagonalCLM r)^j) x) i = r i ^ j * x i := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    change (((EuclideanSpace.diagonalCLM r)^j)
      (EuclideanSpace.diagonalCLM r x)) i = _
    rw [ih, EuclideanSpace.diagonalCLM_apply, pow_succ]
    ring

/-- Every even diagonal power has the sharp half-centering bound. This
applies to the actual centered logarithmic coordinates and retains them all. -/
theorem diagonal_even_power_center_norm_le (a : ι → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (ha : ∀ i, |a i| ≤ b) (j : ℕ) :
    ‖(EuclideanSpace.diagonalCLM (fun i => (a i : ℂ)))^(2*j) -
      (b^(2*j)/2) • (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤
      b^(2*j)/2 := by
  have hp (i : ι) : 0 ≤ a i^(2*j) ∧ a i^(2*j) ≤ b^(2*j) := by
    have hs : a i^2 ≤ b^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hb).2 (ha i)
    constructor
    · rw [pow_mul]; positivity
    · rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hs j
  have heq :
      (EuclideanSpace.diagonalCLM (fun i => (a i : ℂ)))^(2*j) -
        (b^(2*j)/2) • (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      EuclideanSpace.diagonalCLM (fun i => ((a i^(2*j)-b^(2*j)/2 : ℝ) : ℂ)) := by
    ext x i
    change (((EuclideanSpace.diagonalCLM (fun i => (a i : ℂ)))^(2*j)) x) i -
      (b^(2*j)/2 : ℝ) • x i =
      EuclideanSpace.diagonalCLM
        (fun i => ((a i^(2*j)-b^(2*j)/2 : ℝ) : ℂ)) x i
    rw [diagonalCLM_pow_apply, EuclideanSpace.diagonalCLM_apply]
    change (a i : ℂ)^(2*j) * x i -
      (b^(2*j)/2 : ℝ) • x i = _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    ring_nf
    rfl
  rw [heq]
  apply EuclideanSpace.norm_diagonalCLM_le _ _ (by positivity)
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hp i).1, (hp i).2]

end Diagonal

section Series
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem comp_norm_le (A : F →L[ℂ] F) (V : E →L[ℂ] F) :
    ‖A.comp V‖ ≤ ‖A‖ * ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖A (V x)‖ ≤ ‖A‖ * ‖V x‖ := A.le_opNorm _
    _ ≤ ‖A‖ * (‖V‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (V.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

private theorem comp_norm_le_right (V : E →L[ℂ] F) (D : E →L[ℂ] E) :
    ‖V.comp D‖ ≤ ‖V‖ * ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖V (D x)‖ ≤ ‖V‖ * ‖D x‖ := V.le_opNorm _
    _ ≤ ‖V‖ * (‖D‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

private theorem opNorm_pow_le (A : F →L[ℂ] F) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ δ) (j : ℕ) : ‖A^j‖ ≤ δ^j := by
  induction j with
  | zero =>
    simp only [pow_zero]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  | succ j ih =>
    rw [pow_succ]
    calc
      ‖A^j*A‖ = ‖(A^j).comp A‖ := rfl
      _ ≤ ‖A^j‖*‖A‖ := comp_norm_le _ _
      _ ≤ δ^j*δ := mul_le_mul ih hA (norm_nonneg _) (pow_nonneg hδ _)
      _ = δ^(j+1) := by rw [pow_succ]

/-- Exact centered Taylor summand. No entrywise absolute-value matrix
majorant is used, so the estimate below has no dimension factor. -/
def centeredEvenTerm (A : F →L[ℂ] F) (V : E →L[ℂ] F)
    (D : E →L[ℂ] E) (b : ℝ) (j : ℕ) : E →L[ℂ] F :=
  ((Nat.factorial (2*(j+1)) : ℝ)⁻¹) •
    ((A^(2*(j+1))).comp (V.comp
      (D^(2*(j+1)) - (b^(2*(j+1))/2) • (1 : E →L[ℂ] E))))

theorem centeredEvenTerm_norm_le (A : F →L[ℂ] F) (V : E →L[ℂ] F)
    (D : E →L[ℂ] E) (b δ : ℝ) (_hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hA : ‖A‖ ≤ δ)
    (hD : ∀ j, ‖D^(2*(j+1)) -
      (b^(2*(j+1))/2) • (1 : E →L[ℂ] E)‖ ≤ b^(2*(j+1))/2)
    (j : ℕ) :
    ‖centeredEvenTerm A V D b j‖ ≤
      (‖V‖/2) * ((δ*b)^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℝ)) := by
  have hp : ‖A^(2*(j+1))‖ ≤ δ^(2*(j+1)) :=
    opNorm_pow_le A δ hδ hA _
  have hcomp := comp_norm_le (A^(2*(j+1)))
    (V.comp (D^(2*(j+1)) - (b^(2*(j+1))/2) • (1 : E →L[ℂ] E)))
  have hright := comp_norm_le_right V
    (D^(2*(j+1)) - (b^(2*(j+1))/2) • (1 : E →L[ℂ] E))
  have hc : ‖(A^(2*(j+1))).comp (V.comp
      (D^(2*(j+1)) - (b^(2*(j+1))/2) • (1 : E →L[ℂ] E)))‖ ≤
      δ^(2*(j+1)) * (‖V‖ * (b^(2*(j+1))/2)) := by
    apply hcomp.trans
    apply mul_le_mul hp
      (hright.trans (mul_le_mul_of_nonneg_left (hD j) (norm_nonneg _)))
      (norm_nonneg _) (by positivity)
  rw [centeredEvenTerm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      0 ≤ (Nat.factorial (2*(j+1)) : ℝ)⁻¹)]
  calc
    _ ≤ (Nat.factorial (2*(j+1)) : ℝ)⁻¹ *
      (δ^(2*(j+1)) * (‖V‖ * (b^(2*(j+1))/2))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The complete exact centered remainder is absolutely summable, with the
factor one half that strengthens the support constant in the paper. -/
theorem centeredEvenSeries_summable_and_norm_le
    [CompleteSpace F]
    (A : F →L[ℂ] F) (V : E →L[ℂ] F) (D : E →L[ℂ] E)
    (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hA : ‖A‖ ≤ δ)
    (hD : ∀ j, ‖D^(2*(j+1)) -
      (b^(2*(j+1))/2) • (1 : E →L[ℂ] E)‖ ≤ b^(2*(j+1))/2) :
    Summable (fun j => ‖centeredEvenTerm A V D b j‖) ∧
      Summable (centeredEvenTerm A V D b) ∧
      ‖∑' j, centeredEvenTerm A V D b j‖ ≤
        ((Real.cosh (δ*b)-1)/2)*‖V‖ := by
  let majorant : ℕ → ℝ := fun j =>
    (‖V‖/2)*((δ*b)^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℝ))
  have hs : Summable majorant :=
    (HorizontalPhaseBootstrap.cosh_tail_summable (δ*b)).mul_left (‖V‖/2)
  have hn : ∀ j, ‖centeredEvenTerm A V D b j‖ ≤ majorant j :=
    centeredEvenTerm_norm_le A V D b δ hb hδ hA hD
  have hnorm : Summable (fun j => ‖centeredEvenTerm A V D b j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn hs
  have hsum : Summable (centeredEvenTerm A V D b) :=
    Summable.of_norm_bounded hs hn
  refine ⟨hnorm, hsum, ?_⟩
  calc
    _ ≤ ∑' j, ‖centeredEvenTerm A V D b j‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, majorant j := Summable.tsum_le_tsum hn hnorm hs
    _ = _ := by
      dsimp only [majorant]
      rw [tsum_mul_left, HorizontalPhaseBootstrap.cosh_tail_tsum]
      ring

end Series

section Frame
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Deterministic finite frame transfer from the exact centered factorization.
The negative sinh square is retained explicitly in the hypothesis. -/
theorem norm_lower_of_centered_factorization
    (V C S Q : E →L[ℂ] F) (K : F →L[ℂ] F)
    (hminus k q : ℝ) (hh : 0 ≤ hminus) (hk : 0 < k)
    (hfactor : C = K.comp V + Q)
    (hK : ‖K‖ ≤ k) (hQ : ‖Q‖ ≤ q)
    (hform : ∀ x, hminus*‖x‖^2 ≤ ‖C x‖^2 - ‖S x‖^2) :
    ∀ x, ((Real.sqrt hminus-q)/k)*‖x‖ ≤ ‖V x‖ := by
  intro x
  have hCx : Real.sqrt hminus*‖x‖ ≤ ‖C x‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).1
    rw [mul_pow, Real.sq_sqrt hh]
    exact le_trans (hform x) (sub_le_self _ (sq_nonneg _))
  have hupper : ‖C x‖ ≤ k*‖V x‖ + q*‖x‖ := by
    rw [hfactor, add_apply, ContinuousLinearMap.comp_apply]
    apply (norm_add_le _ _).trans
    exact add_le_add
      ((K.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _)))
      ((Q.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)))
  have hline : (Real.sqrt hminus-q)*‖x‖ ≤ k*‖V x‖ := by
    linarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hk).2 (by simpa only [mul_comm] using hline)

/-- A positive deterministic centered gap makes the analysis map injective. -/
theorem injective_of_centered_factorization
    (V C S Q : E →L[ℂ] F) (K : F →L[ℂ] F)
    (hminus k q : ℝ) (hh : 0 ≤ hminus) (hk : 0 < k)
    (hfactor : C = K.comp V + Q)
    (hK : ‖K‖ ≤ k) (hQ : ‖Q‖ ≤ q)
    (hform : ∀ x, hminus*‖x‖^2 ≤ ‖C x‖^2 - ‖S x‖^2)
    (hgap : q < Real.sqrt hminus) : Function.Injective V := by
  intro x y hxy
  have hx : V (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hl := norm_lower_of_centered_factorization V C S Q K
    hminus k q hh hk hfactor hK hQ hform (x-y)
  rw [hx, norm_zero] at hl
  have hc : 0 < (Real.sqrt hminus-q)/k := div_pos (sub_pos.mpr hgap) hk
  have hx0 : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hx0)

end Frame

/-- Polynomial certificate for the improved asymptotic gap. The exact root
is z=7/5; no floating-point numerical premise occurs. -/
theorem centered_gap_polynomial {z : ℝ} (hz : 1 ≤ z) (hupper : z < 7/5) :
    0 < 2-z^2 ∧ (z-1)^2 < 4*(2-z^2) := by
  have hs : 0 < (7/5-z)*(7/5+z) := mul_pos (by linarith) (by linarith)
  have hg : 0 < (7/5-z)*(z+1) := mul_pos (by linarith) (by linarith)
  constructor
  · nlinarith [hs]
  · nlinarith [hg]

/-- The strict square-root gap is equivalent to the centered polynomial
certificate used at the improved constant. -/
theorem centered_gap_sqrt {z : ℝ} (hz : 1 ≤ z) (hupper : z < 7/5) :
    (z-1)/2 < Real.sqrt (2-z^2) := by
  obtain ⟨hpos, hpoly⟩ := centered_gap_polynomial hz hupper
  have hs := Real.sq_sqrt hpos.le
  have hn := Real.sqrt_nonneg (2-z^2)
  nlinarith

/-- Exact improved support constant; decimals play no role in certification. -/
def centeredSupportConstant : ℝ := Real.sqrt ((8/3)*Real.arcosh (7/5))

theorem centeredSupportConstant_pos : 0 < centeredSupportConstant := by
  unfold centeredSupportConstant
  apply Real.sqrt_pos.2
  exact mul_pos (by norm_num) (Real.arcosh_pos (by norm_num))

theorem cosh_lt_seven_fifths_iff {c : ℝ} (hc : 0 ≤ c) :
    Real.cosh (3*c^2/8) < 7/5 ↔ c < centeredSupportConstant := by
  have ha : 0 ≤ Real.arcosh (7/5) := Real.arcosh_nonneg (by norm_num)
  have hp : 0 ≤ (8/3)*Real.arcosh (7/5) := by positivity
  have hs := Real.sq_sqrt hp
  have ht : Real.cosh (3*c^2/8) < 7/5 ↔ 3*c^2/8 < Real.arcosh (7/5) := by
    calc
      (Real.cosh (3*c^2/8) < 7/5) ↔
          Real.cosh (3*c^2/8) < Real.cosh (Real.arcosh (7/5)) := by
        rw [Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 7/5)]
      _ ↔ 3*c^2/8 < Real.arcosh (7/5) := by
        rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity), abs_of_nonneg ha]
  rw [ht]
  unfold centeredSupportConstant
  rw [← sq_lt_sq₀ hc (Real.sqrt_nonneg _)]
  rw [hs]
  constructor <;> intro h <;> nlinarith

/-- Exact support-scale constant discharges the centered finite polynomial
gap; actual Landau and zero-density premises are separate application inputs. -/
theorem centered_support_gap {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c < centeredSupportConstant) :
    0 < 2-(Real.cosh (3*c^2/8))^2 ∧
      (Real.cosh (3*c^2/8)-1)/2 <
        Real.sqrt (2-(Real.cosh (3*c^2/8))^2) := by
  have hu := (cosh_lt_seven_fifths_iff hc).2 hsmall
  have hz : 1 ≤ Real.cosh (3*c^2/8) := by
    have h := HorizontalPhaseBootstrap.cosh_tail_tsum (3*c^2/8)
    have hn : 0 ≤ ∑' j : ℕ,
        (3*c^2/8)^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℝ) := by
      apply tsum_nonneg
      intro j
      positivity
    linarith
  exact ⟨(centered_gap_polynomial hz hu).1, centered_gap_sqrt hz hu⟩


end RiemannResearch.Analysis.CenteredHyperbolicFrames

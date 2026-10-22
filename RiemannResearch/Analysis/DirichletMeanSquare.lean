import RiemannResearch.Analysis.FiniteOscillatoryKernel
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import RiemannResearch.RH.WeilExplicitFormula.MV.Final
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite continuous mean squares of exponential polynomials

This is the elementary continuous mean-value component of the prime-polynomial
moment method. The exact identity retains all signed off-diagonal terms. The
bound is proved by integrating each nonzero frequency, not by assuming a
mean-value estimate. No zeta approximation or Tsang bound is asserted here.

Source for the Hilbert-inequality ingredient: H. L. Montgomery and R. C.
Vaughan, "Hilbert's inequality", J. London Math. Soc. (2) 8 (1974), 73--82.
The existing `Zeta23.MV.mvDiag_thirteen` proves the ingredient used here;
the continuous integral estimate follows by retaining both signed endpoints.
-/

noncomputable section
open MeasureTheory Complex
open scoped BigOperators

namespace RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.ZeroOrdinate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def polynomial (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, a i * phase (ω i) t

theorem polynomial_continuous (a : ι → ℂ) (ω : ι → ℝ) :
    Continuous (polynomial a ω) := by
  unfold polynomial phase
  fun_prop

theorem integral_phase (A B ω : ℝ) :
    (∫ t in A..B, phase ω t) = finitePhaseKernel A B ω := by
  convert integral_phase_eq_finitePhaseKernel A B ω using 1
  congr 1
  funext t
  unfold phase
  congr 1
  push_cast
  ring

theorem polynomial_conj_mul (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    star (polynomial a ω t) * polynomial a ω t =
      ∑ i, ∑ j, star (a i) * a j * phase (ω j - ω i) t := by
  simp only [polynomial, star_sum, star_mul, Finset.sum_mul_sum, phase_sub]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The complete signed finite-interval identity. -/
theorem integral_polynomial_conj_mul (a : ι → ℂ) (ω : ι → ℝ) (A B : ℝ) :
    (∫ t in A..B, star (polynomial a ω t) * polynomial a ω t) =
      ∑ i, ∑ j, star (a i) * a j * finitePhaseKernel A B (ω j - ω i) := by
  simp_rw [polynomial_conj_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, integral_phase]
    · intro j hj
      apply Continuous.intervalIntegrable
      unfold phase
      fun_prop
  · intro i hi
    apply Continuous.intervalIntegrable
    unfold phase
    fun_prop

private theorem conj_mul_eq_norm_sq (z : ℂ) :
    star z * z = (‖z‖ ^ 2 : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq]
  simpa only [Complex.star_def, mul_comm] using Complex.mul_conj z

/-- The same exact identity, expressed as the ordinary real L² integral. -/
theorem integral_norm_sq_eq_gram (a : ι → ℂ) (ω : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖polynomial a ω t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, star (a i) * a j * finitePhaseKernel A B (ω j - ω i) := by
  rw [← integral_polynomial_conj_mul]
  simp_rw [conj_mul_eq_norm_sq]
  rw [intervalIntegral.integral_ofReal]

def offDiagonal (a : ι → ℂ) (ω : ι → ℝ) (A B : ℝ) : ℂ :=
  ∑ i, ∑ j, if i = j then 0 else
    star (a i) * a j * finitePhaseKernel A B (ω j - ω i)

/-- Diagonal plus the full signed off-diagonal, with both interval endpoints. -/
theorem integral_norm_sq_eq_diagonal_add (a : ι → ℂ) (ω : ι → ℝ) (A B : ℝ) :
    ((∫ t in A..B, ‖polynomial a ω t‖ ^ 2 : ℝ) : ℂ) =
      (((B - A) * ∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) + offDiagonal a ω A B := by
  rw [integral_norm_sq_eq_gram]
  unfold offDiagonal
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hsplit : (∑ j, star (a i) * a j * finitePhaseKernel A B (ω j - ω i)) =
      (∑ j, if i = j then star (a i) * a j *
        finitePhaseKernel A B (ω j - ω i) else 0) +
      ∑ j, if i = j then 0 else star (a i) * a j *
        finitePhaseKernel A B (ω j - ω i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  rw [hsplit]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self,
    finitePhaseKernel_zero, conj_mul_eq_norm_sq]
  push_cast
  ring

/-- A proved off-diagonal estimate from an explicit frequency separation. -/
theorem norm_offDiagonal_le (a : ι → ℂ) (ω : ι → ℝ) (A B δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i j, i ≠ j → δ ≤ |ω j - ω i|) :
    ‖offDiagonal a ω A B‖ ≤ (2 / δ) * (∑ i, ‖a i‖) ^ 2 := by
  have hkernel (i j : ι) (hij : i ≠ j) :
      ‖finitePhaseKernel A B (ω j - ω i)‖ ≤ 2 / δ := by
    have hf : 0 < |ω j - ω i| := lt_of_lt_of_le hδ (hsep i j hij)
    exact (norm_finitePhaseKernel_le (abs_pos.mp hf) A B).trans
      (div_le_div_of_nonneg_left (by norm_num) hδ (hsep i j hij))
  calc
    ‖offDiagonal a ω A B‖ ≤
        ∑ i, ∑ j, ‖if i = j then 0 else star (a i) * a j *
          finitePhaseKernel A B (ω j - ω i)‖ := by
      unfold offDiagonal
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * (2 / δ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · simp only [if_pos hij, norm_zero]
        positivity
      · simp only [if_neg hij, norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left (hkernel i j hij) (by positivity)
    _ = (2 / δ) * (∑ i, ‖a i‖) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Continuous L² estimate for separated real frequencies. -/
theorem integral_norm_sq_le (a : ι → ℂ) (ω : ι → ℝ) (A B δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i j, i ≠ j → δ ≤ |ω j - ω i|) :
    (∫ t in A..B, ‖polynomial a ω t‖ ^ 2) ≤
      (B - A) * ∑ i, ‖a i‖ ^ 2 + (2 / δ) * (∑ i, ‖a i‖) ^ 2 := by
  have hid := congrArg Complex.re (integral_norm_sq_eq_diagonal_add a ω A B)
  simp only [Complex.ofReal_re, Complex.add_re] at hid
  rw [hid]
  exact _root_.add_le_add le_rfl
    ((Complex.re_le_norm _).trans (norm_offDiagonal_le a ω A B δ hδ hsep))

/-- The actual endpoint quadratic Hilbert form, before estimating it. -/
def endpointHilbert (a : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i, ∑ j, if i = j then 0 else
    (a i * phase (ω i) t) * star (a j * phase (ω j) t) /
      ((ω i - ω j : ℝ) : ℂ)

private theorem finitePhaseKernel_eq_phase (A B v : ℝ) (hv : v ≠ 0) :
    finitePhaseKernel A B v =
      (phase v B - phase v A) / ((v : ℂ) * Complex.I) := by
  have he (t : ℝ) : Complex.exp (((v : ℂ) * Complex.I) * (t : ℂ)) =
      phase v t := by
    unfold phase
    congr 1
    push_cast
    ring
  simp only [finitePhaseKernel, if_neg hv, he]

private theorem phase_weight_mul_star (a : ι → ℂ) (ω : ι → ℝ)
    (i j : ι) (t : ℝ) :
    (a i * phase (ω i) t) * star (a j * phase (ω j) t) =
      star (a j) * a i * phase (ω i - ω j) t := by
  rw [star_mul, phase_sub]
  ring

/-- Exact signed endpoint identity underlying the continuous mean-value theorem. -/
theorem offDiagonal_eq_endpoints (a : ι → ℂ) (ω : ι → ℝ)
    (hω : Function.Injective ω) (A B : ℝ) :
    offDiagonal a ω A B = (endpointHilbert a ω B - endpointHilbert a ω A) /
      Complex.I := by
  unfold offDiagonal endpointHilbert
  conv_lhs => rw [Finset.sum_comm]
  simp only [sub_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    have hv : ω i - ω j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hω h))
    simp only [if_neg hij, if_neg hji, phase_weight_mul_star]
    rw [finitePhaseKernel_eq_phase A B _ hv]
    simp only [div_mul_eq_div_div]
    ring

/-- Montgomery--Vaughan's proved diagonal inequality controls each endpoint. -/
theorem norm_endpointHilbert_le (a : ι → ℂ) (ω δ : ι → ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) (t : ℝ) :
    ‖endpointHilbert a ω t‖ ≤ 13 * ∑ i, ‖a i‖ ^ 2 / δ i := by
  have h := Zeta23.MV.mvDiag_thirteen ι ω δ
    (fun i => a i * phase (ω i) t) hω hδ hsep
  simpa only [endpointHilbert, Complex.star_def, norm_mul, phase_norm, mul_one] using h

/-- Sharp-in-length continuous mean-value remainder, with explicit constant 26. -/
theorem norm_offDiagonal_le_weighted (a : ι → ℂ) (ω δ : ι → ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) (A B : ℝ) :
    ‖offDiagonal a ω A B‖ ≤ 26 * ∑ i, ‖a i‖ ^ 2 / δ i := by
  rw [offDiagonal_eq_endpoints a ω hω, norm_div, Complex.norm_I, div_one]
  calc
    _ ≤ ‖endpointHilbert a ω B‖ + ‖endpointHilbert a ω A‖ := norm_sub_le _ _
    _ ≤ 13 * (∑ i, ‖a i‖ ^ 2 / δ i) + 13 * (∑ i, ‖a i‖ ^ 2 / δ i) :=
      add_le_add (norm_endpointHilbert_le a ω δ hω hδ hsep B)
        (norm_endpointHilbert_le a ω δ hω hδ hsep A)
    _ = _ := by ring

/-- The analytic mean-value error, expressed entirely as an ordinary real integral. -/
theorem abs_integral_norm_sq_sub_le (a : ι → ℂ) (ω δ : ι → ℝ)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|) (A B : ℝ) :
    |(∫ t in A..B, ‖polynomial a ω t‖ ^ 2) -
      (B - A) * ∑ i, ‖a i‖ ^ 2| ≤ 26 * ∑ i, ‖a i‖ ^ 2 / δ i := by
  have he : (((∫ t in A..B, ‖polynomial a ω t‖ ^ 2) -
      (B - A) * ∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) = offDiagonal a ω A B := by
    rw [Complex.ofReal_sub, integral_norm_sq_eq_diagonal_add]
    ring
  have hn := congrArg norm he
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn]
  exact norm_offDiagonal_le_weighted a ω δ hω hδ hsep A B

/-- Distinct positive integer frequencies have an unconditional O(N) mean-square
error. This is the analytic estimate needed after expanding a prime polynomial
to its kth power. -/
theorem integral_log_polynomial_norm_sq_le (a : ι → ℂ) (n : ι → ℕ)
    (hn : Function.Injective n) (hnpos : ∀ i, 1 ≤ n i)
    (N : ℕ) (hnN : ∀ i, n i ≤ N) (A B : ℝ) :
    (∫ t in A..B, ‖polynomial a (fun i => Real.log (n i)) t‖ ^ 2) ≤
      (B - A + 52 * (N : ℝ)) * ∑ i, ‖a i‖ ^ 2 := by
  have hpos (i : ι) : (0 : ℝ) < n i := by exact_mod_cast hnpos i
  have hinj : Function.Injective (fun i => Real.log (n i : ℝ)) := by
    intro i j hij
    apply hn
    exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos i))
      (Set.mem_Ioi.mpr (hpos j)) hij
  have h := abs_integral_norm_sq_sub_le a (fun i => Real.log (n i))
    (fun i => 1 / (2 * (n i : ℝ))) hinj
    (fun i => by have hi := hpos i; positivity)
    (fun i j hij => Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub
      (hnpos i) (hnpos j) (fun he => hij (hn he))) A B
  have hw : 26 * (∑ i, ‖a i‖ ^ 2 / (1 / (2 * (n i : ℝ)))) ≤
      52 * (N : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
    simp only [div_div_eq_mul_div, div_one]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hni : (n i : ℝ) ≤ N := by exact_mod_cast hnN i
    nlinarith [sq_nonneg ‖a i‖, mul_le_mul_of_nonneg_right hni (sq_nonneg ‖a i‖)]
  have hupper := (abs_le.mp h).2
  nlinarith

end RiemannResearch.Analysis.DirichletMeanSquare

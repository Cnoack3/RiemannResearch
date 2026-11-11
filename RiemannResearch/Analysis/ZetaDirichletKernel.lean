import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# The zeta kernel as an actual Hilbert-space Gram kernel

Source: user-provided V_vector_space_RH.pdf, Section 5; Hedenmalm--Lindqvist--Seip,
A Hilbert space of Dirichlet series and systems of dilated functions in L2(0,1),
Duke Math. J. 86 (1997), https://arxiv.org/abs/math/9512211.
The reference supports the kernel and Dirichlet-Hilbert-space statements.
The proof uses Mathlib's actual zeta Dirichlet series.

We construct the vector with coordinates (n+1)^(-s) in complex l2, prove its
exact Gram formula, and give the complete finite quadratic identity and the
bounded Dirichlet evaluation functional. Lean's inner product is conjugate
linear in its first argument, hence the kernel is zeta(star s + w).

This is a direct integer-coordinate realization of the zeta kernel. It does
not construct the prime-power logarithmic kernel, symmetric Fock space, or the
occupation-basis grouping claimed in the report. Those remain separate tasks.
RH consumer: testing positivity and the scope of zero-sampling kernels.
-/

noncomputable section
open scoped BigOperators ComplexConjugate ENNReal
namespace RiemannResearch.Analysis.ZetaDirichletKernel

def feature (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-s * (Real.log ((n : ℝ) + 1) : ℂ))

theorem feature_eq_cpow (s : ℂ) (n : ℕ) :
    feature s n = 1 / ((n : ℂ) + 1) ^ s := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnC : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnC, one_div, ← Complex.exp_neg]
  have he : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; rfl
  rw [← he, ← Complex.ofReal_log hn.le]
  unfold feature
  congr 1
  ring

/-- The exact coordinate norm, including the critical exponent. -/
theorem feature_norm_sq (s : ℂ) (n : ℕ) :
    ‖feature s n‖ ^ 2 = 1 / ((n : ℝ) + 1) ^ (2 * s.re) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [feature, Complex.norm_exp, ← Real.exp_nat_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [one_div, Real.rpow_def_of_pos hn, ← Real.exp_neg]
  congr 1
  ring

/-- The open half-plane is the exact domain of this l2 feature map, so its
unchanged coordinates do not define a Hilbert vector on the critical line. -/
theorem feature_memℓp_iff (s : ℂ) :
    Memℓp (feature s) 2 ↔ 1 / 2 < s.re := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, feature_norm_sq]
  have h := Real.summable_one_div_nat_add_rpow 1 (2 * s.re)
  have hab (n : ℕ) : |(n : ℝ) + 1| = (n : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  simp only [hab] at h
  rw [h]
  constructor <;> intro h <;> linarith

theorem feature_pair (s w : ℂ) (n : ℕ) :
    star (feature s n) * feature w n = feature (star s + w) n := by
  change (starRingEnd ℂ) (Complex.exp _) * Complex.exp _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, map_neg, Complex.conj_ofReal, feature, Complex.star_def]
  congr 1
  ring

theorem feature_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (feature s) (riemannZeta s) := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Complex.summable_one_div_nat_cpow.mpr hs).comp_injective Nat.succ_injective
  have he : feature s = fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
    funext n
    exact feature_eq_cpow s n
  rw [he, zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact h.hasSum

theorem pair_hasSum (s w : ℂ) (hs : 1 / 2 < s.re) (hw : 1 / 2 < w.re) :
    HasSum (fun n => star (feature s n) * feature w n)
      (riemannZeta (star s + w)) := by
  simp_rw [feature_pair]
  apply feature_hasSum
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  linarith

theorem finite_gram_hasSum {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    HasSum (fun n => star (∑ i, c i * feature (s i) n) *
      (∑ i, c i * feature (s i) n))
      (∑ i, ∑ j, star (c i) * riemannZeta (star (s i) + s j) * c j) := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun j _ =>
      ((pair_hasSum (s i) (s j) (hs i) (hs j)).mul_left (star (c i))).mul_right (c j)))
  have he (n : ℕ) :
      star (∑ i, c i * feature (s i) n) * (∑ i, c i * feature (s i) n) =
        ∑ i, ∑ j, star (c i) * (star (feature (s i) n) * feature (s j) n) * c j := by
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  exact h

private theorem star_mul_re (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [mul_comm]
  change RCLike.re (inner ℂ z z) = ‖z‖ ^ 2
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm

theorem feature_norm_sq_summable (s : ℂ) (hs : 1 / 2 < s.re) :
    Summable (fun n => ‖feature s n‖ ^ 2) := by
  have h := Complex.reCLM.hasSum (pair_hasSum s s hs hs)
  change HasSum (fun n => (star (feature s n) * feature s n).re)
    (riemannZeta (star s + s)).re at h
  simpa only [star_mul_re] using h.summable

def vector (s : ℂ) (hs : 1 / 2 < s.re) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨feature s, by
    apply memℓp_gen
    simpa using feature_norm_sq_summable s hs⟩

theorem vector_inner (s w : ℂ) (hs : 1 / 2 < s.re) (hw : 1 / 2 < w.re) :
    inner ℂ (vector s hs) (vector w hw) = riemannZeta (star s + w) := by
  rw [lp.inner_eq_tsum]
  simp only [RCLike.inner_apply', vector]
  change (∑' n, star (feature s n) * feature w n) = _
  exact (pair_hasSum s w hs hw).tsum_eq

theorem vector_norm_sq (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖vector s hs‖ ^ 2 = (riemannZeta (star s + s)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), vector_inner]
  rfl

theorem finite_gram_energy {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    (∑ i, ∑ j, star (c i) * riemannZeta (star (s i) + s j) * c j).re =
      ∑' n, ‖∑ i, c i * feature (s i) n‖ ^ 2 := by
  have h := Complex.reCLM.hasSum (finite_gram_hasSum s c hs)
  change HasSum (fun n => (star (∑ i, c i * feature (s i) n) *
    (∑ i, c i * feature (s i) n)).re)
    (∑ i, ∑ j, star (c i) * riemannZeta (star (s i) + s j) * c j).re at h
  simpa only [star_mul_re] using h.tsum_eq.symm

theorem finite_gram_nonneg {ι : Type*} [Fintype ι]
    (s c : ι → ℂ) (hs : ∀ i, 1 / 2 < (s i).re) :
    0 ≤ (∑ i, ∑ j, star (c i) * riemannZeta (star (s i) + s j) * c j).re := by
  rw [finite_gram_energy s c hs]
  exact tsum_nonneg (fun _ => sq_nonneg _)


theorem feature_star (s : ℂ) (n : ℕ) :
    star (feature (star s) n) = feature s n := by
  have h := feature_pair (star s) 0 n
  simpa only [feature, neg_zero, zero_mul, Complex.exp_zero, mul_one,
    star_star, add_zero] using h

/-- Every square-summable coefficient vector defines a convergent Dirichlet
series in the open half-plane Re(s)>1/2, with its Riesz evaluation vector. -/
theorem dirichlet_series_hasSum (a : lp (fun _ : ℕ => ℂ) 2)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    HasSum (fun n => a n * feature s n)
      (inner ℂ (vector (star s)
        (by simpa only [Complex.star_def, Complex.conj_re] using hs)) a) := by
  have hss : 1 / 2 < (star s).re := by
    simpa only [Complex.star_def, Complex.conj_re] using hs
  have he (n : ℕ) :
      inner ℂ (vector (star s) hss n) (a n) = a n * feature s n := by
    rw [RCLike.inner_apply']
    change star (feature (star s) n) * a n = _
    rw [feature_star, mul_comm]
  simpa only [he] using lp.hasSum_inner (𝕜 := ℂ) (vector (star s) hss) a

/-- Exact zeta reproducing-kernel bound for an arbitrary Dirichlet coefficient
vector. No analytic continuation beyond this half-plane is used. -/
theorem dirichlet_series_bound (a : lp (fun _ : ℕ => ℂ) 2)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖∑' n, a n * feature s n‖ ^ 2 ≤
      ‖a‖ ^ 2 * (riemannZeta ((2 * s.re : ℝ) : ℂ)).re := by
  have hss : 1 / 2 < (star s).re := by
    simpa only [Complex.star_def, Complex.conj_re] using hs
  have hnorm : ‖vector (star s) hss‖ ^ 2 =
      (riemannZeta ((2 * s.re : ℝ) : ℂ)).re := by
    rw [vector_norm_sq]
    congr 2
    apply Complex.ext <;> simp <;> ring
  rw [(dirichlet_series_hasSum a s hs).tsum_eq]
  calc
    _ ≤ (‖vector (star s) hss‖ * ‖a‖) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ) (vector (star s) hss) a)
    _ = ‖a‖ ^ 2 * ‖vector (star s) hss‖ ^ 2 := by ring
    _ = _ := by rw [hnorm]

end RiemannResearch.Analysis.ZetaDirichletKernel

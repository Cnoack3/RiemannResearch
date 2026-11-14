import RiemannResearch.Analysis.SampledGaugeCompleteness
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# The prime-power logarithmic Hilbert feature
Source: V_vector_space_RH.pdf, Section 5.1, logarithmic feature construction.
For any square-summable family a with |a_i|<1, the coordinates
a_i^(k+1)/sqrt(k+1) define an actual l2 vector. Its mixed inner product
is the convergent Euler sum of -log(1-conj(a_i)b_i).
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.LogEulerFeature
open SampledGauge

theorem summable_neg_log_one_sub {ι : Type*} (u : ι → ℝ)
    (hs : Summable u) (h : ∀ i, u i < 1) :
    Summable (fun i => -Real.log (1 - u i)) := by
  have hc : Summable (fun i => (u i : ℂ)) :=
    (Complex.ofRealCLM.hasSum hs.hasSum).summable
  have hr := (Complex.reCLM.hasSum hc.clog_one_sub.neg.hasSum).summable
  convert hr using 1
  funext i
  change -Real.log (1 - u i) = (-Complex.log (1 - (u i : ℂ))).re
  rw [Complex.neg_re, Complex.log_re]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (h i))]

def coefficient {ι : Type*} (a : ι → ℂ) (q : ι × ℕ) : ℂ :=
  a q.1 ^ (q.2 + 1) / (Real.sqrt ((q.2 : ℝ) + 1) : ℂ)

theorem coefficient_norm_sq {ι : Type*} (a : ι → ℂ) (q : ι × ℕ) :
    ‖coefficient a q‖ ^ 2 = (‖a q.1‖ ^ 2) ^ (q.2 + 1) / ((q.2 : ℝ) + 1) := by
  rw [coefficient, norm_div, div_pow, norm_pow, pow_right_comm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

theorem coefficient_summable_sq {ι : Type*} (a : ι → ℂ)
    (hs : Summable (fun i => ‖a i‖ ^ 2)) (h : ∀ i, ‖a i‖ < 1) :
    Summable (fun q => ‖coefficient a q‖ ^ 2) := by
  have hi : ∀ i, ‖a i‖ ^ 2 < 1 := by
    intro i
    nlinarith [h i, norm_nonneg (a i)]
  have hf : ∀ i, HasSum (fun n => ‖coefficient a (i,n)‖ ^ 2)
      (-Real.log (1 - ‖a i‖ ^ 2)) := by
    intro i
    simpa only [coefficient_norm_sq] using
      Real.hasSum_pow_div_log_of_abs_lt_one
        (by rw [abs_of_nonneg (sq_nonneg _)]; exact hi i)
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun i => (hf i).summable, ?_⟩
  simpa only [(hf _).tsum_eq] using summable_neg_log_one_sub _ hs hi

def vector {ι : Type*} (a : ι → ℂ)
    (hs : Summable (fun i => ‖a i‖ ^ 2)) (h : ∀ i, ‖a i‖ < 1) : Space (ι × ℕ) :=
  ⟨coefficient a, by
    apply memℓp_gen
    simpa using coefficient_summable_sq a hs h⟩

theorem coefficient_pair {ι : Type*} (a b : ι → ℂ) (q : ι × ℕ) :
    star (coefficient a q) * coefficient b q =
      (star (a q.1) * b q.1) ^ (q.2 + 1) / ((q.2 : ℂ) + 1) := by
  simp only [coefficient, Complex.star_def, map_div₀, map_pow, Complex.conj_ofReal]
  rw [div_mul_div_comm, ← mul_pow]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt (by positivity)

theorem vector_inner {ι : Type*} (a b : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖ ^ 2)) (h'a : ∀ i, ‖a i‖ < 1)
    (hb : Summable (fun i => ‖b i‖ ^ 2)) (h'b : ∀ i, ‖b i‖ < 1) :
    inner ℂ (vector a ha h'a) (vector b hb h'b) =
      ∑' i, -Complex.log (1 - star (a i) * b i) := by
  have hfull : HasSum (fun q => star (coefficient a q) * coefficient b q)
      (inner ℂ (vector a ha h'a) (vector b hb h'b)) := by
    simpa only [RCLike.inner_apply', Complex.star_def, vector] using
      lp.hasSum_inner (𝕜 := ℂ) (vector a ha h'a) (vector b hb h'b)
  have hf : ∀ i, HasSum (fun n => star (coefficient a (i,n)) * coefficient b (i,n))
      (-Complex.log (1 - star (a i) * b i)) := by
    intro i
    have hn : ‖star (a i) * b i‖ < 1 := by
      rw [norm_mul, norm_star]
      nlinarith [h'a i, h'b i, norm_nonneg (a i), norm_nonneg (b i)]
    simpa only [coefficient_pair] using Complex.hasSum_taylorSeries_neg_log' hn
  exact (hfull.prod_fiberwise hf).tsum_eq.symm
end RiemannResearch.Analysis.LogEulerFeature

import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Countable Gaussian tests for physical gap measures

Weierstrass approximation on the compact coordinate exp(-x²) gives a
relative error controlled by the first Gaussian. This controls the whole
line for measures with finite first Gaussian integral. The result is an
application of the compact-interval moment determinacy argument.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.GaussianGapTests

/-- The coordinate takes values in the compact unit interval. -/
def weight (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

private theorem continuous_weight : Continuous weight := by unfold weight; fun_prop
private theorem weight_pos (x : ℝ) : 0 < weight x := Real.exp_pos _
private theorem weight_le_one (x : ℝ) : weight x ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))

/-- Approximation by positive-integer Gaussian powers with a decaying
pointwise error for every continuous even test vanishing beyond radius R. -/
theorem exists_polynomial_gaussian_approx {g : ℝ → ℝ} (hg : Continuous g)
    (he : ∀ x, g (-x) = g x) {R : ℝ} (hR : 0 ≤ R) (hz : ∀ x, R ≤ |x| → g x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x, |g x - weight x * p.eval (weight x)| ≤ ε * weight x := by
  let c := weight R
  let m := fun t : ℝ => max c t
  let F := fun t : ℝ => g (Real.sqrt (-Real.log (m t))) / m t
  have hc : 0 < c := weight_pos R
  have hm : Continuous m := continuous_const.max continuous_id
  have hm0 (t : ℝ) : m t ≠ 0 := (hc.trans_le (le_max_left _ _)).ne'
  have hF : Continuous F := (hg.comp (Real.continuous_sqrt.comp (hm.log hm0).neg)).div hm hm0
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 1 F hF.continuousOn ε hε
  refine ⟨p, fun x => ?_⟩
  have hx : 0 < weight x := weight_pos x
  have heven : g |x| = g x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, he]
  have hid : weight x * F (weight x) = g x := by
    by_cases hc' : c ≤ weight x
    · have hm' : m (weight x) = weight x := max_eq_right hc'
      dsimp only [F]
      rw [hm', weight, Real.log_exp, neg_neg, Real.sqrt_sq_eq_abs, heven]
      field_simp
    · have hxc : weight x < c := lt_of_not_ge hc'
      have hsq : R^2 < x^2 := by
        change Real.exp (-(x^2)) < Real.exp (-(R^2)) at hxc
        linarith only [Real.exp_lt_exp.mp hxc]
      have hRx : R ≤ |x| := by
        by_contra! h
        have hh := (sq_lt_sq₀ (abs_nonneg x) hR).2 h
        rw [sq_abs] at hh
        linarith
      have hm' : m (weight x) = c := max_eq_left hxc.le
      dsimp only [F]
      rw [hm', show Real.log c = -(R^2) by exact Real.log_exp _, neg_neg, Real.sqrt_sq hR,
        hz R (by rw [abs_of_nonneg hR]), hz x hRx, zero_div, mul_zero]
  have hnear := (hp (weight x) ⟨hx.le, weight_le_one x⟩).le
  rw [← hid, ← mul_sub, abs_mul, abs_of_pos hx, abs_sub_comm]
  simpa only [mul_comm ε] using mul_le_mul_of_nonneg_left hnear hx.le

private theorem integrable_power {μ : Measure ℝ} (hμ : Integrable weight μ) (n : ℕ) :
    Integrable (fun x => weight x ^ (n + 1)) μ := by
  apply hμ.mono' (continuous_weight.pow _).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖weight x ^ (n + 1)‖ ≤ weight x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (weight_pos x).le _), pow_succ]
    exact mul_le_of_le_one_left (weight_pos x).le
      (pow_le_one₀ (weight_pos x).le (weight_le_one x))

private theorem profile_sum (p : Polynomial ℝ) (x : ℝ) :
    weight x * p.eval (weight x) =
      ∑ n ∈ p.support, p.coeff n * weight x ^ (n+1) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [pow_succ]
  ring

private theorem profile_integral (p : Polynomial ℝ) {μ : Measure ℝ} (hμ : Integrable weight μ) :
    Integrable (fun x => weight x * p.eval (weight x)) μ ∧
    (∫ x, weight x * p.eval (weight x) ∂μ) =
      ∑ n ∈ p.support, p.coeff n * ∫ x, weight x^(n+1) ∂μ := by
  have hi (n : ℕ) := (integrable_power hμ n).const_mul (p.coeff n)
  simp_rw [profile_sum]
  refine ⟨integrable_finsetSum _ (fun n _ => hi n), ?_⟩
  rw [integral_finsetSum _ (fun n _ => hi n)]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

private theorem integral_profile_error {g : ℝ → ℝ} (hg : Continuous g)
    {p : Polynomial ℝ} {ε : ℝ} (hp : ∀ x, |g x - weight x * p.eval (weight x)| ≤ ε * weight x)
    {μ : Measure ℝ} (hμ : Integrable weight μ) :
    |(∫ x, g x ∂μ) - ∫ x, weight x * p.eval (weight x) ∂μ| ≤ ε * ∫ x, weight x ∂μ := by
  let Q := fun x : ℝ => weight x * p.eval (weight x)
  have hQ : Continuous Q := continuous_weight.mul (p.continuous.comp continuous_weight)
  have hd : Integrable (fun x => g x - Q x) μ := (hμ.const_mul ε).mono'
    (hg.sub hQ).aestronglyMeasurable (ae_of_all _ hp)
  have hq := (profile_integral p hμ).1
  have hi : Integrable g μ :=
    (hd.add hq).congr (ae_of_all _ fun x => by change g x - Q x + Q x = g x; ring)
  rw [← integral_sub hi hq, ← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hd.norm (hμ.const_mul ε) hp)

/-- The first Gaussian bounds approximation error for the full family automatically.
Convergence at the positive integer Gaussian powers therefore suffices for all
continuous compactly supported even gap tests. -/
theorem tendsto_even_gap_integral_of_gaussian_moments {ι : Type*} {l : Filter ι}
    (μ : ι → Measure ℝ) (ν : Measure ℝ) (hμ : ∀ i, Integrable weight (μ i))
    (hν : Integrable weight ν)
    (hm : ∀ n : ℕ, Tendsto (fun i => ∫ x, weight x ^ (n + 1) ∂(μ i)) l
      (𝓝 (∫ x, weight x ^ (n + 1) ∂ν)))
    {g : ℝ → ℝ} (hg : Continuous g) (he : ∀ x, g (-x) = g x)
    {R : ℝ} (hR : 0 ≤ R) (hz : ∀ x, R ≤ |x| → g x = 0) :
    Tendsto (fun i => ∫ x, g x ∂(μ i)) l (𝓝 (∫ x, g x ∂ν)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C := (∫ x, weight x ∂ν) + 1
  have hC : 0 < C := by
    dsimp [C]
    have hn : 0 ≤ ∫ x, weight x ∂ν := integral_nonneg fun x => (weight_pos x).le
    linarith
  let d := ε / (4*C)
  have hd : 0 < d := div_pos hε (by positivity)
  have hdC : d * C = ε/4 := by dsimp [d]; field_simp [hC.ne']
  obtain ⟨p,hp⟩ := exists_polynomial_gaussian_approx hg he hR hz hd
  let Q := fun x : ℝ => weight x * p.eval (weight x)
  have hpoly : Tendsto (fun i => ∫ x, Q x ∂(μ i)) l (𝓝 (∫ x, Q x ∂ν)) := by
    dsimp only [Q]
    simp_rw [(profile_integral p (hμ _)).2, (profile_integral p hν).2]
    exact tendsto_finsetSum _ (fun n _ => (hm n).const_mul _)
  have hfirst : Tendsto (fun i => ∫ x, weight x ∂(μ i)) l (𝓝 (∫ x, weight x ∂ν)) := by
    simpa using hm 0
  have hmass := hfirst.eventually (gt_mem_nhds (show (∫ x, weight x ∂ν) < C by dsimp [C]; linarith))
  have hnear := Metric.tendsto_nhds.mp hpoly (ε/2) (half_pos hε)
  filter_upwards [hmass, hnear] with i hi hn
  have ha := (integral_profile_error hg hp (hμ i)).trans
    (mul_le_mul_of_nonneg_left (le_of_lt hi) hd.le)
  have hv := (integral_profile_error hg hp hν).trans
    (mul_le_mul_of_nonneg_left (show (∫ x, weight x ∂ν) ≤ C by dsimp [C]; linarith) hd.le)
  rw [hdC] at ha hv
  change |(∫ x, g x ∂(μ i)) - ∫ x, Q x ∂(μ i)| ≤ ε/4 at ha
  change |(∫ x, g x ∂ν) - ∫ x, Q x ∂ν| ≤ ε/4 at hv
  rw [Real.dist_eq] at hn ⊢
  rcases abs_le.mp ha with ⟨ha₁,ha₂⟩
  rcases abs_le.mp hv with ⟨hv₁,hv₂⟩
  rcases abs_lt.mp hn with ⟨hn₁,hn₂⟩
  rw [abs_lt]
  constructor <;> linarith only [ha₁,ha₂,hv₁,hv₂,hn₁,hn₂]

#print axioms tendsto_even_gap_integral_of_gaussian_moments
end RiemannResearch.Analysis.GaussianGapTests

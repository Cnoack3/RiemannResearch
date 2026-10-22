import RiemannResearch.Analysis.AnalyticZeroPersistence
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonreal zeros of finite exponential polynomials with a zero at one

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. This uses finite compact-torus recurrence and the elementary
zero persistence theorem, without a Mellin injectivity hypothesis.
-/

namespace RiemannResearch.Analysis
open Set Filter Metric
open scoped Topology BigOperators
noncomputable section

def finiteExponentialPolynomial {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (freq : ι → ℝ) (s : ℂ) : ℂ :=
  ∑ i, a i * Complex.exp ((freq i : ℂ) * (s - 1))

theorem finiteExponentialPolynomial_differentiable {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (freq : ι → ℝ) : Differentiable ℂ (finiteExponentialPolynomial a freq) := by
  unfold finiteExponentialPolynomial
  fun_prop

private theorem phase_return_complex {ι : Type*} [Fintype ι]
    (freq : ι → ℝ) (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ i,
      ‖Complex.exp ((freq i : ℂ) * ((n : ℂ) * Complex.I)) - 1‖ < ε := by
  obtain ⟨n, hn, hphase⟩ := finite_circle_phases_return (fun i => Circle.exp (freq i)) ε hε N
  refine ⟨n, hn, ?_⟩
  intro i
  have h := hphase i
  change dist (Circle.coeHom ((Circle.exp (freq i)) ^ n)) (Circle.coeHom 1) < ε at h
  rw [map_pow, map_one] at h
  change dist ((Circle.exp (freq i) : ℂ) ^ n) (1 : ℂ) < ε at h
  rw [Circle.coe_exp, ← Complex.exp_nat_mul, dist_eq_norm] at h
  have he : (n : ℂ) * ((freq i : ℂ) * Complex.I) =
      (freq i : ℂ) * ((n : ℂ) * Complex.I) := by ring
  rwa [he] at h

private theorem exponential_term_bound (freq R : ℝ) (s : ℂ)
    (hs : ‖s - 1‖ ≤ R) :
    ‖Complex.exp ((freq : ℂ) * (s - 1))‖ ≤ Real.exp (|freq| * R) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    ((freq : ℂ) * (s - 1)).re ≤ ‖(freq : ℂ) * (s - 1)‖ := Complex.re_le_norm _
    _ = |freq| * ‖s - 1‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |freq| * R := mul_le_mul_of_nonneg_left hs (abs_nonneg freq)

/-- Arbitrarily late vertical translates approximate the entire finite
polynomial uniformly on a prescribed closed disk. -/
theorem finiteExponentialPolynomial_vertical_return {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (freq : ι → ℝ) (R ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ s : ℂ, ‖s - 1‖ ≤ R →
      ‖finiteExponentialPolynomial a freq (s + (n : ℂ) * Complex.I) -
        finiteExponentialPolynomial a freq s‖ < ε := by
  let C : ℝ := ∑ i, ‖a i‖ * Real.exp (|freq i| * R)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  let η : ℝ := ε / (C + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨n, hn, hp⟩ := phase_return_complex freq η hη N
  refine ⟨n, hn, ?_⟩
  intro s hs
  have he : finiteExponentialPolynomial a freq (s + (n : ℂ) * Complex.I) -
      finiteExponentialPolynomial a freq s =
      ∑ i, (a i * Complex.exp ((freq i : ℂ) * (s - 1))) *
        (Complex.exp ((freq i : ℂ) * ((n : ℂ) * Complex.I)) - 1) := by
    unfold finiteExponentialPolynomial
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (freq i : ℂ) * (s + (n : ℂ) * Complex.I - 1) =
      (freq i : ℂ) * (s - 1) + (freq i : ℂ) * ((n : ℂ) * Complex.I) by ring,
      Complex.exp_add]
    ring
  rw [he]
  calc
    _ ≤ ∑ i, ‖(a i * Complex.exp ((freq i : ℂ) * (s - 1))) *
        (Complex.exp ((freq i : ℂ) * ((n : ℂ) * Complex.I)) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (‖a i‖ * Real.exp (|freq i| * R)) * η := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul]
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (exponential_term_bound (freq i) R s hs) (norm_nonneg _)
      · exact (hp i).le
      · exact norm_nonneg _
      · positivity
    _ = C * η := by rw [← Finset.sum_mul]
    _ < ε := by
      have hηeq : η * (C + 1) = ε := by
        dsimp [η]
        exact div_mul_cancel₀ _ (by linarith)
      nlinarith

/-- A finite exponential polynomial with real frequencies and a zero at one
has a nonreal zero in Re(s)>1/2. No nontriviality assumption is needed:
local identically-zero behavior is handled directly. -/
theorem finiteExponentialPolynomial_nonreal_zero {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (freq : ι → ℝ)
    (hone : finiteExponentialPolynomial a freq 1 = 0) :
    ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ s.im ≠ 0 ∧
      finiteExponentialPolynomial a freq s = 0 := by
  let Q := finiteExponentialPolynomial a freq
  have hdiff : Differentiable ℂ Q := finiteExponentialPolynomial_differentiable a freq
  have hanalytic : AnalyticAt ℂ Q 1 :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr (Eventually.of_forall hdiff)
  rcases hanalytic.eventually_eq_zero_or_eventually_ne_zero with hlocal | hisolated
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hlocal
    let z : ℂ := 1 + ((ε / 2 : ℝ) : ℂ) * Complex.I
    have hz : z ∈ ball (1 : ℂ) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [z, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2)]
      linarith
    refine ⟨z, ?_, ?_, hball hz⟩
    · norm_num [z]
    · simp only [z, Complex.add_im, Complex.one_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
        mul_one, zero_mul, add_zero, zero_add]
      positivity
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hisolated
    let R : ℝ := min (ε / 2) (1 / 4)
    have hR : 0 < R := lt_min (by positivity) (by norm_num)
    have hRε : R < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hRquarter : R ≤ 1 / 4 := min_le_right _ _
    have hnonzero : ∀ z ∈ sphere (1 : ℂ) R, Q z ≠ 0 := by
      intro z hz
      have hdist : dist z (1 : ℂ) = R := hz
      apply hball
      refine ⟨?_, ?_⟩
      · change dist z (1 : ℂ) < ε
        rw [hdist]
        exact hRε
      · change z ∉ ({1} : Set ℂ)
        simp only [mem_singleton_iff]
        intro heq
        simp [heq] at hdist
        linarith
    have hne : (sphere (1 : ℂ) R).Nonempty := by
      refine ⟨1 + (R : ℂ), ?_⟩
      rw [Metric.mem_sphere, dist_eq_norm]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    obtain ⟨zmin, hzmin, hmin⟩ := (isCompact_sphere (1 : ℂ) R).exists_isMinOn hne
      hdiff.continuous.norm.continuousOn
    let δ : ℝ := ‖Q zmin‖
    have hδ : 0 < δ := norm_pos_iff.mpr (hnonzero zmin hzmin)
    have hboundary : ∀ z ∈ sphere (1 : ℂ) R, δ ≤ ‖Q z‖ := hmin
    obtain ⟨n, hn, hreturn⟩ := finiteExponentialPolynomial_vertical_return a freq R (δ / 2)
      (by positivity) 2
    let g : ℂ → ℂ := fun s => Q (s + (n : ℂ) * Complex.I)
    have hg : DiffContOnCl ℂ g (ball (1 : ℂ) R) := by
      apply Differentiable.diffContOnCl
      exact hdiff.comp (differentiable_id.add_const _)
    have herror : ∀ z ∈ sphere (1 : ℂ) R, ‖g z - Q z‖ < δ / 2 := by
      intro z hz
      exact hreturn z (le_of_eq (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz))
    have hcenter : ‖g 1‖ < δ / 2 := by
      have hh := hreturn 1 (by simpa using hR.le)
      simpa only [Q, hone, sub_zero] using hh
    obtain ⟨w, hw, hgw⟩ := exists_zero_in_ball_of_uniform_perturbation hR hδ hg
      hboundary herror hcenter
    have hnorm : ‖w - 1‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hre := Complex.abs_re_le_norm (w - 1)
    have him := Complex.abs_im_le_norm (w - 1)
    simp only [Complex.sub_re, Complex.one_re] at hre
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at him
    have hreb := (abs_le.mp hre).1
    have himb := (abs_le.mp him).1
    have hnR : (2 : ℝ) < n := by exact_mod_cast hn
    refine ⟨w + (n : ℂ) * Complex.I, ?_, ?_, hgw⟩
    · simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero]
      linarith
    · simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
      apply ne_of_gt
      linarith

end
end RiemannResearch.Analysis

import RiemannResearch.Analysis.ActualInghamGabrielDamping
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Tactic

/-!
# Actual strip regularity for Gabriel interpolation

The pole-removed Ingham error of Chourasiya and Simonič,
<https://arxiv.org/html/2507.15184v2>, Corollary 6, has a Gaussian envelope
uniform in each fixed closed strip to the right of the critical line.
The vertical moment profiles are uniformly continuous for every positive
real exponent. Schwarz reflection gives the exact equality of the two
height contributions. All three assertions concern the actual zeta function.
-/

noncomputable section
open Complex Complex.HadamardThreeLines Filter Set
open scoped Topology ComplexConjugate
namespace RiemannResearch.Analysis.InghamMollifier

private theorem nonzero_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) : s ≠ 0 := by
  rintro rfl
  norm_num at hs

theorem gabrielDampedError_diffContOnCl (X : ℕ) (b β : ℝ) :
    DiffContOnCl ℂ (gabrielDampedError X b) (verticalStrip (1/2) β) := by
  constructor
  · intro s hs
    exact (analyticAt_gabrielDampedError X b
      (nonzero_of_half_le_re hs.1.le)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hsub : closure (verticalStrip (1/2) β) ⊆ {z : ℂ | 1/2 ≤ z.re} :=
      closure_minimal (fun _ hz => hz.1.le) (isClosed_le continuous_const Complex.continuous_re)
    exact (analyticAt_gabrielDampedError X b
      (nonzero_of_half_le_re (hsub hs))).continuousAt.continuousWithinAt

/-- A single Gaussian decay bound for both tails at every abscissa of the strip. -/
theorem gabrielDampedError_high_strip (X : ℕ) {b β : ℝ} (hb : 0 < b)
    {z : ℂ} (hx : 1 / 2 ≤ z.re) (hxβ : z.re ≤ β) (hy : max 1 (X : ℝ) ≤ |z.im|) :
    ‖gabrielDampedError X b z‖ ≤ Real.exp (b*β^2) * (40/b) * Real.exp (-(b/2)*z.im^2) := by
  have hy1 : 1 ≤ |z.im| := (le_max_left _ _).trans hy
  have hyX : (X : ℝ) ≤ |z.im| := (le_max_right _ _).trans hy
  have hne : z ≠ 1 := by rintro rfl; norm_num at hy1
  have hraw := mollifiedError_norm_le_on_horizontal (X := X) hy1
    (by linarith : (X : ℝ) ≤ 2*|z.im|) hx hy1 (by linarith)
  rw [sq_abs] at hraw
  have hra : z.re^2 ≤ β^2 := sq_le_sq₀ (by linarith) (by linarith) |>.mpr hxβ
  have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hra hb.le)
  have he : 20*z.im^2 ≤ (40/b) * Real.exp ((b/2)*z.im^2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hb).mpr
    nlinarith [Real.add_one_le_exp ((b/2)*z.im^2)]
  calc
    _ ≤ Real.exp (b*z.re^2) * Real.exp (-b*z.im^2) * ‖mollifiedError X z‖ :=
      gabrielDampedError_gaussian_upper X b hne hx
    _ ≤ Real.exp (b*β^2) * Real.exp (-b*z.im^2) * ((40/b)*Real.exp ((b/2)*z.im^2)) := by
      gcongr
      exact hraw.trans he
    _ = Real.exp (b*β^2) * (40/b) * (Real.exp (-b*z.im^2) * Real.exp ((b/2)*z.im^2)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem gabrielDampedError_bounded_strip (X : ℕ) {b : ℝ} (hb : 0 < b) (β : ℝ) :
    ∃ C : ℝ, ∀ z ∈ verticalClosedStrip (1/2) β, ‖gabrielDampedError X b z‖ ≤ C := by
  let Y : ℝ := max 1 (X : ℝ)
  let K := (Icc (1/2 : ℝ) β) ×ˢ Icc (-Y) Y
  let f : ℝ × ℝ → ℝ := fun v => ‖gabrielDampedError X b ((v.1:ℂ)+(v.2:ℂ)*I)‖
  have hc : ContinuousOn f K := by
    intro v hv
    have hr : 1/2 ≤ ((v.1:ℂ)+(v.2:ℂ)*I).re := by simpa using hv.1.1
    let φ : ℝ × ℝ → ℂ := fun w => (w.1:ℂ)+(w.2:ℂ)*I
    have hφ : Continuous φ := by dsimp [φ]; fun_prop
    have ha : ContinuousAt (gabrielDampedError X b) (φ v) :=
      (analyticAt_gabrielDampedError X b (nonzero_of_half_le_re hr)).continuousAt
    exact (ha.comp hφ.continuousAt).norm.continuousWithinAt
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := (hcompact.image_of_continuousOn hc).bddAbove
  refine ⟨max C (Real.exp (b*β^2)*(40/b)), fun z hz => ?_⟩
  by_cases hy : |z.im| ≤ Y
  · have hmem : (z.re,z.im) ∈ K := ⟨hz, abs_le.mp hy⟩
    have hh := hC (Set.mem_image_of_mem f hmem)
    exact (show ‖gabrielDampedError X b z‖ ≤ C by simpa [f] using hh).trans (le_max_left _ _)
  · have hh := gabrielDampedError_high_strip X hb hz.1 hz.2 (le_of_not_ge hy)
    have he : Real.exp (-(b/2)*z.im^2) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
    exact (hh.trans (mul_le_of_le_one_right (by positivity) he)).trans (le_max_right _ _)

private theorem gabriel_line_tendsto_zero (X : ℕ) {b x : ℝ} (hb : 0 < b) (hx : 1 / 2 ≤ x) :
    Tendsto (fun t : ℝ => ‖gabrielDampedError X b ((x:ℂ)+(t:ℂ)*I)‖) (cocompact ℝ) (𝓝 0) := by
  have ha : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := tendsto_norm_cocompact_atTop
  have hs : Tendsto (fun t : ℝ => (b/2)*t^2) (cocompact ℝ) atTop := by
    have hh := (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp ha
    simpa only [Function.comp_def, sq_abs] using hh.const_mul_atTop (by linarith : 0 < b/2)
  have hlim : Tendsto (fun t : ℝ => Real.exp (-(b/2)*t^2)) (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  apply squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _)
    (g := fun t : ℝ => (Real.exp (b*x^2)*(40/b))*Real.exp (-(b/2)*t^2))
  · filter_upwards [ha.eventually_ge_atTop (max 1 (X:ℝ))] with t ht
    simpa using gabrielDampedError_high_strip (z := (x:ℂ)+(t:ℂ)*I) X hb
      (by simpa using hx) (β := x) (by simp) (by simpa using ht)
  · simpa using (tendsto_const_nhds (x := Real.exp (b*x^2)*(40/b))).mul hlim

theorem uniformContinuous_gabrielDampedError_norm_rpow (X : ℕ) {b x p : ℝ}
    (hb : 0 < b) (hx : 1/2 ≤ x) (hp : 0 < p) :
    UniformContinuous (fun t : ℝ => ‖gabrielDampedError X b ((x:ℂ)+(t:ℂ)*I)‖^p) := by
  have hc : Continuous (fun t : ℝ => ‖gabrielDampedError X b ((x:ℂ)+(t:ℂ)*I)‖) := by
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have hr : 1/2 ≤ ((x:ℂ)+(t:ℂ)*I).re := by simpa using hx
    let φ : ℝ → ℂ := fun u => (x:ℂ)+(u:ℂ)*I
    have hφ : Continuous φ := by dsimp [φ]; fun_prop
    have ha : ContinuousAt (gabrielDampedError X b) (φ t) :=
      (analyticAt_gabrielDampedError X b (nonzero_of_half_le_re hr)).continuousAt
    exact (ha.comp hφ.continuousAt).norm
  have hc' := hc.rpow_const (fun _ => Or.inr hp.le)
  apply hc'.uniformContinuous_of_tendsto_cocompact
  exact (gabriel_line_tendsto_zero X hb hx).rpow_const (Or.inr hp.le)

private theorem mollifier_conjugate (X : ℕ) (s : ℂ) :
    mollifier X (conj s) = conj (mollifier X s) := by
  unfold mollifier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_mul, map_intCast, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]

theorem norm_mollifiedError_vertical_neg (X : ℕ) (x t : ℝ) :
    ‖mollifiedError X ((x:ℂ)+((-t:ℝ):ℂ)*I)‖ = ‖mollifiedError X ((x:ℂ)+(t:ℂ)*I)‖ := by
  let z : ℂ := (x:ℂ)+(t:ℂ)*I
  have hconj : (x:ℂ)+((-t:ℝ):ℂ)*I = conj z := by simp [z]
  by_cases hz : z = 1
  · have ht : t = 0 := by simpa [z] using congrArg Complex.im hz
    simp [ht]
  · rw [hconj]
    change ‖riemannZeta (conj z) * mollifier X (conj z) - 1‖ =
      ‖riemannZeta z * mollifier X z - 1‖
    rw [Zeta23.riemannZeta_conj hz, mollifier_conjugate]
    simpa using Complex.norm_conj (riemannZeta z * mollifier X z - 1)

theorem norm_gabrielDampedError_vertical_neg (X : ℕ) (b x t : ℝ) :
    ‖gabrielDampedError X b ((x:ℂ)+((-t:ℝ):ℂ)*I)‖ =
      ‖gabrielDampedError X b ((x:ℂ)+(t:ℂ)*I)‖ := by
  by_cases ht : t = 0
  · simp [ht]
  · have hs : (x:ℂ)+(t:ℂ)*I ≠ 1 := fun h => ht (by simpa using congrArg Complex.im h)
    have hs' : (x:ℂ)+((-t:ℝ):ℂ)*I ≠ 1 := by
      intro h
      apply ht
      simpa using congrArg Complex.im h
    rw [norm_gabrielDampedError X b hs', norm_gabrielDampedError X b hs,
      norm_mollifiedError_vertical_neg]
    have he : (x:ℂ)+((-t:ℝ):ℂ)*I = conj ((x:ℂ)+(t:ℂ)*I) := by simp
    simp only [he, Complex.conj_re, Complex.conj_im, neg_sq]
    congr 2
    simpa using Complex.norm_conj ((((x:ℂ)+(t:ℂ)*I)-1)/((x:ℂ)+(t:ℂ)*I))

end RiemannResearch.Analysis.InghamMollifier

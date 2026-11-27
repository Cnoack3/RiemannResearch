import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.RH.ParetoResidueSineLimit
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # The prime-power Fourier kernel and its sine determinants

The finite arithmetic measure has masses Λ(n)/(n log T) at log(n)/log T.
Its Fourier transform on differences is a positive Gram kernel. Centering
its frequency axis at 1/2 multiplies each entry by exp(−πi(x−y)), preserving
all finite determinants. Mertens' estimate gives the entrywise sine limit and
therefore the sine determinants of every fixed order.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ComplexOrder Matrix

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open RiemannResearch.RH.Pareto.SpectralObstruction

/-- Fourier kernel of the unnormalized finite prime-power measure. -/
def primeProbeKernel (T x y : ℝ) : ℂ := primeFourierProbe T (x-y)

/-- Translating the log-frequency variable by −1/2 centers its transform. -/
def centeredPrimeProbeKernel (T x y : ℝ) : ℂ :=
  Complex.exp (((-(Real.pi*(x-y)) : ℝ) : ℂ) * Complex.I) * primeProbeKernel T x y

/-- The exponential gauge has modulus one at every frequency difference. -/
theorem norm_primeProbe_centering_phase (x y : ℝ) :
    ‖Complex.exp (((-(Real.pi*(x-y)) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem primeContinuumProbe_centered (u : ℝ) :
    Complex.exp (((-(Real.pi*u) : ℝ) : ℂ) * Complex.I) * primeContinuumProbe u =
      (Real.sinc (Real.pi*u) : ℂ) := by
  rw [primeContinuumProbe_eq, logPhaseKernel, ← mul_assoc, ← Complex.exp_add,
    show -(2*Real.pi*u)/2 = -(Real.pi*u) by ring, Real.sinc_neg]
  have hz : (((-(Real.pi*u) : ℝ) : ℂ) * Complex.I) +
      (-(((-(2*Real.pi*u) : ℝ) : ℂ)/2) * Complex.I) = 0 := by push_cast; ring
  rw [hz, Complex.exp_zero, one_mul]

/-- One estimate controls every finite-height centered entry, including the
diagonal. It is uniform on every bounded interval of differences. -/
theorem centeredPrimeProbeKernel_error {T : ℝ} (hT : 1 < T) (x y : ℝ) :
    ‖centeredPrimeProbeKernel T x y - (Real.sinc (Real.pi*(x-y)) : ℂ)‖ ≤
      ((Real.log 4 + 4)/Real.log T) * (1 + 2*Real.pi*|x-y|) := by
  rw [← primeContinuumProbe_centered (x-y), centeredPrimeProbeKernel, ← mul_sub,
    norm_mul, norm_primeProbe_centering_phase, one_mul]
  exact primeFourierProbe_error hT (x-y)

theorem centeredPrimeProbeKernel_tendsto (x y : ℝ) :
    Tendsto (fun T => centeredPrimeProbeKernel T x y) atTop
      (𝓝 (Real.sinc (Real.pi*(x-y)) : ℂ)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact centeredPrimeProbeKernel_error hT x y
  · simpa using (Real.tendsto_log_atTop.const_div_atTop (Real.log 4+4)).mul_const
      (1+2*Real.pi*|x-y|)

/-- The centered arithmetic kernel tracks its sine entry on every moving
difference of size o(log T). The common translation of the coordinates
may grow at any rate. -/
theorem centeredPrimeProbeKernel_moving_sub_sine {x y : ℝ → ℝ}
    (hgap : Tendsto (fun T => |x T-y T|/Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => centeredPrimeProbeKernel T (x T) (y T) -
      (Real.sinc (Real.pi*(x T-y T)) : ℂ)) atTop (𝓝 0) := by
  let C := Real.log 4 + 4
  have he : Tendsto (fun T : ℝ => C/Real.log T + (C*(2*Real.pi))*(|x T-y T|/Real.log T))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_log_atTop.const_div_atTop C).add (hgap.const_mul (C*(2*Real.pi)))
  apply squeeze_zero_norm' _ he
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  calc
    _ ≤ (C/Real.log T) * (1+2*Real.pi*|x T-y T|) :=
      centeredPrimeProbeKernel_error hT _ _
    _ = _ := by ring

/-- At a diverging sublogarithmic separation the centered prime entries vanish. -/
theorem centeredPrimeProbeKernel_moving_tendsto_zero {x y : ℝ → ℝ}
    (hgap : Tendsto (fun T => |x T-y T|/Real.log T) atTop (𝓝 0))
    (hdiv : Tendsto (fun T => |x T-y T|) atTop atTop) :
    Tendsto (fun T => centeredPrimeProbeKernel T (x T) (y T)) atTop (𝓝 0) := by
  have hs : Tendsto (fun T => (Real.sinc (Real.pi*(x T-y T)) : ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun T => (1/Real.pi) * (|x T-y T|)⁻¹)
    · filter_upwards [hdiv.eventually (eventually_gt_atTop (0:ℝ))] with T ht
      have hd : x T-y T ≠ 0 := abs_pos.mp ht
      rw [Complex.norm_real, Real.norm_eq_abs, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hd),
        abs_div, abs_mul, abs_of_pos Real.pi_pos]
      calc
        _ ≤ 1/(Real.pi*|x T-y T|) :=
          div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
        _ = _ := by simp [div_eq_mul_inv, mul_comm]
    · simpa using (tendsto_inv_atTop_zero.comp hdiv).const_mul (1/Real.pi)
  simpa only [sub_add_cancel, add_zero] using (centeredPrimeProbeKernel_moving_sub_sine hgap).add hs

private theorem rawProbeEntry_from_centered (T x y : ℝ) :
    primeProbeKernel T x y = Complex.exp (((Real.pi*(x-y) : ℝ) : ℂ)*Complex.I) *
        centeredPrimeProbeKernel T x y := by
  unfold centeredPrimeProbeKernel
  rw [← mul_assoc, ← Complex.exp_add, Complex.ofReal_neg, neg_mul, add_neg_cancel,
    Complex.exp_zero, one_mul]

/-- The raw kernel has the positive half-interval phase in the limit. -/
theorem primeProbeKernel_tendsto (x y : ℝ) :
    Tendsto (fun T => primeProbeKernel T x y) atTop
      (𝓝 (Complex.exp (((Real.pi*(x-y) : ℝ) : ℂ)*Complex.I) *
        (Real.sinc (Real.pi*(x-y)) : ℂ))) := by
  simpa only [rawProbeEntry_from_centered] using
    (centeredPrimeProbeKernel_tendsto x y).const_mul
      (Complex.exp (((Real.pi*(x-y) : ℝ) : ℂ)*Complex.I))

/-- The raw finite mass tends to one at the origin. -/
theorem primeProbeKernel_mass_tendsto_one :
    Tendsto (fun T : ℝ => primeFourierProbe T 0) atTop (𝓝 1) := by
  simpa [primeProbeKernel] using primeProbeKernel_tendsto 0 0

/-- The centered and raw determinants agree at every finite cutoff. -/
theorem centeredPrimeProbeKernel_det_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ℝ) (x : ι → ℝ) :
    Matrix.det (fun i j => centeredPrimeProbeKernel T (x i) (x j)) =
      Matrix.det (fun i j => primeProbeKernel T (x i) (x j)) := by
  let a (i : ι) := Complex.exp (((-(Real.pi*x i) : ℝ) : ℂ)*Complex.I)
  let b (i : ι) := Complex.exp (((Real.pi*x i : ℝ) : ℂ)*Complex.I)
  let K : Matrix ι ι ℂ := fun i j => primeProbeKernel T (x i) (x j)
  have hab (i : ι) : a i * b i = 1 := by
    dsimp only [a,b]
    rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul, neg_add_cancel, Complex.exp_zero]
  have hmatrix : (fun i j => centeredPrimeProbeKernel T (x i) (x j)) =
      Matrix.of (fun i j => a i * (Matrix.of (fun k l => b l * K k l)) i j) := by
    funext i j
    change _ = a i * (b j * K i j)
    dsimp only [a,b,K,centeredPrimeProbeKernel]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmatrix, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc,
    ← Finset.prod_mul_distrib]
  simp only [hab, Finset.prod_const_one, one_mul]
  rfl

/-- All finite prime-kernel determinants converge to the sine determinants.
Points may coincide and the tuple can have any finite cardinality. -/
theorem primeProbeKernel_det_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    Tendsto (fun T => Matrix.det (fun i j => primeProbeKernel T (x i) (x j))) atTop
      (𝓝 (Matrix.det (fun i j => (Real.sinc (Real.pi*(x i-x j)) : ℂ)))) := by
  have hentry : Tendsto (fun T i j => centeredPrimeProbeKernel T (x i) (x j)) atTop
      (𝓝 (fun i j => (Real.sinc (Real.pi*(x i-x j)) : ℂ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
      centeredPrimeProbeKernel_tendsto (x i) (x j)
  have hd : Tendsto (fun T => Matrix.det (fun i j => centeredPrimeProbeKernel T (x i) (x j)))
      atTop (𝓝 (Matrix.det (fun i j => (Real.sinc (Real.pi*(x i-x j)) : ℂ)))) :=
    (continuous_id.matrix_det.tendsto _).comp hentry
  simpa only [centeredPrimeProbeKernel_det_eq] using hd

/-- A feature for each log-frequency atom, weighted by its square-root mass. -/
def primeProbeFeature (T x : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (ArithmeticFunction.vonMangoldt n/(n:ℝ)/Real.log T) : ℂ) *
    Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log n/Real.log T : ℝ) : ℂ))

/-- Exact finite Gram expansion in the individual prime-power atoms. -/
theorem primeProbeKernel_eq_feature_sum {T : ℝ} (hT : 1 < T) (x y : ℝ) :
    primeProbeKernel T x y = ∑ n ∈ Finset.Ioc 0 ⌊T⌋₊,
      primeProbeFeature T x n * star (primeProbeFeature T y n) := by
  unfold primeProbeKernel primeFourierProbe
  apply Finset.sum_congr rfl
  intro n _
  let w := ArithmeticFunction.vonMangoldt n/(n:ℝ)/Real.log T
  let d := (Real.log n/Real.log T : ℝ)
  let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I*(d:ℂ))
  have hw : 0 ≤ w := div_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)) (Real.log_pos hT).le
  have hes (u v : ℝ) : e u * star (e v) = e (u-v) := by
    dsimp only [e]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, map_mul,
      Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change (w:ℂ) * e (x-y) = ((Real.sqrt w : ℂ)*e x) * star ((Real.sqrt w : ℂ)*e y)
  rw [star_mul, show star (Real.sqrt w : ℂ) = (Real.sqrt w : ℂ) by simp]
  calc
    _ = ((Real.sqrt w : ℂ)*(Real.sqrt w : ℂ)) * (e x * star (e y)) := by
      rw [hes, ← Complex.ofReal_mul, Real.mul_self_sqrt hw]
    _ = _ := by ring

/-- Each finite tuple yields a positive semidefinite complex Gram matrix. -/
theorem primeProbeKernel_posSemidef {ι : Type*} [Fintype ι] {T : ℝ}
    (hT : 1 < T) (x : ι → ℝ) :
    (Matrix.of (fun i j => primeProbeKernel T (x i) (x j))).PosSemidef := by
  classical
  let s := Finset.Ioc 0 ⌊T⌋₊
  let F : Matrix ι s ℂ := fun i n => primeProbeFeature T (x i) n.val
  have hgram : Matrix.of (fun i j => primeProbeKernel T (x i) (x j)) = F * Fᴴ := by
    ext i j
    rw [Matrix.of_apply, primeProbeKernel_eq_feature_sum hT, Matrix.mul_apply]
    change (∑ n ∈ s, primeProbeFeature T (x i) n * star (primeProbeFeature T (x j) n)) =
      ∑ n : s, primeProbeFeature T (x i) n.val * star (primeProbeFeature T (x j) n.val)
    exact (Finset.sum_attach s _).symm
  rw [hgram]
  exact Matrix.posSemidef_self_mul_conjTranspose F

/-- The finite two-point determinant is mass squared minus the squared modulus
of the off-diagonal probe, also when the two coordinates agree. -/
theorem primeProbeKernel_det_two {T : ℝ} (hT : 1 < T) (x : Fin 2 → ℝ) :
    Matrix.det (fun i j => primeProbeKernel T (x i) (x j)) =
      (primeFourierProbe T 0)^2 - (Complex.normSq (primeFourierProbe T (x 0-x 1)) : ℂ) := by
  have hflip : primeProbeKernel T (x 1) (x 0) = star (primeProbeKernel T (x 0) (x 1)) := by
    rw [primeProbeKernel_eq_feature_sum hT, primeProbeKernel_eq_feature_sum hT]
    simp only [star_sum, star_mul, star_star]
  change (Matrix.of (fun i j => primeProbeKernel T (x i) (x j))).det = _
  rw [Matrix.det_fin_two]
  change primeProbeKernel T (x 0) (x 0) * primeProbeKernel T (x 1) (x 1) -
      primeProbeKernel T (x 0) (x 1) * primeProbeKernel T (x 1) (x 0) = _
  rw [hflip, Complex.star_def, Complex.mul_conj]
  simp [primeProbeKernel, pow_two]

end RiemannResearch.Analysis.MontgomeryPrimeTrace

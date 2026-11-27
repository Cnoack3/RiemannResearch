import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Fixed Fourier tests can miss microscopic excess in a pair density

On the circle take the probability density pₙ(x)=1+cos(2πnx), n≥1. Each
fixed Fourier coefficient eventually equals its Haar counterpart. The two
moving modes retain half a unit of off-origin Fourier energy. The physical
autocorrelation is exactly 1+cos(2πnx)/2. At separation u/n its profile
therefore stays 1+cos(2πu)/2 for every n. This is a model for the
quantifier issue when comparing a fixed Fourier law with microscopic pairs.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators Real

namespace RiemannResearch.Analysis.MontgomeryFixedModesEscape

local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
private abbrev X := AddCircle (1:ℝ)

/-- Real trigonometric polynomial, viewed as a complex function for Fourier
analysis. The parameter a controls the amplitude. -/
def wave (a : ℝ) (n : ℤ) (x : AddCircle (1:ℝ)) : ℂ :=
  fourier 0 x + ((a/2 : ℝ):ℂ)*(fourier n x + fourier (-n) x)

theorem wave_eq_real (a : ℝ) (n : ℤ) (x : X) :
    wave a n x = ((1+a*(fourier n x).re : ℝ):ℂ) := by
  unfold wave
  rw [fourier_zero, fourier_neg]
  apply Complex.ext <;> simp [Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im]
  ring

private theorem integrable_fourier (n : ℤ) :
    Integrable (fourier (T:=1) n) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem wave_coefficient (a : ℝ) (n k : ℤ) :
    fourierCoeff (wave a n) k = (if k=0 then 1 else 0) + ((a/2 : ℝ):ℂ) *
      ((if k=n then 1 else 0) + (if k= -n then 1 else 0)) := by
  let u (j : ℤ) : X → ℂ := fourier j
  have hc (j : ℤ) : fourierCoeff (u j) k = if k=j then 1 else 0 := by
    simpa only [u, Pi.single_apply] using congrFun (fourierCoeff_fourier (T:=1) j) k
  have hi (j : ℤ) : Integrable (u j) AddCircle.haarAddCircle := integrable_fourier j
  have he : wave a n = u 0 + fun x => ((a/2 : ℝ):ℂ) * ((u n + u (-n)) x) := rfl
  rw [he, fourierCoeff.add (hi 0) (((hi n).add (hi (-n))).const_mul _)]
  change fourierCoeff (u 0) k + fourierCoeff (fun x => ((a/2:ℝ):ℂ)*((u n + u (-n)) x)) k = _
  rw [fourierCoeff.const_mul, fourierCoeff.add (hi n) (hi (-n))]
  simp only [Pi.add_apply, hc]

/-- Nonnegative real density of mass one at each positive frequency. -/
theorem wave_probability {n : ℤ} (hn : 0 < n) :
    (∀ x : X, 0 ≤ (wave 1 n x).re) ∧ (∫ x, wave 1 n x ∂AddCircle.haarAddCircle) = 1 := by
  constructor
  · intro x
    rw [wave_eq_real]
    have hnorm : ‖fourier n x‖ = 1 := by rw [fourier_apply, Circle.norm_coe]
    have h := (abs_le.mp ((Complex.abs_re_le_norm (fourier n x)).trans hnorm.le)).1
    simp only [Complex.ofReal_re, one_mul]
    linarith
  · have h := wave_coefficient 1 n 0
    simpa [fourierCoeff, fourier_zero, hn.ne, hn.ne', -fourier_apply] using h

/-- Every finite collection of fixed modes eventually agrees exactly with
the constant Haar density. This includes their squared intensities. -/
theorem eventually_fixed_modes (S : Finset ℤ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ S, fourierCoeff (wave 1 (N:ℤ)) k =
      (if k=0 then 1 else 0) := by
  apply (Filter.eventually_all_finset S).2
  intro k _
  filter_upwards [eventually_gt_atTop k.natAbs] with N hN
  have hne : k ≠ (N:ℤ) := by omega
  have hne' : k ≠ -(N:ℤ) := by omega
  simp [wave_coefficient, hne, hne']

/-- The full nonconstant Fourier energy is independent of n. -/
theorem exact_offorigin_fourier_energy {n : ℤ} (hn : 0 < n) :
    (∑' k : ℤ, if k=0 then (0:ℝ) else Complex.normSq (fourierCoeff (wave 1 n) k)) = 1/2 := by
  classical
  let e (k : ℤ) := if k=0 then (0:ℝ) else Complex.normSq (fourierCoeff (wave 1 n) k)
  have he : ∀ k, k ∉ ({n,-n} : Finset ℤ) → e k = 0 := by
    intro k hk
    have hne : k ≠ n ∧ k ≠ -n := by simpa using hk
    by_cases h0 : k=0 <;> simp [e, h0, wave_coefficient, hne.1, hne.2]
  rw [tsum_eq_sum he]
  have hne : n ≠ -n := by omega
  have hne' : -n ≠ n := Ne.symm hne
  have h0 : -n ≠ 0 := neg_ne_zero.mpr hn.ne'
  simp [e, Finset.sum_pair hne, wave_coefficient, hn.ne', h0, hne, hne']
  norm_num [Complex.normSq]

/-- Outside any fixed finite list containing the origin the Fourier tail
eventually has exactly half a unit of energy. -/
theorem eventually_fixed_cutoff_tail (S : Finset ℤ) (h0 : (0:ℤ) ∈ S) :
    ∀ᶠ N : ℕ in atTop, (∑' k : ℤ, if k ∈ S then (0:ℝ) else
      Complex.normSq (fourierCoeff (wave 1 (N:ℤ)) k)) = 1/2 := by
  filter_upwards [eventually_fixed_modes S, eventually_gt_atTop (0:ℕ)] with N hS hN
  rw [← exact_offorigin_fourier_energy (n := (N:ℤ)) (by exact_mod_cast hN)]
  apply tsum_congr
  intro k
  by_cases h : k ∈ S
  · rw [if_pos h, hS _ h]
    split_ifs <;> simp_all
  · have hk : k ≠ 0 := fun e => h (e.symm ▸ h0)
    simp [h, hk]

private theorem character_translate (k : ℤ) (t x : X) :
    fourier k (t+x) = fourier k t * fourier k x := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The Haar autocorrelation of the density is the density of the difference
between two independent samples. The equalities hold at every separation. -/
theorem wave_autocorrelation {n : ℤ} (hn : 0 < n) (x : X) :
    (∫ t : X, wave 1 n t * wave 1 n (t+x) ∂AddCircle.haarAddCircle) =
      wave (1/2) n x := by
  let p := wave 1 n
  let A (k : ℤ) (t : X) := fourier k t * p t
  have hp : Integrable p AddCircle.haarAddCircle := (integrable_fourier 0).add
    (((integrable_fourier n).add (integrable_fourier (-n))).const_mul _)
  have hA (k : ℤ) : Integrable (A k) AddCircle.haarAddCircle := hp.fourier_smul k
  have hco (k : ℤ) : (∫ t, A k t ∂AddCircle.haarAddCircle) = fourierCoeff p (-k) := by
    simp only [A, fourierCoeff, neg_neg, smul_eq_mul]
  have h0 (t : X) : p t * p (t+x) = A 0 t +
      (fourier n x/2) * A n t + (fourier (-n) x/2) * A (-n) t := by
    change p t * wave 1 n (t+x) = _
    rw [wave, fourier_zero, character_translate, character_translate]
    simp only [A, fourier_zero, one_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  change (∫ t, p t * p (t+x) ∂AddCircle.haarAddCircle) = _
  simp_rw [h0]
  have hab : Integrable (fun t => A 0 t + (fourier n x/2)*A n t) AddCircle.haarAddCircle :=
    (hA 0).add ((hA n).const_mul _)
  rw [integral_add hab ((hA (-n)).const_mul _),
    integral_add (hA 0) ((hA n).const_mul _), integral_const_mul, integral_const_mul,
    hco, hco, hco]
  have hne : n ≠ -n := by omega
  simp [p, wave_coefficient, wave, hn.ne, hn.ne', hne, hne.symm, fourier_zero,
    -fourier_apply]
  ring

/-- Microscopic separation u/n keeps a nonconstant correlation profile even
though all fixed Fourier observables eventually equal their Haar values. -/
theorem microscopic_profile {n : ℤ} (hn : 0 < n) (u : ℝ) :
    (∫ t : X, wave 1 n t * wave 1 n (t + ((u/(n:ℝ) : ℝ) : X))
      ∂AddCircle.haarAddCircle).re = 1 + Real.cos (2*Real.pi*u)/2 := by
  rw [wave_autocorrelation hn, wave_eq_real, Complex.ofReal_re, fourier_coe_apply]
  have hn' : (n:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn.ne'
  rw [show 2 * (Real.pi:ℂ) * Complex.I * n * ((u/(n:ℝ) : ℝ):ℂ) / (1:ℝ) =
        ((2*Real.pi*u : ℝ):ℂ) * Complex.I by push_cast; field_simp,
    Complex.exp_ofReal_mul_I_re]
  ring

/-- The excess survives integration over a microscopic gap window. At width
q=1/4 the normalized excess over Haar is 1/(4π), at every positive n. -/
theorem microscopic_window_mass {n : ℤ} (hn : 0 < n) (q : ℝ) :
    (∫ u in (0:ℝ)..q, (∫ t : X, wave 1 n t * wave 1 n (t + ((u/(n:ℝ) : ℝ) : X))
      ∂AddCircle.haarAddCircle).re) = q + Real.sin (2*Real.pi*q)/(4*Real.pi) := by
  simp_rw [microscopic_profile hn]
  rw [intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left Real.cos (by positivity : (2*Real.pi:ℝ) ≠ 0),
    integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, mul_one]
  ring

end RiemannResearch.Analysis.MontgomeryFixedModesEscape

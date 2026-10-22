import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebra of twisted arithmetic Riesz filters

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

These declarations prove the finite algebra behind the prime-side filter
`sum Λ(n) n^(-iτ) (1-n/x)^2` and its full-zero sensitivity. They do not assert
an explicit formula, a Mellin continuation, RH, or a zero-energy estimate.
The analytic providers for those statements remain separate and open.

The spectral kernel calculation is a direct partial-fraction calculation.
The exponential expression below is only the proposed Fourier multiplier;
its positivity is proved, while identifying it as a Fourier integral is a
separate analytic obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.TwistedRieszFilter

/-- The denominator of a general finite-order Riesz multiplier. -/
def denominator (r : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range (r + 1), (z + (j : ℂ))

/-- Every factor has positive real part in the positive half-plane. -/
theorem shift_ne_zero {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    z + (j : ℂ) ≠ 0 := by
  have hp : 0 < (z + (j : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  intro h
  rw [h] at hp
  norm_num at hp

/-- No fixed finite Riesz order erases a full zero in the positive half-plane. -/
theorem denominator_ne_zero {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    denominator r z ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact shift_ne_zero hz j

def multiplier (r : ℕ) (z : ℂ) : ℂ :=
  (r.factorial : ℂ) / denominator r z

theorem multiplier_ne_zero {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    multiplier r z ≠ 0 := by
  apply div_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero r
  · exact denominator_ne_zero hz r

def denominatorTwo (z : ℂ) : ℂ := z * (z + 1) * (z + 2)

def multiplierTwo (z : ℂ) : ℂ := 2 / denominatorTwo z

def twistedMultiplierTwo (z : ℂ) (τ : ℝ) : ℂ :=
  multiplierTwo (z - (τ : ℂ) * Complex.I)

theorem denominatorTwo_ne_zero {z : ℂ} (hz : 0 < z.re) :
    denominatorTwo z ≠ 0 := by
  unfold denominatorTwo
  exact mul_ne_zero (mul_ne_zero (by simpa using shift_ne_zero hz 0)
    (by simpa using shift_ne_zero hz 1))
    (by simpa using shift_ne_zero hz 2)

theorem multiplierTwo_ne_zero {z : ℂ} (hz : 0 < z.re) :
    multiplierTwo z ≠ 0 := by
  exact div_ne_zero (by norm_num) (denominatorTwo_ne_zero hz)

/-- Subtracting the actual ordinate moves a full zero to its real part. -/
theorem shift_ordinate_eq_real (z : ℂ) :
    z - (z.im : ℂ) * Complex.I = (z.re : ℂ) := by
  apply Complex.ext <;> simp

theorem twistedMultiplierTwo_ne_zero {z : ℂ} (hz : 0 < z.re) (τ : ℝ) :
    twistedMultiplierTwo z τ ≠ 0 := by
  apply multiplierTwo_ne_zero
  simpa using hz

def realAmplitudeTwo (β : ℝ) : ℝ := 2 / (β * (β + 1) * (β + 2))

theorem peak_multiplier_eq_real (z : ℂ) :
    twistedMultiplierTwo z z.im = (realAmplitudeTwo z.re : ℂ) := by
  rw [twistedMultiplierTwo, shift_ordinate_eq_real]
  unfold multiplierTwo denominatorTwo realAmplitudeTwo
  push_cast <;> rfl

theorem real_denominator_pos {β : ℝ} (hβ : 0 < β) :
    0 < β * (β + 1) * (β + 2) := by positivity

/-- Uniform residue amplitude after centering the zero's actual ordinate. -/
theorem realAmplitudeTwo_bounds {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (hβ' : β ≤ 1) :
    (1 / 3 : ℝ) ≤ realAmplitudeTwo β ∧
      realAmplitudeTwo β ≤ (16 / 15 : ℝ) := by
  have hb : 0 < β := by linarith
  have hd := real_denominator_pos hb
  have hlower : (15 / 8 : ℝ) ≤ β * (β + 1) * (β + 2) := by
    have h := mul_nonneg (show 0 ≤ β - 1 / 2 by linarith)
      (show 0 ≤ β ^ 2 + (7 / 2) * β + 15 / 4 by positivity)
    nlinarith
  have hupper : β * (β + 1) * (β + 2) ≤ 6 := by
    have h := mul_nonneg (show 0 ≤ 1 - β by linarith)
      (show 0 ≤ β ^ 2 + 4 * β + 6 by positivity)
    nlinarith
  unfold realAmplitudeTwo
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

theorem realAmplitudeTwo_half : realAmplitudeTwo (1 / 2) = 16 / 15 := by
  norm_num [realAmplitudeTwo]

theorem realAmplitudeTwo_one : realAmplitudeTwo 1 = 1 / 3 := by
  norm_num [realAmplitudeTwo]

/-- The true multiplicity is retained in the squared residue amplitude. -/
theorem squared_residue_bounds {β m : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (hβ' : β ≤ 1) (hm : 0 ≤ m) :
    m ^ 2 / 9 ≤ (m * realAmplitudeTwo β) ^ 2 ∧
      (m * realAmplitudeTwo β) ^ 2 ≤ (256 / 225 : ℝ) * m ^ 2 := by
  obtain ⟨hl, hu⟩ := realAmplitudeTwo_bounds hβ hβ'
  have hlow : m / 3 ≤ m * realAmplitudeTwo β := by
    have h := mul_le_mul_of_nonneg_left hl hm
    nlinarith
  have hhigh : m * realAmplitudeTwo β ≤ (16 / 15 : ℝ) * m := by
    have h := mul_le_mul_of_nonneg_left hu hm
    nlinarith
  have hn : 0 ≤ m * realAmplitudeTwo β :=
    mul_nonneg hm (le_trans (by norm_num) hl)
  constructor
  · have hp := mul_nonneg (show 0 ≤ m * realAmplitudeTwo β - m / 3 by linarith)
      (show 0 ≤ m * realAmplitudeTwo β + m / 3 by positivity)
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ (16 / 15 : ℝ) * m - m * realAmplitudeTwo β by linarith)
      (show 0 ≤ (16 / 15 : ℝ) * m + m * realAmplitudeTwo β by positivity)
    nlinarith

def spectralKernelTwo (β t : ℝ) : ℝ :=
  4 / ((β ^ 2 + t ^ 2) * ((β + 1) ^ 2 + t ^ 2) *
    ((β + 2) ^ 2 + t ^ 2))

def criticalSpectralKernel (t : ℝ) : ℝ :=
  4 / ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4) * (t ^ 2 + 25 / 4))

theorem spectralKernelTwo_pos {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    0 < spectralKernelTwo β t := by
  unfold spectralKernelTwo
  positivity

theorem spectralKernelTwo_half (t : ℝ) :
    spectralKernelTwo (1 / 2) t = criticalSpectralKernel t := by
  norm_num [spectralKernelTwo, criticalSpectralKernel, add_comm]

theorem normSq_multiplierTwo_shift (β t : ℝ) :
    Complex.normSq (multiplierTwo ((β : ℂ) + (t : ℂ) * Complex.I)) =
      spectralKernelTwo β t := by
  have h0 : Complex.normSq ((β : ℂ) + (t : ℂ) * Complex.I) = β ^ 2 + t ^ 2 :=
    Complex.normSq_add_mul_I β t
  have h1 : Complex.normSq (((β : ℂ) + (t : ℂ) * Complex.I) + 1) =
      (β + 1) ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, pow_two] <;> ring
  have h2 : Complex.normSq (((β : ℂ) + (t : ℂ) * Complex.I) + 2) =
      (β + 2) ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, pow_two] <;> ring
  unfold multiplierTwo denominatorTwo spectralKernelTwo
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, h0, h1, h2]
  norm_num

theorem criticalSpectralKernel_peak :
    criticalSpectralKernel 0 = 256 / 225 := by
  norm_num [criticalSpectralKernel]

/-- Exact rational partial fractions; signs are retained. -/
theorem criticalSpectralKernel_partialFractions (t : ℝ) :
    criticalSpectralKernel t =
      1 / (3 * (t ^ 2 + 1 / 4)) -
      1 / (2 * (t ^ 2 + 9 / 4)) +
      1 / (6 * (t ^ 2 + 25 / 4)) := by
  have h1 : t ^ 2 + (1 / 4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have h2 : t ^ 2 + (9 / 4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have h3 : t ^ 2 + (25 / 4 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  unfold criticalSpectralKernel
  field_simp [h1, h2, h3]
  <;> ring

/-- The rational quadratic is positive even outside the exponential range. -/
theorem fourier_quadratic_lower (z : ℝ) :
    (15 / 4 : ℝ) ≤ 10 - 5 * z + z ^ 2 := by
  nlinarith [sq_nonneg (z - 5 / 2)]

theorem fourier_quadratic_bounds {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    6 ≤ 10 - 5 * z + z ^ 2 ∧ 10 - 5 * z + z ^ 2 ≤ 10 := by
  have h := mul_nonneg (show 0 ≤ 1 - z by linarith)
    (show 0 ≤ 4 - z by linarith)
  have h' := mul_nonneg hz (show 0 ≤ 1 - z by linarith)
  constructor <;> nlinarith

/-- Proposed Fourier multiplier. The Fourier integral identity is separate. -/
def proposedFourierFactor (u : ℝ) : ℝ :=
  (Real.pi / 15) * Real.exp (-|u| / 2) *
    (10 - 5 * Real.exp (-|u|) + (Real.exp (-|u|)) ^ 2)

theorem proposedFourierFactor_pos (u : ℝ) : 0 < proposedFourierFactor u := by
  have hq := fourier_quadratic_lower (Real.exp (-|u|))
  have hqp : 0 < 10 - 5 * Real.exp (-|u|) + (Real.exp (-|u|)) ^ 2 := by
    linarith
  unfold proposedFourierFactor
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _)) hqp

/-- A sharp positive envelope, strengthening mere nonvanishing. -/
theorem proposedFourierFactor_bounds (u : ℝ) :
    (2 * Real.pi / 5) * Real.exp (-|u| / 2) ≤ proposedFourierFactor u ∧
      proposedFourierFactor u ≤ (2 * Real.pi / 3) * Real.exp (-|u| / 2) := by
  have hz : 0 ≤ Real.exp (-|u|) := (Real.exp_pos _).le
  have hz' : Real.exp (-|u|) ≤ 1 := by
    calc
      Real.exp (-|u|) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by simp)
      _ = 1 := Real.exp_zero
  obtain ⟨hl, hu⟩ := fourier_quadratic_bounds hz hz'
  have hp : 0 < (Real.pi / 15) * Real.exp (-|u| / 2) := by positivity
  have hlo := mul_le_mul_of_nonneg_left hl hp.le
  have hup := mul_le_mul_of_nonneg_left hu hp.le
  unfold proposedFourierFactor
  constructor <;> nlinarith

/-- Pointwise factor-two energy transfer retains the complete difference. -/
theorem square_energy_transfer (a b : ℝ) :
    a ^ 2 ≤ 2 * b ^ 2 + 2 * (a - b) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b)]

theorem sum_square_energy_transfer {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) :
    (∑ i ∈ s, a i ^ 2) ≤
      2 * (∑ i ∈ s, b i ^ 2) + 2 * (∑ i ∈ s, (a i - b i) ^ 2) := by
  calc
    (∑ i ∈ s, a i ^ 2) ≤ ∑ i ∈ s, (2 * b i ^ 2 + 2 * (a i - b i) ^ 2) :=
      Finset.sum_le_sum (fun i hi => square_energy_transfer (a i) (b i))
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]

end RiemannResearch.Analysis.TwistedRieszFilter

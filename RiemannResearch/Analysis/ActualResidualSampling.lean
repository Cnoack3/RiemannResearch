/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConreyBaluyotConsequences
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualLogarithmicCovarianceAssembly
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ZeroSamplingQuadratic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual zero samples detect finite Dirichlet coordinate energies

Source: user-directed prime/zero-space residual formalization, 14 November 2026.
For the underlying arithmetic correction and sampling strategy, see
Ford--Meng--Zaharescu, *Simultaneous distribution of fractional parts of
Riemann zeta zeros*, Bull. London Math. Soc. 49 (2017), 1--9,
https://arxiv.org/abs/1511.06814 .
The source motivates the sampling input; the proofs below assemble existing
project Landau, density-comparison, and zero-count theorems.

Every sample is an actual zeta-zero copy, including analytic multiplicity.
The exact identity retains the complete signed prime-power form and the
literal remainder. Any positive uniform Selberg exponent suffices for
count-normalized convergence. Coefficients may vary with the height, provided
they converge on the finite head.

Each finite head admits eventual conditioning and a cofinal choice of heights.
There is no positive lower frame bound on the entire infinite space and no
claim that a residual's sampled energy vanishes. The concrete RH consumer is
QFullPrimeZeroResidual. Zero counts of zero give the usual totalized quotient;
all convergence arguments use the proved eventual positivity.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualResidualSampling
open ActualZeroOrdinate ActualDirichletPolynomialGram ZeroSamplingQuadratic

def countGram (T : ℝ) (n m : ℕ) : ℂ :=
  ordinateSum T (Real.log (n : ℝ) - Real.log (m : ℝ)) / (Ncount 0 T : ℂ)

def sampledEnergy (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (form s (countGram T) c).re

theorem copiedSquare_div_count (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    actualCopiedSquare T s c / (Ncount 0 T : ℂ) = form s (countGram T) c := by
  classical
  have hk : (fun n m : ℕ => ordinateSum T
      (Real.log (n : ℝ) - Real.log (m : ℝ))) =
      samplingGram (Finset.univ : Finset (Copies T)) (fun _ => (1 : ℝ))
        (fun z (k : ℕ) => ZeroOrdinate.phase (Real.log (k : ℝ)) z.1.1.im) := by
    funext n m
    exact (copy_samplingGram_eq_ordinate T n m).symm
  have hb : form s (fun n m => ordinateSum T
      (Real.log (n : ℝ) - Real.log (m : ℝ))) c = actualCopiedSquare T s c := by
    rw [hk, form_samplingGram]
    simp only [actualCopiedSquare, copyPolynomial, Complex.ofReal_one, one_mul]
  rw [← hb]
  calc
    _ = (Ncount 0 T : ℂ)⁻¹ * form s (fun n m => ordinateSum T
        (Real.log (n : ℝ) - Real.log (m : ℝ))) c := by ring
    _ = form s (fun n m => (Ncount 0 T : ℂ)⁻¹ * ordinateSum T
        (Real.log (n : ℝ) - Real.log (m : ℝ))) c := (form_mul _ _ _ _).symm
    _ = _ := by
      congr 1
      funext n m
      unfold countGram
      ring

theorem sampledEnergy_eq_mean (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    sampledEnergy T s c =
      (∑ z : Copies T, ‖copyPolynomial T s c z‖ ^ 2) / (Ncount 0 T : ℝ) := by
  have hs : actualCopiedSquare T s c =
      ((∑ z : Copies T, ‖copyPolynomial T s c z‖ ^ 2 : ℝ) : ℂ) := by
    simp [actualCopiedSquare, Complex.mul_conj, Complex.sq_norm]
  rw [sampledEnergy, ← copiedSquare_div_count, hs]
  norm_cast

theorem sampledEnergy_nonneg (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    0 ≤ sampledEnergy T s c := by
  rw [sampledEnergy_eq_mean]
  positivity

def primeRemainder (T : ℝ) (n m : ℕ) : ℂ :=
  countGram T n m - (if n = m then 1 else 0) -
    ((T : ℂ) / (Ncount 0 T : ℂ)) * rationalFMZMain n m

theorem sampledEnergy_signed_identity (T : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    sampledEnergy T s c = coefficientEnergy s c +
      (((T : ℂ) / (Ncount 0 T : ℂ)) * form s rationalFMZMain c).re +
      (form s (primeRemainder T) c).re := by
  classical
  have hg : countGram T = fun n m =>
      ((if n = m then 1 else 0) +
        ((T : ℂ) / (Ncount 0 T : ℂ)) * rationalFMZMain n m) +
          primeRemainder T n m := by
    funext n m
    unfold primeRemainder
    ring
  rw [sampledEnergy, hg, form_add, form_add, form_identity, form_mul]
  simp only [Complex.add_re, Complex.ofReal_re]

theorem rational_ordinate_count_tendsto_zero {a : ℝ}
    (ha : 0 < a) (hD : UniformSelbergDensity a)
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    Tendsto (fun T : ℝ => ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) /
      (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  have h1 := (tendsto_ordinate_landau_error_of_positive_density a
    (Real.log ((n : ℝ) / (m : ℝ))) ha hD).add
      (tendsto_rational_landau_div hm hmn)
  have h2 : Tendsto (fun T : ℝ =>
      ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ))
      atTop (𝓝 (-(rationalLandauMain n m : ℂ))) := by
    convert h1 using 1
    · funext T
      ring
    · simp
  have h3 := h2.mul tendsto_complex_height_div_count
  simp only [mul_zero] at h3
  apply h3.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_count_pos] with T hT hN
  have ht : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hn : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [ht, hn]

theorem countGram_star_swap (T : ℝ) (n m : ℕ) :
    countGram T n m = star (countGram T m n) := by
  unfold countGram
  rw [show Real.log (n : ℝ) - Real.log (m : ℝ) =
      -(Real.log (m : ℝ) - Real.log (n : ℝ)) by ring, ordinateSum_neg]
  simp

theorem countGram_tendsto {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun T : ℝ => countGram T n m) atTop (𝓝 (if n = m then 1 else 0)) := by
  have hpos {k l : ℕ} (hl : 1 ≤ l) (hlk : l < k) :
      Tendsto (fun T : ℝ => countGram T k l) atTop (𝓝 0) := by
    have hk : 1 ≤ k := by omega
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    simpa only [countGram, Real.log_div hk0 hl0] using
      rational_ordinate_count_tendsto_zero ha hD hl hlk
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · simpa only [if_neg (by omega : n ≠ m)] using hpos hm hmn
  · subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_count_pos] with T hT
    simp [countGram, (by exact_mod_cast hT.ne' : (Ncount 0 T : ℂ) ≠ 0)]
  · have h := (hpos hn hnm).star
    simpa only [countGram_star_swap (n := n) (m := m), star_zero,
      if_neg (by omega : n ≠ m)] using h

theorem sampledEnergy_tendsto_of_coefficients
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (c : ℕ → ℕ → ℂ) (d : ℕ → ℂ)
    (hc : ∀ n ∈ s, Tendsto (fun j => c j n) atTop (𝓝 (d n))) :
    Tendsto (fun j => sampledEnergy (T j) s (c j)) atTop
      (𝓝 (coefficientEnergy s d)) := by
  have h : Tendsto (fun j => form s (countGram (T j)) (c j)) atTop
      (𝓝 (form s (fun n m => if n = m then 1 else 0) d)) := by
    unfold form
    exact tendsto_finsetSum s (fun n hn => tendsto_finsetSum s (fun m hm =>
      ((hc n hn).mul (hc m hm).star).mul
        ((countGram_tendsto ha hD (hs n hn) (hs m hm)).comp hT)))
  rw [form_identity] at h
  simpa only [sampledEnergy, Complex.ofReal_re, Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp h


/-- Each fixed finite block is eventually well conditioned. No uniform
lower bound on the entire infinite sampled space is asserted. -/
theorem eventually_finite_detection
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ℕ → ℂ,
      (1 / 2 : ℝ) * coefficientEnergy s c ≤ sampledEnergy T s c ∧
      sampledEnergy T s c ≤ (3 / 2 : ℝ) * coefficientEnergy s c := by
  classical
  let ε : ℝ := 1 / (2 * (s.card : ℝ) + 2)
  have hepos : 0 < ε := by dsimp [ε]; positivity
  have hnorm (n m : s) :
      Tendsto (fun T : ℝ => ‖countGram T n m - (if (n : ℕ) = m then 1 else 0)‖)
        atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((countGram_tendsto ha hD (hs n n.property) (hs m m.property)).sub_const
        (if (n : ℕ) = m then 1 else 0)).norm
  have hb : ∀ᶠ T : ℝ in atTop, ∀ n : s, ∀ m : s,
      ‖countGram T n m - (if (n : ℕ) = m then 1 else 0)‖ ≤ ε :=
    Filter.eventually_all.mpr (fun n => Filter.eventually_all.mpr
      (fun m => (hnorm n m).eventually_le_const hepos))
  have he : (s.card : ℝ) * ε ≤ (1 / 2 : ℝ) := by
    dsimp [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (s.card : ℝ) + 2)).mpr
    linarith
  filter_upwards [hb] with T hT c
  have h := near_identity_bounds s (countGram T) c ε hepos.le
    (fun n hn m hm => hT ⟨n, hn⟩ ⟨m, hm⟩)
  have hec := mul_le_mul_of_nonneg_right he (coefficientEnergy_nonneg s c)
  change (1 / 2 : ℝ) * coefficientEnergy s c ≤ (form s (countGram T) c).re ∧
    (form s (countGram T) c).re ≤ (3 / 2 : ℝ) * coefficientEnergy s c
  constructor <;> nlinarith [h.1, h.2]


/-- The signed remainder is the literal residual after removing the exact
prime-power term; it is not an independently postulated error matrix. -/
theorem primeRemainder_tendsto_zero
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Tendsto (fun T : ℝ => primeRemainder T n m) atTop (𝓝 0) := by
  have h := ((countGram_tendsto ha hD hn hm).sub_const
    (if n = m then 1 else 0)).sub
      (tendsto_complex_height_div_count.mul_const (rationalFMZMain n m))
  simpa only [primeRemainder, sub_self, zero_mul, sub_zero] using h

/-- Arbitrary finite heads have cofinal sampling heights at which every
coefficient vector is detected. This is finite-dimensional conditioning,
not a positive lower frame bound on the infinite Hilbert space. -/
theorem exists_cofinal_detection_schedule
    {a : ℝ} (ha : 0 < a) (hD : UniformSelbergDensity a)
    (s : ℕ → Finset ℕ) (hs : ∀ j n, n ∈ s j → 1 ≤ n) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ ∀ j (c : ℕ → ℂ),
      (1 / 2 : ℝ) * coefficientEnergy (s j) c ≤ sampledEnergy (T j) (s j) c ∧
      sampledEnergy (T j) (s j) c ≤ (3 / 2 : ℝ) * coefficientEnergy (s j) c := by
  have hb (j : ℕ) : ∃ b : ℝ, ∀ t, b ≤ t → ∀ c : ℕ → ℂ,
      (1 / 2 : ℝ) * coefficientEnergy (s j) c ≤ sampledEnergy t (s j) c ∧
      sampledEnergy t (s j) c ≤ (3 / 2 : ℝ) * coefficientEnergy (s j) c :=
    Filter.eventually_atTop.mp (eventually_finite_detection ha hD (s j) (hs j))
  choose b hb using hb
  refine ⟨fun j => max (j : ℝ) (b j), ?_, ?_⟩
  · exact tendsto_atTop_mono (fun j => le_max_left (j : ℝ) (b j))
      tendsto_natCast_atTop_atTop
  · intro j c
    exact hb j _ (le_max_right (j : ℝ) (b j)) c

end RiemannResearch.Analysis.ActualResidualSampling

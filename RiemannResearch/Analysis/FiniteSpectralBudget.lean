/-
# Finite source spectral budgets for the Green–Pareto–Schur continuation

Source: user-provided Green-Pareto-Schur continuation, Sections 12 and 17.

This Mathlib-only module extends Sections 12.4–12.6 of the supplied Markdown.
Its hypotheses are explicit finite scalar hypotheses. It does NOT assert any
moment bound, tightness, screening provider, or RH result for the actual
arithmetic matrices. In that application the data are the complete spectrum
of H^(-1/2) Theta H^(-1/2), with source weights |<H^(-1/2)a,u_i>|^2.

All conductors and source components remain present before spectral screening.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

variable {ι : Type*}

/-- Source mass. In the compact two–three application this is 134-e_N. -/
def mass (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, w i

/-- Complete correction T, expressed in the generalized tail/head spectrum. -/
def correction (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * lam i / (1 + lam i)

/-- Full optimizer physical-tail square S. -/
def optimizerTail (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * lam i / (1 + lam i)^2

/-- Head displacement square J. -/
def headDisplacement (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (lam i / (1 + lam i))^2

/-- Source mass removed by screening all eigenvalues at or above R. -/
def highMass (s : Finset ι) (w lam : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i ∈ s, if R ≤ lam i then w i else 0

/-- A source-weighted spectral moment. Phi may grow arbitrarily slowly. -/
def moment (s : Finset ι) (w lam : ι → ℝ) (Phi : ℝ → ℝ) : ℝ :=
  ∑ i ∈ s, w i * Phi (lam i)

/-- Complete physical tail of the spectrally retained head trial. -/
def screenedTail (s : Finset ι) (w lam : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ i ∈ s, if R ≤ lam i then 0 else w i * lam i

theorem correction_nonneg (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    0 ≤ correction s w lam := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi])

theorem optimizerTail_nonneg (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    0 ≤ optimizerTail s w lam := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (sq_nonneg _)

theorem highMass_nonneg (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ highMass s w lam R := by
  apply Finset.sum_nonneg
  intro i hi
  by_cases hr : R ≤ lam i
  · rw [if_pos hr]
    exact hw i hi
  · simpa only [if_neg hr] using (le_rfl : (0 : ℝ) ≤ 0)

/-- Exact finite identity preserving both nonnegative correction squares. -/
theorem correction_eq_headDisplacement_add_optimizerTail
    (s : Finset ι) (w lam : ι → ℝ) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    correction s w lam = headDisplacement s w lam + optimizerTail s w lam := by
  unfold correction headDisplacement optimizerTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : (1 + lam i) ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  field_simp [hd]
  ring

private theorem scalar_correction_le_weight (w lam : ℝ)
    (hw : 0 ≤ w) (hlam : 0 ≤ lam) : w*lam/(1+lam) ≤ w := by
  apply (div_le_iff₀ (by linarith : 0 < 1+lam)).mpr
  nlinarith

private theorem scalar_correction_le_low_tail (w lam R : ℝ)
    (hw : 0 ≤ w) (hlam : 0 ≤ lam) (hlamR : lam ≤ R) :
    w*lam/(1+lam) ≤ (1+R)*(w*lam/(1+lam)^2) := by
  have hd : 1+lam ≠ 0 := ne_of_gt (by linarith)
  have hid : w*lam/(1+lam) = (1+lam)*(w*lam/(1+lam)^2) := by
    field_simp [hd]
  rw [hid]
  apply mul_le_mul_of_nonneg_right (by linarith)
  exact div_nonneg (mul_nonneg hw hlam) (sq_nonneg _)

/-- A threshold split uses S only on the low spectrum and leaves the entire
high-spectrum source mass intact. No a priori first moment is required. -/
theorem correction_le_threshold_tail_add_highMass
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hR : 0 ≤ R) :
    correction s w lam ≤ (1+R)*optimizerTail s w lam + highMass s w lam R := by
  unfold correction optimizerTail highMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hs : 0 ≤ w i*lam i/(1+lam i)^2 :=
    div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (sq_nonneg _)
  by_cases hr : R ≤ lam i
  · rw [if_pos hr]
    have ht := scalar_correction_le_weight (w i) (lam i) (hw i hi) (hlam i hi)
    have hp : 0 ≤ (1+R)*(w i*lam i/(1+lam i)^2) :=
      mul_nonneg (by linarith) hs
    linarith
  · rw [if_neg hr, add_zero]
    exact scalar_correction_le_low_tail (w i) (lam i) R
      (hw i hi) (hlam i hi) (le_of_lt (lt_of_not_ge hr))

private theorem scalar_weight_le_correction_add_high_tail
    (w lam R : ℝ) (hw : 0 ≤ w) (hlam : 0 ≤ lam) (hR : 0 < R) (hRlam : R ≤ lam) :
    w ≤ w*lam/(1+lam) + ((1+R)/R)*(w*lam/(1+lam)^2) := by
  have hlampos : 0 < lam := lt_of_lt_of_le hR hRlam
  have hd : 1+lam ≠ 0 := ne_of_gt (by linarith)
  have hid : w = w*lam/(1+lam) + w/(1+lam) := by
    field_simp [hd]
    ring
  have hratio : (1+lam)/lam ≤ (1+R)/R := by
    apply (div_le_div_iff₀ hlampos hR).mpr
    nlinarith
  have htail : w/(1+lam) = ((1+lam)/lam)*(w*lam/(1+lam)^2) := by
    field_simp [hd, ne_of_gt hlampos]
  have hs : 0 ≤ w*lam/(1+lam)^2 := div_nonneg (mul_nonneg hw hlam) (sq_nonneg _)
  calc
    w = w*lam/(1+lam) + ((1+lam)/lam)*(w*lam/(1+lam)^2) := by rw [← htail]; exact hid
    _ ≤ w*lam/(1+lam) + ((1+R)/R)*(w*lam/(1+lam)^2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio hs)

/-- Reverse threshold comparison. For each fixed positive R the removed
source mass and complete correction differ by at most a constant times S. -/
theorem highMass_le_correction_add_threshold_tail
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hR : 0 < R) :
    highMass s w lam R ≤ correction s w lam + ((1+R)/R)*optimizerTail s w lam := by
  unfold highMass correction optimizerTail
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hr : R ≤ lam i
  · rw [if_pos hr]
    exact scalar_weight_le_correction_add_high_tail
      (w i) (lam i) R (hw i hi) (hlam i hi) hR hr
  · rw [if_neg hr]
    have ht : 0 ≤ w i*lam i/(1+lam i) :=
      div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi])
    have hs : 0 ≤ w i*lam i/(1+lam i)^2 :=
      div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (sq_nonneg _)
    have hc : 0 ≤ (1+R)/R := div_nonneg (by linarith) (le_of_lt hR)
    exact add_nonneg ht (mul_nonneg hc hs)

/-- Quantitative polarization of the source spectrum at every fixed
positive threshold. The estimate retains the complete source weights. -/
theorem abs_highMass_sub_correction_le_threshold_tail
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hR : 0 < R) :
    |highMass s w lam R - correction s w lam| ≤
      max (1+R) ((1+R)/R)*optimizerTail s w lam := by
  have hforward := correction_le_threshold_tail_add_highMass s w lam R hw hlam (le_of_lt hR)
  have hreverse := highMass_le_correction_add_threshold_tail s w lam R hw hlam hR
  have hs := optimizerTail_nonneg s w lam hw hlam
  have hleft := mul_le_mul_of_nonneg_right (le_max_left (1+R) ((1+R)/R)) hs
  have hright := mul_le_mul_of_nonneg_right (le_max_right (1+R) ((1+R)/R)) hs
  apply abs_le.mpr
  constructor <;> linarith

/-- A division-free weighted Markov inequality. Monotonicity is required
only above the selected threshold; the moment integrand is nonnegative
below it. Thus this also applies to threshold-adapted, stage-dependent Phi. -/
theorem threshold_mul_highMass_le_moment
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ) (Phi : ℝ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hPhi : ∀ i ∈ s, 0 ≤ Phi (lam i))
    (hmono : ∀ i ∈ s, R ≤ lam i → Phi R ≤ Phi (lam i)) :
    Phi R * highMass s w lam R ≤ moment s w lam Phi := by
  unfold highMass moment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hr : R ≤ lam i
  · rw [if_pos hr, mul_comm (Phi R)]
    exact mul_le_mul_of_nonneg_left (hmono i hi hr) (hw i hi)
  · rw [if_neg hr, mul_zero]
    exact mul_nonneg (hw i hi) (hPhi i hi)

/-- The quantitative moment bound needs monotonicity only on the actual
spectral points above the chosen threshold. In particular, it applies to
log(1+x), whose monotonicity is needed only for x≥0. -/
theorem correction_le_threshold_tail_add_local_moment_quotient
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ) (Phi : ℝ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hR : 0 ≤ R) (hPhiR : 0 < Phi R)
    (hPhi : ∀ i ∈ s, 0 ≤ Phi (lam i))
    (hmono : ∀ i ∈ s, R ≤ lam i → Phi R ≤ Phi (lam i)) :
    correction s w lam ≤ (1+R)*optimizerTail s w lam +
      moment s w lam Phi / Phi R := by
  apply (correction_le_threshold_tail_add_highMass s w lam R hw hlam hR).trans
  apply add_le_add le_rfl
  apply (le_div_iff₀ hPhiR).mpr
  rw [mul_comm]
  exact threshold_mul_highMass_le_moment s w lam R Phi hw hPhi hmono

/-- Monotone coercive-moment providers give a quantitative finite bound.
Coercivity is deliberately not assumed in this finite theorem; it is used
only when the threshold is sent to infinity. -/
theorem correction_le_threshold_tail_add_moment_quotient
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ) (Phi : ℝ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hR : 0 ≤ R) (hPhiR : 0 < Phi R)
    (hPhi : ∀ i ∈ s, 0 ≤ Phi (lam i)) (hmono : Monotone Phi) :
    correction s w lam ≤ (1+R)*optimizerTail s w lam +
      moment s w lam Phi / Phi R := by
  exact correction_le_threshold_tail_add_local_moment_quotient
    s w lam R Phi hw hlam hR hPhiR hPhi
    (fun i _ hi => hmono hi)

/-- Concrete logarithmic source budget, strictly weaker as a provider than
a first-moment cap. The finite inequality itself is unconditional for any
nonnegative finite spectral data; boundedness of the arithmetic logarithmic
moment is NOT asserted. -/
theorem correction_le_threshold_tail_add_log_moment
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hR : 0 < R) :
    correction s w lam ≤ (1+R)*optimizerTail s w lam +
      (∑ i ∈ s, w i * Real.log (1+lam i)) / Real.log (1+R) := by
  apply correction_le_threshold_tail_add_local_moment_quotient
    s w lam R (fun x => Real.log (1+x)) hw hlam (le_of_lt hR)
  · exact Real.log_pos (by linarith)
  · intro i hi
    exact Real.log_nonneg (by linarith [hlam i hi])
  · intro i _ hi
    exact Real.log_le_log (by linarith : 0 < 1+R) (by linarith)

/-- The retained trial has tail energy at most R times the entire source
mass. Screening removes eigencomponents, not conductor columns. -/
theorem screenedTail_le_threshold_mul_mass
    (s : Finset ι) (w lam : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hR : 0 ≤ R) :
    screenedTail s w lam R ≤ R*mass s w := by
  unfold screenedTail mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hr : R ≤ lam i
  · rw [if_pos hr]
    exact mul_nonneg hR (hw i hi)
  · rw [if_neg hr, mul_comm R]
    exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hr)) (hw i hi)

/-- A legal screened trial with head charge e has complete error bounded
by e + removed source mass + R times total source mass. In the arithmetic
application the equality identifying trial error is a separate geometric
statement, not an assumption hidden in this finite spectral module. -/
theorem screened_trial_budget (s : Finset ι) (w lam : ι → ℝ) (R e : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hR : 0 ≤ R) :
    e + highMass s w lam R + screenedTail s w lam R ≤
      e + highMass s w lam R + R*mass s w := by
  exact add_le_add le_rfl (screenedTail_le_threshold_mul_mass s w lam R hw hR)

/-- Strict fractional feedback is absorbable; no separate bound on T is
required. This is the finite scalar core of relaxed cancellation providers. -/
theorem absorption_bound (T E theta : ℝ) (htheta : theta < 1)
    (hbudget : T ≤ E + theta*T) : T ≤ E/(1-theta) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-theta)).mpr
  nlinarith

/-- A vanishing error with any fixed strict feedback fraction forces T→0. -/
theorem correction_tendsto_zero_of_absorbed_budget
    (T E : ℕ → ℝ) (theta : ℝ) (htheta : theta < 1)
    (hT : ∀ n, 0 ≤ T n) (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ n, T n ≤ E n + theta*T n) :
    Tendsto T atTop (𝓝 0) := by
  apply squeeze_zero hT (fun n => absorption_bound (T n) (E n) theta htheta (hbudget n))
  simpa using hE.div_const (1-theta)

/-- A moving cutoff gives a direct quantitative route: only the product
(1+R_N)S_N and the complete high-spectrum mass must vanish. -/
theorem correction_tendsto_zero_of_threshold_budgets
    (T S B R : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n)
    (hbound : ∀ n, T n ≤ (1+R n)*S n + B n)
    (hlow : Tendsto (fun n => (1+R n)*S n) atTop (𝓝 0))
    (hhigh : Tendsto B atTop (𝓝 0)) : Tendsto T atTop (𝓝 0) := by
  apply squeeze_zero hT hbound
  simpa using hlow.add hhigh

/-- Cofinal relative logarithmic growth is enough. The moment may be
unbounded: only its ratio to log(1+R_n) must vanish, while the moving low
spectral budget (1+R_n)S_{k_n} vanishes. This finite-spectrum consumer does
not assume the arithmetic logarithmic provider or its spectral realization. -/
theorem limit_eq_zero_of_cofinal_log_moment_budgets
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (R : ℕ → ℝ)
    (k : ℕ → ℕ) (delta : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hR : ∀ n, 0 < R n) (hk : Tendsto k atTop atTop)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1+R n)*optimizerTail (s (k n)) (w (k n)) (lam (k n))) atTop (𝓝 0))
    (hlog : Tendsto (fun n =>
      (∑ i ∈ s (k n), w (k n) i * Real.log (1+lam (k n) i)) /
        Real.log (1+R n)) atTop (𝓝 0)) : delta = 0 := by
  have hz : Tendsto (fun n => correction (s (k n)) (w (k n)) (lam (k n)))
      atTop (𝓝 0) := by
    apply correction_tendsto_zero_of_threshold_budgets
      (fun n => correction (s (k n)) (w (k n)) (lam (k n)))
      (fun n => optimizerTail (s (k n)) (w (k n)) (lam (k n)))
      (fun n => (∑ i ∈ s (k n), w (k n) i * Real.log (1+lam (k n) i)) /
        Real.log (1+R n)) R
    · intro n
      exact correction_nonneg _ _ _ (hw (k n)) (hlam (k n))
    · intro n
      exact correction_le_threshold_tail_add_log_moment _ _ _ _
        (hw (k n)) (hlam (k n)) (hR n)
    · exact hlow
    · exact hlog
  exact tendsto_nhds_unique (hT.comp hk) hz

end RiemannResearch.Analysis.FiniteSpectralBudget

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroHorizontalEnergy
import RiemannResearch.Analysis.HorizontalPhaseBootstrap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive actual-zero cosh mass

The source note `Prime_Phase_Harmonic_Analysis_Corrected_20261011(1).md`,
Section 8, supplies the exact reflected signed correction. This companion
retains its nonnegative horizontal mass without the complex phase factor.
Every actual positive-height zero and its analytic multiplicity are kept.
The cofinal epsilon criterion concerns the UNNORMALIZED mass. It is an
equivalence, not a proof that the mass vanishes; no RH or density assumption
is used in the criterion.
-/

noncomputable section
open Complex Zeta23 Filter
open scoped BigOperators Topology

namespace Real

/-- The first positive even Taylor term is retained as a lower bound. -/
theorem sq_div_two_le_cosh_sub_one (q : ℝ) : q ^ 2 / 2 ≤ cosh q - 1 := by
  have h :=
    (RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_summable q).sum_le_tsum
      ({0} : Finset ℕ) (fun k _ =>
        div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg q) _) (Nat.cast_nonneg _))
  rw [Finset.sum_singleton,
    RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_tsum] at h
  norm_num at h
  exact h

private theorem cosh_even_power_le_scaled_half (u d : ℝ)
    (hd : d ^ 2 ≤ 1 / 4) (k : ℕ) :
    (u * d) ^ (2 * (k + 1)) ≤
      (4 * d ^ 2) * (u / 2) ^ (2 * (k + 1)) := by
  have hbase : (u * d) ^ 2 ≤ (u / 2) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hd (sq_nonneg u)]
  have hpow : ((u * d) ^ 2) ^ k ≤ ((u / 2) ^ 2) ^ k :=
    pow_le_pow_left₀ (sq_nonneg (u * d)) hbase k
  have hsplit (x : ℝ) : x ^ (2 * (k + 1)) = x ^ 2 * (x ^ 2) ^ k := by
    rw [Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
    ring
  calc
    (u * d) ^ (2 * (k + 1)) =
        (u * d) ^ 2 * ((u * d) ^ 2) ^ k := hsplit _
    _ ≤ (u * d) ^ 2 * ((u / 2) ^ 2) ^ k :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = (4 * d ^ 2) * (u / 2) ^ (2 * (k + 1)) := by
      rw [hsplit]
      ring

/-- The sharp uniform strip coefficient follows termwise from the complete
even series. Equality at `d = ±1/2` prevents a smaller uniform coefficient. -/
theorem cosh_mul_sub_one_le_sharp (u d : ℝ) (hd : d ^ 2 ≤ 1 / 4) :
    cosh (u * d) - 1 ≤ (4 * (cosh (|u| / 2) - 1)) * d ^ 2 := by
  let a : ℕ → ℝ := fun k =>
    (u * d) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ)
  let b : ℕ → ℝ := fun k =>
    (4 * d ^ 2) *
      ((u / 2) ^ (2 * (k + 1)) / (Nat.factorial (2 * (k + 1)) : ℝ))
  have hs : Summable a :=
    RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_summable (u * d)
  have ht : Summable b :=
    (RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_summable
      (u / 2)).mul_left (4 * d ^ 2)
  have hb (k : ℕ) : a k ≤ b k := by
    dsimp [a, b]
    calc
      _ ≤ ((4 * d ^ 2) * (u / 2) ^ (2 * (k + 1))) /
          (Nat.factorial (2 * (k + 1)) : ℝ) :=
        div_le_div_of_nonneg_right (cosh_even_power_le_scaled_half u d hd k)
          (Nat.cast_nonneg _)
      _ = _ := by ring
  have h := Summable.tsum_le_tsum hb hs ht
  dsimp [a, b] at h
  rw [RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_tsum,
    tsum_mul_left,
    RiemannResearch.Analysis.HorizontalPhaseBootstrap.cosh_tail_tsum] at h
  have heven : cosh (u / 2) = cosh (|u| / 2) := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · have hu' : u < 0 := lt_of_not_ge hu
      rw [abs_of_neg hu', neg_div, cosh_neg]
  rw [heven] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end Real

namespace RiemannResearch.Analysis.ActualZeroCoshMass
open ActualZeroOrdinate ZeroOrdinate

/-- The single-copy defect is nonnegative for every real frequency. -/
def coshDefect (u : ℝ) (ρ : ℂ) : ℝ :=
  Real.cosh (u * (ρ.re - 1 / 2)) - 1

theorem coshDefect_nonneg (u : ℝ) (ρ : ℂ) : 0 ≤ coshDefect u ρ := by
  exact sub_nonneg.mpr (Real.one_le_cosh _)

theorem coshDefect_pos {u : ℝ} (hu : u ≠ 0) {ρ : ℂ}
    (hρ : ρ.re ≠ 1 / 2) : 0 < coshDefect u ρ := by
  exact sub_pos.mpr (Real.one_lt_cosh.mpr
    (mul_ne_zero hu (sub_ne_zero.mpr hρ)))

theorem coshDefect_eq_zero_iff {u : ℝ} (hu : u ≠ 0) (ρ : ℂ) :
    coshDefect u ρ = 0 ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    by_contra hn
    have hp := coshDefect_pos hu hn
    rw [h] at hp
    exact lt_irrefl 0 hp
  · intro h
    simp [coshDefect, h]

/-- Analytic multiplicity is retained in every individual contribution. -/
def singleCharge (u : ℝ) (ρ : ℂ) : ℝ :=
  (zeroMult ρ : ℝ) * coshDefect u ρ

theorem singleCharge_nonneg (u : ℝ) (ρ : ℂ) : 0 ≤ singleCharge u ρ :=
  mul_nonneg (Nat.cast_nonneg _) (coshDefect_nonneg u ρ)

/-- Positive horizontal mass with the original actual zero cutoff. -/
def coshMass (T u : ℝ) : ℝ := realSum T (coshDefect u)

theorem coshMass_nonneg (T u : ℝ) : 0 ≤ coshMass T u :=
  realSum_nonneg T _ (fun ρ _ => coshDefect_nonneg u ρ)

theorem singleCharge_le_mass {T : ℝ} (u : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ cutoff T) : singleCharge u ρ ≤ coshMass T u := by
  unfold singleCharge coshMass realSum
  exact Finset.single_le_sum
    (fun σ _ => singleCharge_nonneg u σ) hρ

theorem cutoff_subset_of_le {S T : ℝ} (hST : S ≤ T) : cutoff S ⊆ cutoff T := by
  intro ρ hρ
  obtain ⟨hz, hi, hS⟩ := mem_cutoff.mp hρ
  exact mem_cutoff.mpr ⟨hz, hi, hS.trans hST⟩

/-- An off-line zero's positive contribution survives every later cutoff. -/
theorem coshMass_monotone (u : ℝ) : Monotone (fun T => coshMass T u) := by
  intro S T hST
  unfold coshMass realSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (cutoff_subset_of_le hST)
  intro ρ _ _
  exact singleCharge_nonneg u ρ

theorem coshMass_eq_zero_iff (T : ℝ) {u : ℝ} (hu : u ≠ 0) :
    coshMass T u = 0 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · intro he ρ hρ
    by_contra hn
    have hm : (0 : ℝ) < (zeroMult ρ : ℝ) := by
      exact_mod_cast multiplicity_pos hρ
    have hp : 0 < singleCharge u ρ := mul_pos hm (coshDefect_pos hu hn)
    have hs := singleCharge_le_mass u hρ
    rw [he] at hs
    exact (not_lt_of_ge hs) hp
  · intro hall
    unfold coshMass realSum
    apply Finset.sum_eq_zero
    intro ρ hρ
    rw [(coshDefect_eq_zero_iff hu ρ).mpr (hall ρ hρ), mul_zero]

theorem all_cutoffs_zero_iff {u : ℝ} (hu : u ≠ 0) :
    (∀ T : ℝ, coshMass T u = 0) ↔
      ∀ ρ : PositiveZero, ρ.1.re = 1 / 2 := by
  constructor
  · intro h ρ
    apply (coshMass_eq_zero_iff ρ.1.im hu).mp (h ρ.1.im) ρ.1
    exact mem_cutoff_iff_zeta.mpr ⟨ρ.2.1, ρ.2.2, le_rfl⟩
  · intro h T
    apply (coshMass_eq_zero_iff T hu).mpr
    intro ρ hρ
    obtain ⟨hz, hi, _⟩ := mem_cutoff_iff_zeta.mp hρ
    exact h ⟨ρ, hz, hi⟩

/-- Arbitrarily small UNNORMALIZED mass at arbitrarily high cutoffs is
equivalent to the critical-line assertion for every actual positive zero.
Sparse off-line zeros cannot disappear from this monotone positive mass. -/
theorem cofinal_coshMass_small_iff {u : ℝ} (hu : u ≠ 0) :
    (∀ ε : ℝ, 0 < ε → ∀ B : ℝ,
      ∃ T : ℝ, B ≤ T ∧ coshMass T u < ε) ↔
      ∀ ρ : PositiveZero, ρ.1.re = 1 / 2 := by
  constructor
  · intro h ρ
    by_contra hn
    have hmembase : ρ.1 ∈ cutoff ρ.1.im :=
      mem_cutoff_iff_zeta.mpr ⟨ρ.2.1, ρ.2.2, le_rfl⟩
    have hm : (0 : ℝ) < (zeroMult ρ.1 : ℝ) := by
      exact_mod_cast multiplicity_pos hmembase
    have hp : 0 < singleCharge u ρ.1 := mul_pos hm (coshDefect_pos hu hn)
    obtain ⟨T, hT, he⟩ := h (singleCharge u ρ.1 / 2) (by positivity) ρ.1.im
    have hmem : ρ.1 ∈ cutoff T :=
      mem_cutoff_iff_zeta.mpr ⟨ρ.2.1, ρ.2.2, hT⟩
    have hs := singleCharge_le_mass u hmem
    linarith
  · intro h ε hε B
    refine ⟨B, le_rfl, ?_⟩
    rw [(all_cutoffs_zero_iff hu).mpr h B]
    exact hε

/-- For this monotone nonnegative quantity, convergence to zero is equally
strong as cofinal epsilon smallness. No zero-density estimate is used. -/
theorem coshMass_tendsto_zero_iff {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun T : ℝ => coshMass T u) atTop (nhds 0) ↔
      ∀ ρ : PositiveZero, ρ.1.re = 1 / 2 := by
  constructor
  · intro hlim
    apply (cofinal_coshMass_small_iff hu).mp
    intro ε hε B
    have hev : ∀ᶠ T : ℝ in atTop, coshMass T u < ε :=
      hlim.eventually_lt_const hε
    obtain ⟨S, hS⟩ := eventually_atTop.mp hev
    refine ⟨max B S, le_max_left _ _, hS _ (le_max_right _ _)⟩
  · intro h
    have hz := (all_cutoffs_zero_iff hu).mpr h
    simp_rw [hz]
    exact tendsto_const_nhds

/-- The complete signed reflected phase correction is controlled by its
positive mass, without first discarding any zero or multiplicity. -/
theorem norm_coshCorrection_le_mass (T u : ℝ) :
    ‖coshCorrection T u‖ ≤ coshMass T u := by
  unfold coshCorrection
  calc
    _ ≤ realSum T (fun ρ => ‖phase u ρ.im *
        ((Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) - 1)‖) := norm_sum_le _ _
    _ ≤ coshMass T u := by
      apply realSum_mono
      intro ρ hρ
      have he : (Real.cosh (u * (ρ.re - 1 / 2)) : ℂ) - 1 =
          (coshDefect u ρ : ℂ) := by simp [coshDefect]
      rw [norm_mul, phase_norm, one_mul, he,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coshDefect_nonneg u ρ)]

/-- Sharp finite-cutoff control, retaining all actual multiplicities. -/
theorem coshMass_le_horizontalEnergy_sharp (T u : ℝ) :
    coshMass T u ≤ (4 * (Real.cosh (|u| / 2) - 1)) * horizontalEnergy T := by
  calc
    _ ≤ realSum T (fun ρ => (ρ.re - 1 / 2) ^ 2 *
        (4 * (Real.cosh (|u| / 2) - 1))) := by
      apply realSum_mono
      intro ρ hρ
      have hd := displacement_lt_half hρ
      have hsq : (ρ.re - 1 / 2) ^ 2 ≤ 1 / 4 := by
        nlinarith [sq_abs (ρ.re - 1 / 2), abs_nonneg (ρ.re - 1 / 2)]
      simpa only [coshDefect, mul_comm] using
        Real.cosh_mul_sub_one_le_sharp u (ρ.re - 1 / 2) hsq
    _ = _ := by rw [realSum_mul_const]; exact mul_comm _ _
theorem ordinate_landau_error_sharp (T u : ℝ) :
    ‖ordinateSum T u - landauSum T u‖ ≤
      (4 * (Real.cosh (|u| / 2) - 1)) * horizontalEnergy T := by
  have he : ordinateSum T u - landauSum T u = -coshCorrection T u := by
    rw [exact_signed_correction]
    abel
  rw [he, norm_neg]
  exact (norm_coshCorrection_le_mass T u).trans
    (coshMass_le_horizontalEnergy_sharp T u)
theorem sharp_coefficient_le_exponential (u : ℝ) :
    4 * (Real.cosh (|u| / 2) - 1) ≤ u ^ 2 * Real.exp (|u| / 2) := by
  have h := cosh_sub_one_bound (|u| / 2)
  have he : ‖(Real.cosh (|u| / 2) : ℂ) - 1‖ = Real.cosh (|u| / 2) - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
  rw [he, abs_of_nonneg (by positivity : 0 ≤ |u| / 2)] at h
  calc
    _ ≤ 4 * ((|u| / 2) ^ 2 * Real.exp (|u| / 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [div_pow, sq_abs]; ring

/-! ## Regularized mass over all actual zeros

This uses every actual nontrivial zero, including both ordinate signs and
any real zeros. Thus the all-zero RH criterion needs no real-axis exclusion
provider. The existing unconditional fourth-energy summability supplies
convergence, rather than an unproved zero-density estimate.
-/

open ActualZeroHorizontalEnergy

theorem actual_coshDefect_le (u : ℝ) (ρ : ActualZero) :
    coshDefect u (ρ : ℂ) ≤
      (u ^ 2 * Real.exp (|u| / 2)) * ((ρ : ℂ).re - 1 / 2) ^ 2 := by
  have hstrip : IsNontrivialZero (ρ : ℂ) := ρ.property
  have hd : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hstrip.2.1, hstrip.2.2]
  have ha : |u * ((ρ : ℂ).re - 1 / 2)| ≤ |u| / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg u]
  have he : (Real.cosh (u * ((ρ : ℂ).re - 1 / 2)) : ℂ) - 1 =
      (coshDefect u (ρ : ℂ) : ℂ) := by simp [coshDefect]
  have hn : ‖(Real.cosh (u * ((ρ : ℂ).re - 1 / 2)) : ℂ) - 1‖ =
      coshDefect u (ρ : ℂ) := by
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coshDefect_nonneg u (ρ : ℂ))]
  calc
    _ = ‖(Real.cosh (u * ((ρ : ℂ).re - 1 / 2)) : ℂ) - 1‖ := hn.symm
    _ ≤ (u * ((ρ : ℂ).re - 1 / 2)) ^ 2 *
        Real.exp |u * ((ρ : ℂ).re - 1 / 2)| := cosh_sub_one_bound _
    _ ≤ (u * ((ρ : ℂ).re - 1 / 2)) ^ 2 * Real.exp (|u| / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (sq_nonneg _)
    _ = _ := by ring

/-- The optimal strip-envelope coefficient improves the exponential majorant. -/
theorem actual_coshDefect_le_sharp (u : ℝ) (ρ : ActualZero) :
    coshDefect u (ρ : ℂ) ≤
      (4 * (Real.cosh (|u| / 2) - 1)) * ((ρ : ℂ).re - 1 / 2) ^ 2 := by
  have hd : ((ρ : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
    have hstrip : IsNontrivialZero (ρ : ℂ) := ρ.property
    nlinarith only [hstrip.2.1, hstrip.2.2,
      mul_nonneg hstrip.2.1.le (sub_nonneg.mpr hstrip.2.2.le)]
  exact Real.cosh_mul_sub_one_le_sharp u ((ρ : ℂ).re - 1 / 2) hd

/-- Each actual zero keeps its analytic multiplicity and horizontal defect. -/
def regularizedTerm (u : ℝ) (ρ : ActualZero) : ℝ :=
  (zeroMult (ρ : ℂ) : ℝ) * coshDefect u (ρ : ℂ) /
    (1 + (ρ : ℂ).im ^ 2) ^ 2

theorem regularizedTerm_nonneg (u : ℝ) (ρ : ActualZero) :
    0 ≤ regularizedTerm u ρ := by
  unfold regularizedTerm
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (coshDefect_nonneg u (ρ : ℂ))) (by positivity)

theorem regularizedTerm_le_horizontalTerm (u : ℝ) (ρ : ActualZero) :
    regularizedTerm u ρ ≤
      (u ^ 2 * Real.exp (|u| / 2)) * horizontalTerm ρ := by
  unfold regularizedTerm horizontalTerm
  calc
    _ ≤ (zeroMult (ρ : ℂ) : ℝ) *
        ((u ^ 2 * Real.exp (|u| / 2)) * ((ρ : ℂ).re - 1 / 2) ^ 2) /
          (1 + (ρ : ℂ).im ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (actual_coshDefect_le u ρ) (Nat.cast_nonneg _))
        (by positivity)
    _ = _ := by ring

/-- Sharp domination retains the actual zero, multiplicity and fourth weight. -/
theorem regularizedTerm_le_horizontalTerm_sharp (u : ℝ) (ρ : ActualZero) :
    regularizedTerm u ρ ≤
      (4 * (Real.cosh (|u| / 2) - 1)) * horizontalTerm ρ := by
  unfold regularizedTerm horizontalTerm
  calc
    _ ≤ (zeroMult (ρ : ℂ) : ℝ) *
        ((4 * (Real.cosh (|u| / 2) - 1)) * ((ρ : ℂ).re - 1 / 2) ^ 2) /
          (1 + (ρ : ℂ).im ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (actual_coshDefect_le_sharp u ρ)
          (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by ring

theorem regularizedTerm_summable (u : ℝ) : Summable (regularizedTerm u) := by
  have hs := horizontalTerm_summable.mul_left (u ^ 2 * Real.exp (|u| / 2))
  exact Summable.of_nonneg_of_le (regularizedTerm_nonneg u)
    (regularizedTerm_le_horizontalTerm u) hs

/-- Absolutely convergent positive cosh mass over all actual nontrivial zeros. -/
def regularizedCoshMass (u : ℝ) : ℝ := ∑' ρ : ActualZero, regularizedTerm u ρ

theorem regularizedCoshMass_nonneg (u : ℝ) : 0 ≤ regularizedCoshMass u :=
  tsum_nonneg (regularizedTerm_nonneg u)

theorem regularizedCoshMass_le_fourthEnergy (u : ℝ) :
    regularizedCoshMass u ≤
      (u ^ 2 * Real.exp (|u| / 2)) * horizontalFourthEnergy := by
  have hs := horizontalTerm_summable.mul_left (u ^ 2 * Real.exp (|u| / 2))
  have h := (regularizedTerm_summable u).tsum_le_tsum
    (regularizedTerm_le_horizontalTerm u) hs
  simpa only [regularizedCoshMass, horizontalFourthEnergy, tsum_mul_left] using h

/-- Sharp upper control uses the already defined convergent actual-zero mass. -/
theorem regularizedCoshMass_le_fourthEnergy_sharp (u : ℝ) :
    regularizedCoshMass u ≤
      (4 * (Real.cosh (|u| / 2) - 1)) * horizontalFourthEnergy := by
  have hs := horizontalTerm_summable.mul_left (4 * (Real.cosh (|u| / 2) - 1))
  have h := (regularizedTerm_summable u).tsum_le_tsum
    (regularizedTerm_le_horizontalTerm_sharp u) hs
  simpa only [regularizedCoshMass, horizontalFourthEnergy, tsum_mul_left] using h

/-- Quantitative lower detection keeps the second Taylor term explicitly. -/
theorem half_sq_mul_horizontalTerm_le_regularizedTerm (u : ℝ) (ρ : ActualZero) :
    (u ^ 2 / 2) * horizontalTerm ρ ≤ regularizedTerm u ρ := by
  have h := Real.sq_div_two_le_cosh_sub_one (u * ((ρ : ℂ).re - 1 / 2))
  have hl : (u ^ 2 / 2) * ((ρ : ℂ).re - 1 / 2) ^ 2 ≤ coshDefect u (ρ : ℂ) := by
    unfold coshDefect
    nlinarith only [h]
  unfold regularizedTerm horizontalTerm
  calc
    _ = (zeroMult (ρ : ℂ) : ℝ) *
        ((u ^ 2 / 2) * ((ρ : ℂ).re - 1 / 2) ^ 2) /
          (1 + (ρ : ℂ).im ^ 2) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)) (by positivity)

/-- The convergent cosh mass and the existing E4 energy are comparable
without an analytic distribution premise. -/
theorem regularizedCoshMass_two_bounds (u : ℝ) :
    (u ^ 2 / 2) * horizontalFourthEnergy ≤ regularizedCoshMass u ∧
      regularizedCoshMass u ≤
        (u ^ 2 * Real.exp (|u| / 2)) * horizontalFourthEnergy := by
  refine ⟨?_, regularizedCoshMass_le_fourthEnergy u⟩
  have hs := horizontalTerm_summable.mul_left (u ^ 2 / 2)
  have h := hs.tsum_le_tsum
    (half_sq_mul_horizontalTerm_le_regularizedTerm u) (regularizedTerm_summable u)
  simpa only [regularizedCoshMass, horizontalFourthEnergy, tsum_mul_left] using h

/-- The sharp two-sided strip bound adds no analytic or RH premise. -/
theorem regularizedCoshMass_two_bounds_sharp (u : ℝ) :
    (u ^ 2 / 2) * horizontalFourthEnergy ≤ regularizedCoshMass u ∧
      regularizedCoshMass u ≤
        (4 * (Real.cosh (|u| / 2) - 1)) * horizontalFourthEnergy :=
  ⟨(regularizedCoshMass_two_bounds u).1,
    regularizedCoshMass_le_fourthEnergy_sharp u⟩

theorem regularizedTerm_le_mass (u : ℝ) (ρ : ActualZero) :
    regularizedTerm u ρ ≤ regularizedCoshMass u := by
  classical
  have h := (regularizedTerm_summable u).sum_le_tsum ({ρ} : Finset ActualZero)
    (fun σ _ => regularizedTerm_nonneg u σ)
  simpa only [Finset.sum_singleton, regularizedCoshMass] using h

theorem actual_on_line_of_regularizedCoshMass_zero {u : ℝ} (hu : u ≠ 0)
    (hE : regularizedCoshMass u = 0) (ρ : ActualZero) :
    (ρ : ℂ).re = 1 / 2 := by
  have ht := regularizedTerm_le_mass u ρ
  rw [hE] at ht
  have hden : 0 < (1 + (ρ : ℂ).im ^ 2) ^ 2 := by positivity
  change (zeroMult (ρ : ℂ) : ℝ) * coshDefect u (ρ : ℂ) /
    (1 + (ρ : ℂ).im ^ 2) ^ 2 ≤ 0 at ht
  have hnum := (div_le_iff₀ hden).mp ht
  simp only [zero_mul] at hnum
  have hm : (0 : ℝ) < (zeroMult (ρ : ℂ) : ℝ) := by
    have hmnat : 0 < zeroMult (ρ : ℂ) := zetaSeam.one_le_mult (ρ : ℂ) ρ.property
    exact_mod_cast hmnat
  have hd : coshDefect u (ρ : ℂ) ≤ 0 :=
    nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hnum) hm
  exact (coshDefect_eq_zero_iff hu (ρ : ℂ)).mp
    (le_antisymm hd (coshDefect_nonneg u (ρ : ℂ)))

/-- This actual all-zero criterion has no real-axis, density or RH premise. -/
theorem regularizedCoshMass_eq_zero_iff_RH {u : ℝ} (hu : u ≠ 0) :
    regularizedCoshMass u = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hE
    apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro s hz h0 h1
    exact actual_on_line_of_regularizedCoshMass_zero hu hE
      (⟨s, hz, h0, h1⟩ : ActualZero)
  · intro hRH
    have hterm : ∀ ρ : ActualZero, regularizedTerm u ρ = 0 := by
      intro ρ
      have hline := Zeta23.RH_implies_on_line hRH ρ.property
      simp [regularizedTerm, coshDefect, hline]
    simp only [regularizedCoshMass, hterm, tsum_zero]

end RiemannResearch.Analysis.ActualZeroCoshMass
end

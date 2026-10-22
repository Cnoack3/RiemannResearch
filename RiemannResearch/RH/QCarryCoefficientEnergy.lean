/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QConductorEscape
import RiemannResearch.RH.QExactHeadAverages
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.Analysis.WeakConvergenceDenseTests
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.InnerProductSpace.Basic
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Bounded Q energy with growing signed carry coefficients

Source: continuation of the user's coefficient-mass question, 19 October 2026.
The already established lower bound for a step carry is reused. Scaling by
the square root of its new multiplier accommodates growing coefficients and
bounded complete Q energy. This family is pointwise null, not an approximant
to one. It supplies no arithmetic estimate for growing signed carry blocks.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QResidueConditional
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative

/-- Upper bound paired with the existing lower bound for the unscaled carry. -/
theorem carry_norm_sq_upper (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) :
    ‖carry d p‖^2 ≤ 4 * ((p : ℝ) + 1) / (zetaTwo * (d : ℝ)) := by
  have hZ := zetaTwo_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hdp : 2 ≤ d * p := by nlinarith
  have hn := norm_sub_le ((p : ℝ) • qResidue (d * p)) (qResidue d)
  change ‖carry d p‖ ≤ _ at hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpR] at hn
  have hquad : ‖carry d p‖^2 ≤
      2 * (p : ℝ)^2 * ‖qResidue (d * p)‖^2 + 2 * ‖qResidue d‖^2 := by
    nlinarith [norm_nonneg (carry d p),
      norm_nonneg (qResidue (d * p)), norm_nonneg (qResidue d),
      sq_nonneg ((p : ℝ) * ‖qResidue (d * p)‖ - ‖qResidue d‖)]
  have ha := qResidue_norm_sq_le_two_div (d * p) hdp
  have hb := qResidue_norm_sq_le_two_div d hd
  calc
    _ ≤ 2 * (p : ℝ)^2 * ‖qResidue (d * p)‖^2 + 2 * ‖qResidue d‖^2 := hquad
    _ ≤ 2 * (p : ℝ)^2 * (2 / (zetaTwo * (d * p : ℕ))) +
        2 * (2 / (zetaTwo * (d : ℝ))) := by
      nlinarith only [mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2 * (p : ℝ)^2), hb]
    _ = _ := by
      push_cast
      field_simp [ne_of_gt hZ, ne_of_gt hdR, ne_of_gt hpR]
      ring

/-- A normalized signed packet; its two residue coefficients have sizes
sqrt(p) and 1/sqrt(p). -/
def normalizedCarry (d p : ℕ) : QHilbert := (Real.sqrt (p : ℝ))⁻¹ • carry d p

theorem normalizedCarry_eq (d p : ℕ) (hp : 0 < p) :
    normalizedCarry d p = Real.sqrt (p : ℝ) • qResidue (d * p) -
      (Real.sqrt (p : ℝ))⁻¹ • qResidue d := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs := Real.sq_sqrt hpR.le
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpR)
  have he : (Real.sqrt (p : ℝ))⁻¹ * (p : ℝ) = Real.sqrt (p : ℝ) := by
    field_simp [hs0]
    nlinarith only [hs]
  simp only [normalizedCarry, carry, smul_sub, smul_smul, he]

theorem normalizedCarry_norm_sq (d p : ℕ) :
    ‖normalizedCarry d p‖^2 = ‖carry d p‖^2 / (p : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  rw [normalizedCarry, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, hs]
  ring

/-- Growing square-root coefficient mass is compatible with bounded physical
energy. The positive lower bound shows that this is not strong convergence to zero. -/
theorem normalizedCarry_energy_bounds (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) :
    ((p - 1 : ℕ) : ℝ) / (zetaTwo * (d : ℝ)^2 * (p : ℝ)) ≤
        ‖normalizedCarry d p‖^2 ∧
      ‖normalizedCarry d p‖^2 ≤ 8 / (zetaTwo * (d : ℝ)) := by
  have hZ := zetaTwo_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [normalizedCarry_norm_sq]
  constructor
  · simpa only [div_div] using
      div_le_div_of_nonneg_right (carry_norm_sq_lower d p (by omega)) hpR.le
  · apply (div_le_iff₀ hpR).mpr
    apply (carry_norm_sq_upper d p hd hp).trans
    apply (div_le_iff₀ (by positivity : 0 < zetaTwo * (d : ℝ))).mpr
    have he : (8 / (zetaTwo * (d : ℝ)) * (p : ℝ)) *
        (zetaTwo * (d : ℝ)) = 8 * (p : ℝ) := by
      field_simp
    rw [he]
    linarith

/-- Squarefreeness is only needed for legal membership, not for the energy bounds. -/
theorem normalizedCarry_mem_squarefreeSpan (d p : ℕ) (hd : 0 < d) (hp : 0 < p)
    (hsf : Squarefree (d * p)) : normalizedCarry d p ∈ qSquarefreeCRTSpan := by
  apply qSquarefreeCRTSpan.smul_mem
  exact QSquarefreeLatticePackets.divisorStage_le_squarefreeSpan (d * p)
    (Nat.mul_pos hd hp) hsf (carry_mem_divisorStage d d p (dvd_refl d))

/-- Despite bounded energy and growing coefficients, every fixed physical
coordinate of the normalized carry tends to zero. -/
theorem normalizedCarry_pointwise_tendsto_zero (d : ℕ) (hd : 0 < d)
    (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) (n : ℕ) :
    Tendsto (fun j => qSequence (normalizedCarry d (p j)) n) atTop (𝓝 0) := by
  have hi : Tendsto (fun j => (Real.sqrt (p j : ℝ))⁻¹) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hp)
    simpa only [Function.comp_def, one_div, Real.sqrt_inv, Real.sqrt_zero] using ht
  have ht := hi.const_mul ((n / d : ℕ) : ℝ)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [hp.eventually (eventually_gt_atTop (n / d)),
    hp.eventually (eventually_gt_atTop 0)] with j hj hjpos
  change _ = qSequenceLinear ((Real.sqrt (p j : ℝ))⁻¹ • carry d (p j)) n
  rw [map_smul]
  change _ = (Real.sqrt (p j : ℝ))⁻¹ * qSequence (carry d (p j)) n
  rw [carry_sequence d (p j) n hd hjpos, Nat.mod_eq_of_lt hj]
  ring

/-- All continuous physical pairings vanish for the bounded normalized carries. -/
theorem normalizedCarry_weak_tendsto_zero (d : ℕ) (hd : 2 ≤ d)
    (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) (hpos : ∀ j, 1 ≤ p j)
    (x : QHilbert) :
    Tendsto (fun j => inner ℝ x (normalizedCarry d (p j))) atTop (𝓝 0) := by
  have hZ := zetaTwo_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hB : 0 ≤ 8 / (zetaTwo * (d : ℝ)) := by positivity
  have hb : ∀ j, ‖normalizedCarry d (p j)‖ ≤ 8 / (zetaTwo * (d : ℝ)) + 1 := by
    intro j
    have he := (normalizedCarry_energy_bounds d (p j) hd (hpos j)).2
    nlinarith [norm_nonneg (normalizedCarry d (p j)),
      sq_nonneg (‖normalizedCarry d (p j)‖ - 1)]
  apply RiemannResearch.Analysis.tendsto_inner_zero_of_mem_closure_span
    (by positivity : 0 ≤ 8 / (zetaTwo * (d : ℝ)) + 1)
    (Filter.Eventually.of_forall hb) _
    (by rw [QExactHeadAverages.qPoint_span_dense]; trivial)
  rintro y ⟨n, rfl⟩
  simpa only [qPoint_inner, mul_zero] using
    (normalizedCarry_pointwise_tendsto_zero d (by omega) p hp (n + 1)).const_mul
      (qWeight n)

/-- Exact signed error accounting rules out interpreting the bounded packets
as approximants to one: their error minus their own energy tends to one. -/
theorem normalizedCarry_error_minus_energy_tendsto_one (d : ℕ) (hd : 2 ≤ d)
    (p : ℕ → ℕ) (hp : Tendsto p atTop atTop) (hpos : ∀ j, 1 ≤ p j) :
    Tendsto (fun j => ‖qOne - normalizedCarry d (p j)‖^2 -
      ‖normalizedCarry d (p j)‖^2) atTop (𝓝 1) := by
  have ht := (normalizedCarry_weak_tendsto_zero d hd p hp hpos qOne).const_mul 2
  have hh := ht.const_sub 1
  simp only [mul_zero, sub_zero] at hh
  convert hh using 1
  funext j
  rw [norm_sub_sq_real, qOne_norm_sq]
  ring

/-- When the base conductor also escapes, this extra scaling gives bounded
energy with both conductors escaping and coefficient mass of order sqrt(d)
for a fixed multiplier p>1. -/
theorem scaled_normalizedCarry_norm_sq_upper (d p : ℕ) (hd : 2 ≤ d)
    (hp : 1 ≤ p) :
    ‖Real.sqrt (d : ℝ) • normalizedCarry d p‖^2 ≤ 8 / zetaTwo := by
  have hZ := zetaTwo_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hdR.le]
  calc
    _ ≤ (d : ℝ) * (8 / (zetaTwo * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left (normalizedCarry_energy_bounds d p hd hp).2 hdR.le
    _ = _ := by field_simp

theorem normalizedCarry_mem_tailSpan (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) :
    normalizedCarry d p ∈ qConductorTailSpan (d - 1) := by
  have hdd : d - 1 < d := by omega
  have hdp : d - 1 < d * p := by nlinarith
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d * p, hdp, rfl⟩)
  · exact Submodule.subset_span ⟨d, hdd, rfl⟩

/-- Bounded-energy, signed, all-escaping packets still have zero weak limit.
This reuses the existing general conductor-escape theorem. -/
theorem scaled_normalizedCarry_weak_tendsto_zero (d : ℕ → ℕ)
    (hd : Tendsto d atTop atTop) (hd2 : ∀ j, 2 ≤ d j)
    (p : ℕ) (hp : 1 ≤ p) (x : QHilbert) :
    Tendsto (fun j => inner ℝ x (Real.sqrt (d j : ℝ) • normalizedCarry (d j) p))
      atTop (𝓝 0) := by
  have hZ := zetaTwo_pos
  have hb : ∀ j, ‖Real.sqrt (d j : ℝ) • normalizedCarry (d j) p‖ ≤
      8 / zetaTwo + 1 := by
    intro j
    have he := scaled_normalizedCarry_norm_sq_upper (d j) p (hd2 j) hp
    nlinarith [norm_nonneg (Real.sqrt (d j : ℝ) • normalizedCarry (d j) p),
      sq_nonneg (‖Real.sqrt (d j : ℝ) • normalizedCarry (d j) p‖ - 1)]
  exact qConductorTailSpan_weak_tendsto_zero
    (fun j => Real.sqrt (d j : ℝ) • normalizedCarry (d j) p)
    (fun j => d j - 1) ((tendsto_sub_atTop_nat 1).comp hd)
    (fun j => by have := hd2 j; omega)
    (fun j => Submodule.smul_mem _ _ (normalizedCarry_mem_tailSpan (d j) p (hd2 j) hp))
    (8 / zetaTwo + 1) (by positivity) hb x

end RiemannResearch.RH.QResidueConditional

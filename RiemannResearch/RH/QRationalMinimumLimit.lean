/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QRationalWeightComparison
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTReciprocalEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual rational minima converge to the complete-Q limiting defect

Source: user-provided RH/CRT research handoff, 20 October 2026, Section 8;
the fixed-competitor variational argument is developed here.

The rational minimizer exists by the actual divisor normal equations. Its
exact excess over the Q minimum is a projection-displacement square plus
the nonnegative rational weight gap. For the upper limit, one fixes a
single earlier Q optimizer before letting the representation period grow.
Consequently no bound on the coefficients of the moving rational optimizer
and no convergence of its weight gap is assumed.

The limit is zeta(2) times the squared distance to the closed squarefree
legal span. This identifies the limiting value; it does not assert that
the distance is zero.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QRationalCoprimeTail
open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability
open QSquarefreePrimorialCofinality QSquarefreeInverseCapacity
open Pareto.SquarefreeStageExhaustion

/-- The actual QHilbert vector belonging to a finite divisor synthesis. -/
def qDivisorFit (L : ℕ) (c : ℕ → ℝ) : QHilbert :=
  ∑ d ∈ L.divisors, c d • qResidue d

def qDivisorLinear (L : ℕ) : (ℕ → ℝ) →ₗ[ℝ] QHilbert where
  toFun := qDivisorFit L
  map_add' c b := by
    simp [qDivisorFit, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [qDivisorFit, mul_smul, Finset.smul_sum]

theorem qSequence_qDivisorFit (L : ℕ) (c : ℕ → ℝ) :
    qSequence (qDivisorFit L c) = divisorFit L c := by
  change qSequenceLinear (∑ d ∈ L.divisors, c d • qResidue d) = _
  simp only [map_sum, map_smul]
  ext k
  simp [qSequenceLinear, qSequence_qResidue, divisorFit]

theorem divisorFit_periodic (L : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    divisorFit L c (k + L) = divisorFit L c k := by
  unfold divisorFit
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  unfold residueFraction
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd),
    add_zero, Nat.mod_mod]

/-- An explicit bound for each fixed finite synthesis. -/
theorem divisorFit_abs_le (L : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    |divisorFit L c k| ≤ ∑ d ∈ L.divisors, |c d| := by
  unfold divisorFit
  calc
    |∑ d ∈ L.divisors, c d * residueFraction d k| ≤
        ∑ d ∈ L.divisors, |c d * residueFraction d k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ L.divisors, |c d| := by
      apply Finset.sum_le_sum
      intro d hd
      have hr : |residueFraction d k| ≤ 1 := by
        by_cases hd0 : d = 0
        · simp [hd0, residueFraction]
        · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
          have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
          unfold residueFraction
          rw [abs_of_nonneg (by positivity)]
          apply (div_le_iff₀ hdR).mpr
          simpa only [one_mul] using
            (show ((k % d : ℕ) : ℝ) ≤ (d : ℝ) by
              exact_mod_cast (Nat.mod_lt k hdpos).le)
      rw [abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hr (abs_nonneg (c d))

theorem divisorFit_residual_bound (L : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    |1 - divisorFit L c k| ≤ 1 + ∑ d ∈ L.divisors, |c d| := by
  calc
    |1 - divisorFit L c k| ≤ 1 + |divisorFit L c k| := by
      simpa [sub_eq_add_neg] using abs_add_le (1 : ℝ) (-divisorFit L c k)
    _ ≤ _ := add_le_add (le_refl _) (divisorFit_abs_le L c k)

/-- The exact finite dictionary agrees with the Q primorial stage. -/
theorem qDivisorLinear_range_eq_primorialStage (n : ℕ) :
    LinearMap.range (qDivisorLinear (primorialPeriod n)) = primorialStage n := by
  classical
  apply le_antisymm
  · rintro f ⟨c, rfl⟩
    change qDivisorFit (primorialPeriod n) c ∈ primorialStage n
    unfold qDivisorFit
    apply Submodule.sum_mem
    intro d hd
    apply Submodule.smul_mem
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hdvd : d ∣ primorialPeriod n := Nat.dvd_of_mem_divisors hd
      have hd0 : d ≠ 0 := by
        intro he
        subst d
        have hzero : primorialPeriod n = 0 := Nat.eq_zero_of_zero_dvd hdvd
        exact (ne_of_gt (primorialPeriod_pos n)) hzero
      exact Submodule.subset_span ⟨d, by omega, hdvd, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, hdvd, rfl⟩
    have hdmem : d ∈ (primorialPeriod n).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd, ne_of_gt (primorialPeriod_pos n)⟩
    refine ⟨fun k => if k = d then 1 else 0, ?_⟩
    change qDivisorFit (primorialPeriod n) (fun k => if k = d then 1 else 0) = _
    simp [qDivisorFit, hdmem]

theorem exists_qDivisorFit_of_mem {n : ℕ} {f : QHilbert}
    (hf : f ∈ primorialStage n) :
    ∃ c : ℕ → ℝ, qDivisorFit (primorialPeriod n) c = f := by
  rw [← qDivisorLinear_range_eq_primorialStage] at hf
  exact hf

theorem qSequence_periodic_of_mem {n : ℕ} {f : QHilbert}
    (hf : f ∈ primorialStage n) (k : ℕ) :
    qSequence f (k + primorialPeriod n) = qSequence f k := by
  obtain ⟨c, rfl⟩ := exists_qDivisorFit_of_mem hf
  simp only [qSequence_qDivisorFit]
  exact divisorFit_periodic _ c k

theorem qSequence_bounded_of_mem {n : ℕ} {f : QHilbert}
    (hf : f ∈ primorialStage n) :
    ∃ C : ℝ, ∀ k, |qSequence f k| ≤ C := by
  obtain ⟨c, rfl⟩ := exists_qDivisorFit_of_mem hf
  refine ⟨∑ d ∈ (primorialPeriod n).divisors, |c d|, ?_⟩
  intro k
  rw [qSequence_qDivisorFit]
  exact divisorFit_abs_le _ c k

/-- A selected actual solution of all finite divisor normal equations. -/
def rationalCoefficients (L : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_divisor_normal L)

theorem rationalCoefficients_normal (L : ℕ) :
    ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a *
        (1 - divisorFit L (rationalCoefficients L) a) * residueFraction d a) = 0 :=
  Classical.choose_spec (exists_divisor_normal L)

def rationalMinimizer (L : ℕ) : QHilbert :=
  qDivisorFit L (rationalCoefficients L)

def rationalMinimum (L : ℕ) : ℝ :=
  rationalError L (divisorFit L (rationalCoefficients L))

theorem rationalMinimum_le (L : ℕ) (c : ℕ → ℝ) :
    rationalMinimum L ≤ rationalError L (divisorFit L c) := by
  have he := divisorFit_completion L (rationalCoefficients L) c
    (rationalCoefficients_normal L)
  have hn : 0 ≤ ∑ a ∈ sites L, weight L a *
      (divisorFit L c a - divisorFit L (rationalCoefficients L) a)^2 := by
    apply Finset.sum_nonneg
    intro a ha
    apply mul_nonneg
    · unfold weight
      positivity
    · exact sq_nonneg _
  unfold rationalMinimum
  linarith

theorem rationalMinimum_le_of_mem {n : ℕ} {f : QHilbert}
    (hf : f ∈ primorialStage n) :
    rationalMinimum (primorialPeriod n) ≤
      rationalError (primorialPeriod n) (qSequence f) := by
  obtain ⟨c, rfl⟩ := exists_qDivisorFit_of_mem hf
  rw [qSequence_qDivisorFit]
  exact rationalMinimum_le _ c

theorem rationalMinimizer_mem (n : ℕ) :
    rationalMinimizer (primorialPeriod n) ∈ primorialStage n := by
  rw [← qDivisorLinear_range_eq_primorialStage]
  exact ⟨rationalCoefficients (primorialPeriod n), rfl⟩

/-- Exact projection excess, preserving the displacement square. -/
theorem primorial_qError_exact {n : ℕ} {f : QHilbert}
    (hf : f ∈ primorialStage n) :
    ‖qOne - f‖^2 = primorialError n + ‖f - primorialOptimizer n‖^2 := by
  have hp : primorialOptimizer n ∈ primorialStage n :=
    (primorialStage n).starProjection_apply_mem qOne
  have ho' : inner ℝ (qOne - primorialOptimizer n)
      (f - primorialOptimizer n) = 0 :=
    Submodule.starProjection_inner_eq_zero (K := primorialStage n) qOne
      (f - primorialOptimizer n) ((primorialStage n).sub_mem hf hp)
  rw [show qOne - f =
    (qOne - primorialOptimizer n) - (f - primorialOptimizer n) by abel]
  rw [norm_sub_sq_real, ho']
  unfold primorialError
  ring

/-- The rational minimum differs from the true Q minimum by two explicit
nonnegative terms; neither term has been discarded from the identity. -/
theorem rationalMinimum_exact (n : ℕ) :
    rationalMinimum (primorialPeriod n) =
      zetaTwo * primorialError n +
        zetaTwo * ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2 +
        rationalGap (primorialPeriod n)
          (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n))) := by
  let L := primorialPeriod n
  let c := rationalCoefficients L
  have he := rationalError_exact_gap L (primorialPeriod_pos n) (divisorFit L c)
    (divisorFit_residual_bound L c) (divisorFit_periodic L c)
  simp_rw [← qSequence_qDivisorFit L c] at he
  rw [← qError_eq_inversePowerMean] at he
  have hm : qDivisorFit L c ∈ primorialStage n := rationalMinimizer_mem n
  rw [primorial_qError_exact hm] at he
  simp only [qSequence_qDivisorFit] at he
  change rationalMinimum (primorialPeriod n) = _
  change rationalError L (divisorFit L c) = _
  rw [he]
  change zetaTwo * (primorialError n +
      ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖^2) + _ = _
  ring

theorem rationalMinimum_lower (n : ℕ) :
    zetaTwo * primorialError n ≤ rationalMinimum (primorialPeriod n) := by
  rw [rationalMinimum_exact]
  have hg := (rationalGap_bounds (primorialPeriod n) (primorialPeriod_pos n)
    (divisorFit (primorialPeriod n) (rationalCoefficients (primorialPeriod n)))
    (divisorFit_residual_bound _ _)).1
  have hs := mul_nonneg zetaTwo_pos.le
    (sq_nonneg ‖rationalMinimizer (primorialPeriod n) - primorialOptimizer n‖)
  linarith

/-- Unconditional convergence of the attained rational minima to zeta(2)
times the actual squared distance to the closed squarefree legal span. -/
theorem rationalMinimum_tendsto :
    Tendsto (fun n => rationalMinimum (primorialPeriod n)) atTop
      (𝓝 (zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2)) := by
  have ht : Tendsto (fun n => zetaTwo * primorialError n) atTop
      (𝓝 (zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2)) :=
    tendsto_const_nhds.mul primorialError_tendsto
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [ht.eventually (Ioi_mem_nhds ha)] with n hn
    exact hn.trans_le (rationalMinimum_lower n)
  · intro b hb
    obtain ⟨m, hm⟩ := (ht.eventually (Iio_mem_nhds hb)).exists
    have hmem : primorialOptimizer m ∈ primorialStage m :=
      (primorialStage m).starProjection_apply_mem qOne
    obtain ⟨C, hC⟩ := qSequence_bounded_of_mem hmem
    let B : ℝ := 1 + C
    have hB (k : ℕ) : |1 - qSequence (primorialOptimizer m) k| ≤ B := by
      calc
        |1 - qSequence (primorialOptimizer m) k| ≤
            1 + |qSequence (primorialOptimizer m) k| := by
          simpa [sub_eq_add_neg] using
            abs_add_le (1 : ℝ) (-qSequence (primorialOptimizer m) k)
        _ ≤ B := add_le_add (le_refl _) (hC k)
    have hgap : 0 < b - zetaTwo * primorialError m := sub_pos.mpr hm
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * B^2 / (b - zetaTwo * primorialError m))
    filter_upwards [eventually_ge_atTop m, eventually_ge_atTop N] with n hmn hNn
    have hmemn : primorialOptimizer m ∈ primorialStage n :=
      primorialStage_mono hmn hmem
    have hu := rationalError_fixed_competitor_bound (primorialPeriod n)
      (primorialPeriod_pos n) (qSequence (primorialOptimizer m)) hB
      (qSequence_periodic_of_mem hmemn)
    rw [← qError_eq_inversePowerMean] at hu
    change rationalError (primorialPeriod n) (qSequence (primorialOptimizer m)) ≤
      zetaTwo * primorialError m + 2 * B^2 / (primorialPeriod n : ℝ) at hu
    have hNL : N ≤ primorialPeriod n :=
      hNn.trans ((Nat.le_add_right n 3).trans le_primorial_self)
    have hNLR : (N : ℝ) ≤ primorialPeriod n := by exact_mod_cast hNL
    have hLR : (0 : ℝ) < primorialPeriod n := by
      exact_mod_cast primorialPeriod_pos n
    have hsmall : 2 * B^2 / (primorialPeriod n : ℝ) <
        b - zetaTwo * primorialError m := by
      apply (div_lt_iff₀ hLR).mpr
      have hmul := (div_lt_iff₀ hgap).mp (hN.trans_le hNLR)
      nlinarith
    exact lt_of_le_of_lt ((rationalMinimum_le_of_mem hmemn).trans hu) (by linarith)

/-- Vanishing of the actual rational minima is exactly the remaining
squarefree-closure obligation, with no surrogate convergence hypothesis. -/
theorem rationalMinimum_tendsto_zero_iff :
    Tendsto (fun n => rationalMinimum (primorialPeriod n)) atTop (𝓝 0) ↔
      qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro hzero
    have he := tendsto_nhds_unique rationalMinimum_tendsto hzero
    have hz : ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2 = 0 :=
      (mul_eq_zero.mp he).resolve_left (ne_of_gt zetaTwo_pos)
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm,
      Submodule.starProjection_eq_self_iff] at hz
    exact hz
  · intro hmem
    have he : zetaTwo * ‖qOne -
        qSquarefreeCRTSpan.topologicalClosure.starProjection qOne‖^2 = 0 := by
      rw [Submodule.starProjection_eq_self_iff.mpr hmem, sub_self, norm_zero]
      ring
    simpa only [he] using rationalMinimum_tendsto

end RiemannResearch.RH.QRationalCoprimeTail

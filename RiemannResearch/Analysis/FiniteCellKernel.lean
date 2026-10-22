/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-!
# Exact finite-cell kernel integrals
Integration, quadratic reconstruction, and cancellation of separated anchor terms
for real continuous kernels. Cell coefficients add on overlaps; disjointness
is not needed. Every integrability claim used in reconstruction is proved.

RH consumer: RiemannResearch.RH.FiniteDyadicCellKernel.
Source: user-provided handoff v15 and RH_Proof_First_Continuation_2026-09-04.md,
Section 5, support the cell-compression strategy. The anchored-kernel convention
is Suzuki, Aspects of the screw function corresponding to the Riemann
zeta-function (2023), equation (1.4), https://arxiv.org/abs/2206.03682.
No arithmetic kernel identification, positivity, density, or RH is asserted.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RiemannResearch.Analysis
noncomputable section

/-- A finite real step function, with cell coefficients added on overlaps. -/
def finiteCellStep {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (Ioc (a i) (b i)).indicator (fun _ => c i) x

@[fun_prop]
theorem measurable_finiteCellStep {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) :
    Measurable (finiteCellStep a b c) := by
  classical
  unfold finiteCellStep
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.indicator measurableSet_Ioc

theorem integrable_mul_finiteCellStep {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (fun x => f x * finiteCellStep a b c x) := by
  classical
  unfold finiteCellStep
  simp_rw [Finset.mul_sum, ← Set.indicator_mul_right]
  apply integrable_finsetSum
  intro i hi
  exact (hf.mul continuous_const).integrableOn_Ioc.integrable_indicator measurableSet_Ioc

/-- A finite-cell step is globally bounded, even when its cells overlap. -/
theorem norm_finiteCellStep_le {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (x : ℝ) :
    ‖finiteCellStep a b c x‖ ≤ ∑ i, ‖c i‖ := by
  classical
  unfold finiteCellStep
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : x ∈ Ioc (a i) (b i)
  · simp [hx]
  · simp [hx]

/-- Square integrability of a finite step, without a disjoint-cell hypothesis. -/
theorem integrable_finiteCellStep_sq {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) :
    Integrable (fun x => (finiteCellStep a b c x) ^ 2) := by
  have hu : Integrable (finiteCellStep a b c) := by
    simpa using integrable_mul_finiteCellStep a b c (fun _ => 1) continuous_const
  simpa only [pow_two] using
    hu.mul_bdd (measurable_finiteCellStep a b c).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_finiteCellStep_le a b c))

theorem integral_mul_finiteCellStep {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f x * finiteCellStep a b c x) =
      ∑ i, c i * (∫ x in a i..b i, f x) := by
  classical
  unfold finiteCellStep
  simp_rw [Finset.mul_sum, ← Set.indicator_mul_right]
  have hI (i : ι) : Integrable
      ((Ioc (a i) (b i)).indicator (fun x => f x * c i)) :=
    (hf.mul continuous_const).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (hab i), intervalIntegral.integral_mul_const]
  exact mul_comm _ _

theorem continuous_finiteCellKernel_transform {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k)) :
    Continuous (fun x => ∫ y, k x y * finiteCellStep a b c y) := by
  have hs (x : ℝ) : Continuous (k x) :=
    hk.comp (continuous_const.prodMk continuous_id)
  simp_rw [integral_mul_finiteCellStep a b c hab _ (hs _)]
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk (a j) (b j))

/-- Both stages of the kernel integral exist as genuine integrable functions. -/
theorem finiteCellKernel_integrable {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k)) :
    (∀ x, Integrable (fun y => k x y * finiteCellStep a b c y)) ∧
      Integrable (fun x => finiteCellStep a b c x *
        (∫ y, k x y * finiteCellStep a b c y)) := by
  constructor
  · intro x
    exact integrable_mul_finiteCellStep a b c (k x)
      (hk.comp (continuous_const.prodMk continuous_id))
  · simpa only [mul_comm] using
      integrable_mul_finiteCellStep a b c
        (fun x => ∫ y, k x y * finiteCellStep a b c y)
        (continuous_finiteCellKernel_transform a b c hab k hk)

/-- The actual iterated kernel integral of a finite step function is the
quadratic expression in exact cell integrals. No positivity or symmetry is
assumed of the continuous kernel. -/
theorem finiteCellKernel_quadratic_reconstruction {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k)) :
    (∫ x, finiteCellStep a b c x *
      (∫ y, k x y * finiteCellStep a b c y)) =
      ∑ i, ∑ j, c i *
        (∫ x in a i..b i, ∫ y in a j..b j, k x y) * c j := by
  have hs (x : ℝ) : Continuous (k x) :=
    hk.comp (continuous_const.prodMk continuous_id)
  have ht := continuous_finiteCellKernel_transform a b c hab k hk
  calc
    _ = ∑ i, c i *
        (∫ x in a i..b i, ∫ y, k x y * finiteCellStep a b c y) := by
      simpa only [mul_comm] using
        integral_mul_finiteCellStep a b c hab
          (fun x => ∫ y, k x y * finiteCellStep a b c y) ht
    _ = _ := by
      simp_rw [integral_mul_finiteCellStep a b c hab _ (hs _)]
      apply Finset.sum_congr rfl
      intro i hi
      have hI (j : ι) : IntervalIntegrable
          (fun x => c j * (∫ y in a j..b j, k x y)) volume (a i) (b i) :=
        (continuous_const.mul
          (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
            hk (a j) (b j))).intervalIntegrable (a i) (b i)
      rw [intervalIntegral.integral_finsetSum (fun j _ => hI j)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring



/-- Separated one-variable terms vanish in a mean-zero cell quadratic form.
This does not remove a term depending on x-y, such as |x-y|. -/
theorem finiteCellKernel_gauge_invariant {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (k : ℝ → ℝ → ℝ) (hk : Continuous (Function.uncurry k))
    (f h : ℝ → ℝ) (hh : Continuous h)
    (hzero : (∫ x, finiteCellStep a b c x) = 0) :
    (∫ x, finiteCellStep a b c x *
      (∫ y, (k x y + f x + h y) * finiteCellStep a b c y)) =
    (∫ x, finiteCellStep a b c x *
      (∫ y, k x y * finiteCellStep a b c y)) := by
  let u := finiteCellStep a b c
  have hu : Integrable u := by
    simpa only [one_mul] using
      integrable_mul_finiteCellStep a b c (fun _ => (1 : ℝ)) continuous_const
  have hku (x : ℝ) : Integrable (fun y => k x y * u y) :=
    integrable_mul_finiteCellStep a b c (k x)
      (hk.comp (continuous_const.prodMk continuous_id))
  have hhu : Integrable (fun y => h y * u y) :=
    integrable_mul_finiteCellStep a b c h hh
  have hx (x : ℝ) :
      (∫ y, (k x y + f x + h y) * u y) =
      (∫ y, k x y * u y) + (∫ y, h y * u y) := by
    simp_rw [add_mul]
    have hsum : Integrable (fun y => k x y * u y + f x * u y) :=
      (hku x).add (hu.const_mul (f x))
    rw [integral_add hsum hhu,
      integral_add (hku x) (hu.const_mul (f x)), integral_const_mul]
    change _ + f x * (∫ y, finiteCellStep a b c y) + _ = _
    rw [hzero, mul_zero, add_zero]
  change (∫ x, u x * (∫ y, (k x y + f x + h y) * u y)) = _
  simp_rw [hx, mul_add]
  have houter : Integrable (fun x => u x * (∫ y, k x y * u y)) :=
    (finiteCellKernel_integrable a b c hab k hk).2
  rw [integral_add houter (hu.mul_const _), integral_mul_const]
  change _ + (∫ x, finiteCellStep a b c x) * _ = _
  rw [hzero, zero_mul, add_zero]

/-- The anchored screw kernel has exactly the convolution quadratic form on
mean-zero finite cell steps. The arithmetic choice of g is a separate obligation. -/
theorem finiteCellKernel_screw_reconstruction {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hzero : (∫ x, finiteCellStep a b c x) = 0) :
    (∫ x, finiteCellStep a b c x *
      (∫ y, (g (x-y) - g x - g (-y) + g 0) * finiteCellStep a b c y)) =
    (∫ x, finiteCellStep a b c x *
      (∫ y, g (x-y) * finiteCellStep a b c y)) := by
  have h := finiteCellKernel_gauge_invariant a b c hab
    (fun x y => g (x-y)) (hg.comp (continuous_fst.sub continuous_snd))
    (fun x => -g x) (fun y => -g (-y) + g 0)
    ((hg.comp continuous_neg).neg.add continuous_const) hzero
  simpa only [sub_eq_add_neg, add_assoc] using h
end
end RiemannResearch.Analysis

namespace RiemannResearch.Analysis
open MeasureTheory Set
noncomputable section

theorem norm_integral_integral_le {k : ℝ → ℝ → ℝ} {a b c d C : ℝ}
    (h : ∀ x ∈ uIoc a b, ∀ y ∈ uIoc c d, ‖k x y‖ ≤ C) :
    ‖∫ x in a..b, ∫ y in c..d, k x y‖ ≤ C * |d-c| * |b-a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  exact intervalIntegral.norm_integral_le_of_norm_le_const (h x hx)

theorem integral_integral_sub {k l : ℝ → ℝ → ℝ}
    (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l))
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, k x y) -
      (∫ x in a..b, ∫ y in c..d, l x y) =
      ∫ x in a..b, ∫ y in c..d, k x y-l x y := by
  have hki (x : ℝ) : IntervalIntegrable (k x) volume c d :=
    (hk.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d
  have hli (x : ℝ) : IntervalIntegrable (l x) volume c d :=
    (hl.comp (continuous_const.prodMk continuous_id)).intervalIntegrable c d
  have hko : IntervalIntegrable (fun x => ∫ y in c..d, k x y) volume a b :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hk c d).intervalIntegrable a b
  have hlo : IntervalIntegrable (fun x => ∫ y in c..d, l x y) volume a b :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hl c d).intervalIntegrable a b
  simp_rw [intervalIntegral.integral_sub (hki _) (hli _)]
  exact (intervalIntegral.integral_sub hko hlo).symm

/-- Subtract actual quadratic integrals only after proving both integrabilities. -/
theorem finiteCellKernel_quadratic_sub {ι : Type*} [Fintype ι]
    (a b c : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (k l : ℝ → ℝ → ℝ)
    (hk : Continuous (Function.uncurry k)) (hl : Continuous (Function.uncurry l)) :
    (∫ x, finiteCellStep a b c x * (∫ y, k x y * finiteCellStep a b c y)) -
      (∫ x, finiteCellStep a b c x * (∫ y, l x y * finiteCellStep a b c y)) =
    (∫ x, finiteCellStep a b c x *
      (∫ y, (k x y - l x y) * finiteCellStep a b c y)) := by
  have hki := finiteCellKernel_integrable a b c hab k hk
  have hli := finiteCellKernel_integrable a b c hab l hl
  symm
  simp_rw [sub_mul, integral_sub (hki.1 _) (hli.1 _), mul_sub]
  exact integral_sub hki.2 hli.2

end
end RiemannResearch.Analysis

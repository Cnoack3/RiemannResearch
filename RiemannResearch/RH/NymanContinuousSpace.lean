import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The actual continuous Nyman--Beurling space

Source: J.-F. Burnol, A note on Nyman's equivalent formulation of the
Riemann Hypothesis, Section 1, https://arxiv.org/pdf/math/9910055.

The generators are actual fractional-part functions in complex L²((0,1)).
Their closed linear span is constructed directly. The dilation identity
is proved pointwise, without a Mellin-transform assumption. This module
does not assert the still-missing Hardy invariant-subspace identification.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.RH.Burnol.ContinuousNyman

abbrev intervalMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
abbrev Hilbert := Lp ℂ 2 intervalMeasure

def realGenerator (α t : ℝ) : ℝ := Int.fract (α / t) - α * Int.fract (1 / t)
def generatorFunction (α t : ℝ) : ℂ := (realGenerator α t : ℂ)

theorem realGenerator_measurable (α : ℝ) : Measurable (realGenerator α) := by
  exact (measurable_const.div measurable_id).fract.sub
    (measurable_const.mul (measurable_const.div measurable_id).fract)

theorem generatorFunction_measurable (α : ℝ) : Measurable (generatorFunction α) :=
  Complex.continuous_ofReal.measurable.comp (realGenerator_measurable α)

theorem realGenerator_abs_le (α t : ℝ) : |realGenerator α t| ≤ 1 + |α| := by
  calc
    |realGenerator α t| ≤ |Int.fract (α / t)| + |α * Int.fract (1 / t)| := by
      simpa only [realGenerator, Real.norm_eq_abs] using
        norm_sub_le (Int.fract (α / t)) (α * Int.fract (1 / t))
    _ = Int.fract (α / t) + |α| * Int.fract (1 / t) := by
      rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (α / t)),
        abs_of_nonneg (Int.fract_nonneg (1 / t))]
    _ ≤ 1 + |α| := by
      have h1 := (Int.fract_lt_one (α / t)).le
      have h2 := mul_le_mul_of_nonneg_left (Int.fract_lt_one (1 / t)).le (abs_nonneg α)
      nlinarith

theorem generatorFunction_norm_le (α t : ℝ) : ‖generatorFunction α t‖ ≤ 1 + |α| := by
  simpa only [generatorFunction, Complex.norm_real, Real.norm_eq_abs] using
    realGenerator_abs_le α t

theorem generatorFunction_memLp (α : ℝ) : MemLp (generatorFunction α) 2 intervalMeasure :=
  MemLp.of_bound (generatorFunction_measurable α).aestronglyMeasurable
    (1 + |α|) (Filter.Eventually.of_forall (generatorFunction_norm_le α))

def generator (α : ℝ) : Hilbert :=
  (generatorFunction_memLp α).toLp (generatorFunction α)

theorem generator_ae (α : ℝ) :
    (generator α : ℝ → ℂ) =ᵐ[intervalMeasure] generatorFunction α :=
  MemLp.coeFn_toLp _

/-- Away from the countable family of floor jumps, convergence of dilation
parameters gives pointwise convergence of the corresponding generators. -/
theorem generatorFunction_ae_tendsto
    {a : ℕ → ℝ} {α : ℝ} (hα : α ≠ 0)
    (ha : Filter.Tendsto a Filter.atTop (nhds α)) :
    ∀ᵐ t ∂intervalMeasure,
      Filter.Tendsto (fun n => generatorFunction (a n) t) Filter.atTop
        (nhds (generatorFunction α t)) := by
  have hinj : Function.Injective (fun t : ℝ => α / t) :=
    (Equiv.divLeft₀ α hα).injective
  have hcount :
      ((fun t : ℝ => α / t) ⁻¹' Set.range (fun z : ℤ => (z : ℝ))).Countable :=
    (Set.countable_range (fun z : ℤ => (z : ℝ))).preimage hinj
  filter_upwards [hcount.ae_notMem intervalMeasure] with t ht
  have hne : α / t ≠ (Int.floor (α / t) : ℝ) := by
    intro h
    exact ht ⟨Int.floor (α / t), h.symm⟩
  have hdiv : ContinuousAt (fun b : ℝ => b / t) α := by fun_prop
  have hfract : ContinuousAt (fun b : ℝ => Int.fract (b / t)) α := by
    simpa only [Function.comp_def] using
      (ContinuousAt.comp (f := fun b : ℝ => b / t) (g := Int.fract)
        (continuousAt_fract (x := α / t) hne) hdiv)
  have hreal : ContinuousAt (fun b : ℝ => realGenerator b t) α := by
    exact hfract.sub (continuousAt_id.mul continuousAt_const)
  have hcast : ContinuousAt (fun x : ℝ => (x : ℂ)) (realGenerator α t) :=
    Complex.continuous_ofReal.continuousAt
  have hc : ContinuousAt (fun b : ℝ => generatorFunction b t) α := by
    simpa only [Function.comp_def, generatorFunction] using
      (ContinuousAt.comp (f := fun b : ℝ => realGenerator b t)
        (g := fun x : ℝ => (x : ℂ)) hcast hreal)
  exact hc.tendsto.comp ha

/-- A uniformly bounded sequence of dilation parameters gives a uniformly
integrable family of continuous Nyman generators. -/
theorem generatorFunction_unifIntegrable_of_abs_le
    {a : ℕ → ℝ} {C : ℝ} (ha : ∀ n, |a n| ≤ C) :
    UnifIntegrable (fun n => generatorFunction (a n)) 2 intervalMeasure := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (a 0)) (ha 0)
  apply (uniformIntegrable_of (p := (2 : ENNReal)) (by norm_num) (by norm_num)
    (fun n => (generatorFunction_measurable (a n)).aestronglyMeasurable) ?_).unifIntegrable
  intro ε hε
  let R : NNReal := ⟨C + 2, by positivity⟩
  refine ⟨R, fun n => ?_⟩
  have hzero :
      {x | R ≤ ‖generatorFunction (a n) x‖₊}.indicator
        (generatorFunction (a n)) = 0 := by
    funext x
    rw [Set.indicator_of_notMem]
    · rfl
    · change ¬ R ≤ ‖generatorFunction (a n) x‖₊
      apply not_le_of_gt
      apply NNReal.coe_lt_coe.mp
      change ‖generatorFunction (a n) x‖ < C + 2
      calc
        ‖generatorFunction (a n) x‖ ≤ 1 + |a n| :=
          generatorFunction_norm_le (a n) x
        _ ≤ 1 + C := by linarith [ha n]
        _ < C + 2 := by linarith
  rw [hzero, eLpNorm_zero]
  exact bot_le

/-- The actual L² generator depends continuously on every nonzero dilation
parameter. This is the dominated-convergence step needed to pass from rational
meshes to Burnol's full continuous parameter family. -/
theorem tendsto_generator {a : ℕ → ℝ} {α : ℝ} (hα : α ≠ 0)
    (ha : Filter.Tendsto a Filter.atTop (nhds α)) :
    Filter.Tendsto (fun n => generator (a n)) Filter.atTop (nhds (generator α)) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_norm_le
  have habs : ∀ n, |a n| ≤ C := by
    intro n
    simpa only [Real.norm_eq_abs] using hC (a n) ⟨n, rfl⟩
  have hnorm :
      Filter.Tendsto
        (fun n => eLpNorm (generatorFunction (a n) - generatorFunction α)
          2 intervalMeasure)
        Filter.atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (fun n => (generatorFunction_measurable (a n)).aestronglyMeasurable)
      (generatorFunction_memLp α)
      (generatorFunction_unifIntegrable_of_abs_le habs)
      (generatorFunction_ae_tendsto hα ha)
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => generatorFunction (a n))
    (fun n => generatorFunction_memLp (a n))
    (generatorFunction α) (generatorFunction_memLp α)).2 hnorm

theorem continuousAt_generator {α : ℝ} (hα : α ≠ 0) :
    ContinuousAt generator α := by
  show Filter.Tendsto generator (nhds α) (nhds (generator α))
  rw [tendsto_nhds_iff_seq_tendsto]
  intro a ha
  simpa only [Function.comp_def] using tendsto_generator hα ha

def unitVector : Hilbert := (memLp_const (1 : ℂ)).toLp (fun _ : ℝ => (1 : ℂ))

theorem unitVector_ae :
    (unitVector : ℝ → ℂ) =ᵐ[intervalMeasure] (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp _

theorem unitVector_norm : ‖unitVector‖ = 1 := by
  rw [unitVector, Lp.norm_toLp,
    eLpNorm_const' (1 : ℂ) (by norm_num) (by norm_num)]
  norm_num [intervalMeasure]

/-- Burnol's full continuous closed span, indexed by every alpha in (0,1). -/
def closedSpace : Submodule ℂ Hilbert :=
  (Submodule.span ℂ (range fun α : Ioo (0 : ℝ) 1 => generator α)).topologicalClosure

theorem generator_mem_closedSpace {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    generator α ∈ closedSpace :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨⟨α, hα⟩, rfl⟩)

theorem closedSpace_isClosed : IsClosed (closedSpace : Set Hilbert) :=
  Submodule.isClosed_topologicalClosure _

/-- Rational dilation parameters in the open unit interval. -/
def rationalParameters : Set ℝ :=
  (fun q : ℚ => (q : ℝ)) '' ((fun q : ℚ => (q : ℝ)) ⁻¹' Ioo (0 : ℝ) 1)

/-- The closed span generated using rational parameters only. -/
def rationalClosedSpace : Submodule ℂ Hilbert :=
  (Submodule.span ℂ (generator '' rationalParameters)).topologicalClosure

theorem generator_mem_rationalClosedSpace {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    generator α ∈ rationalClosedSpace := by
  have hcl : α ∈ closure rationalParameters :=
    Rat.denseRange_cast.subset_closure_image_preimage_of_isOpen isOpen_Ioo hα
  have himg : generator α ∈ closure (generator '' rationalParameters) :=
    mem_closure_image (continuousAt_generator (ne_of_gt hα.1)) hcl
  exact (closure_minimal
    (fun x hx => (Submodule.le_topologicalClosure _)
      (Submodule.subset_span hx))
    (Submodule.isClosed_topologicalClosure _)) himg

/-- Burnol's full continuous Nyman space is already generated densely by the
rational dilation parameters in the open unit interval. -/
theorem rationalClosedSpace_eq_closedSpace :
    rationalClosedSpace = closedSpace := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.2
      rintro x ⟨α, hα, rfl⟩
      rcases hα with ⟨q, hq, rfl⟩
      exact generator_mem_closedSpace hq
    · exact closedSpace_isClosed
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.2
      rintro x ⟨α, rfl⟩
      exact generator_mem_rationalClosedSpace α.property
    · exact Submodule.isClosed_topologicalClosure _

/-- The unnormalized dilation identity, valid pointwise including Lean's totalized zero. -/
theorem realGenerator_dilation (α lam t : ℝ) :
    realGenerator α (t / lam) = realGenerator (α * lam) t - α * realGenerator lam t := by
  simp only [realGenerator, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul, mul_assoc]
  ring

theorem generatorFunction_dilation (α lam t : ℝ) :
    generatorFunction α (t / lam) =
      generatorFunction (α * lam) t - (α : ℂ) * generatorFunction lam t := by
  simpa only [generatorFunction, Complex.ofReal_sub, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) (realGenerator_dilation α lam t)

theorem generatorFunction_conj (α t : ℝ) :
    star (generatorFunction α t) = generatorFunction α t := by
  simp [generatorFunction]

/-- Beyond one both fractional parts are their arguments and cancel exactly. -/
theorem realGenerator_eq_zero_of_one_lt {α t : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ht : 1 < t) : realGenerator α t = 0 := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have ha : Int.fract (α / t) = α / t := Int.fract_eq_self.mpr
    ⟨div_nonneg hα0 ht0.le, (div_lt_one ht0).mpr (lt_of_le_of_lt hα1 ht)⟩
  have hb : Int.fract (1 / t) = 1 / t := Int.fract_eq_self.mpr
    ⟨by positivity, (div_lt_one ht0).mpr ht⟩
  rw [realGenerator, ha, hb]
  ring

/-- Every contracted generator is represented by a vector in the actual
continuous Nyman closed span. This is an equality of L2 representatives. -/
theorem exists_closedSpace_dilatedGenerator {α lam : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ v : Hilbert, v ∈ closedSpace ∧
      (v : ℝ → ℂ) =ᵐ[intervalMeasure] (fun t => generatorFunction α (t / lam)) := by
  have hp : α * lam ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨mul_pos hα.1 hlam.1, ?_⟩
    calc
      α * lam < 1 * lam := mul_lt_mul_of_pos_right hα.2 hlam.1
      _ < 1 := by simpa using hlam.2
  refine ⟨generator (α * lam) - (α : ℂ) • generator lam,
    closedSpace.sub_mem (generator_mem_closedSpace hp)
      (closedSpace.smul_mem _ (generator_mem_closedSpace hlam)), ?_⟩
  filter_upwards [Lp.coeFn_sub (generator (α * lam)) ((α : ℂ) • generator lam),
    Lp.coeFn_smul (α : ℂ) (generator lam), generator_ae (α * lam), generator_ae lam]
    with t hsub hsm hprod hgen
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hsub hsm
  rw [hsub, hsm, hprod, hgen]
  exact (generatorFunction_dilation α lam t).symm

end RiemannResearch.RH.Burnol.ContinuousNyman

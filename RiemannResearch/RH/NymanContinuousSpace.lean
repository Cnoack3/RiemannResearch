import Mathlib.MeasureTheory.Function.L2Space
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

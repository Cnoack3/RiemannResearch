import RiemannResearch.RH.RamanujanMellinInfiniteInnovations
import RiemannResearch.RH.ParetoMellinSourceMetric
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Uniform stability of physical Mellin observation energies

Source: the complete inverse-Gram source metric and physical projection
identity, 24 October 2026. Constants are independent of probe count,
separation, and ordering. The genuine Q bound retains its exact metric
correction. No completeness of the Mellin observations is used.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mellinPhysicalCapacity_bounds (f : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    0 ≤ mellinInverseCapacity s (fun i => paretoMellin f (s i)) ∧
      mellinInverseCapacity s (fun i => paretoMellin f (s i)) ≤ ‖f‖ ^ 2 := by
  refine ⟨mellinInverseCapacity_nonneg s _ hs hdet, ?_⟩
  have he := finiteMellinKernel_inverse_completion f s hs hdet
  change ‖f‖ ^ 2 = _ + mellinProjectionRemainder f s at he
  have hr := mellinProjectionRemainder_nonneg f s
  linarith

theorem mellinPhysicalCapacity_sqrt_le (f : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin f (s i))) ≤ ‖f‖ := by
  have h := mellinPhysicalCapacity_bounds f s hs hdet
  have hsqrt := Real.sq_sqrt h.1
  nlinarith [Real.sqrt_nonneg (mellinInverseCapacity s (fun i => paretoMellin f (s i))),
    norm_nonneg f]

/-- The square root of any finite observation energy is a contraction of the
physical Hilbert norm, uniformly even for nearly colliding probes. -/
theorem mellinPhysicalCapacity_sqrt_lipschitz (f g : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    |Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin f (s i))) -
      Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin g (s i)))| ≤ ‖f - g‖ := by
  have h := finiteMellinKernel_source_metric_lower (f - g) s
    (fun i => paretoMellin f (s i)) (fun i => paretoMellin g (s i)) hs hdet
    (fun i => (paretoMellinContinuous (s i) (hs i)).map_sub f g)
  have ha := sq_abs (Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin f (s i))) -
    Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin g (s i))))
  nlinarith [abs_nonneg (Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin f (s i))) -
    Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin g (s i)))), norm_nonneg (f - g)]

/-- Sharp probe-independent local Lipschitz bound on the complete capacity. -/
theorem mellinPhysicalCapacity_abs_sub_le (f g : ThresholdHilbert) (s : ι → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    |mellinInverseCapacity s (fun i => paretoMellin f (s i)) -
      mellinInverseCapacity s (fun i => paretoMellin g (s i))| ≤
        ‖f - g‖ * (‖f‖ + ‖g‖) := by
  let a := Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin f (s i)))
  let b := Real.sqrt (mellinInverseCapacity s (fun i => paretoMellin g (s i)))
  have ha : a ^ 2 = mellinInverseCapacity s (fun i => paretoMellin f (s i)) :=
    Real.sq_sqrt (mellinPhysicalCapacity_bounds f s hs hdet).1
  have hb : b ^ 2 = mellinInverseCapacity s (fun i => paretoMellin g (s i)) :=
    Real.sq_sqrt (mellinPhysicalCapacity_bounds g s hs hdet).1
  have hab : 0 ≤ a + b := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : a + b ≤ ‖f‖ + ‖g‖ := add_le_add
    (mellinPhysicalCapacity_sqrt_le f s hs hdet)
    (mellinPhysicalCapacity_sqrt_le g s hs hdet)
  have hdiff : |a - b| ≤ ‖f - g‖ := mellinPhysicalCapacity_sqrt_lipschitz f g s hs hdet
  calc
    _ = |a - b| * (a + b) := by rw [← ha, ← hb, ← abs_of_nonneg hab, ← abs_mul]; congr 1; ring
    _ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := mul_le_mul hdiff hsum hab (norm_nonneg _)

/-- The complete infinite capacity has the same stability constant. -/
theorem mellinCapacityLimit_abs_sub_le (f g : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    |mellinCapacityLimit f z - mellinCapacityLimit g z| ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
  apply le_of_tendsto' (((mellinPrefixCapacity_physical_tendsto f z hz hinj).sub
    (mellinPrefixCapacity_physical_tendsto g z hz hinj)).abs)
  intro N
  exact mellinPhysicalCapacity_abs_sub_le f g (fun i : Fin N => z i.val)
    (fun i => hz i.val) ((mellinCauchyGram_det_ne_zero_iff_injective _
      (fun i : Fin N => hz i.val)).mpr (hinj.comp Fin.val_injective))

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QMellinTransfer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Genuine Q physical stability with the exact positive measure correction. -/
theorem qMellinPhysicalCapacity_sqrt_lipschitz_exact (f g : QHilbert) (z : ι → ℂ)
    (hz : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z) :
    (Real.sqrt (mellinInverseCapacity z (fun i => qMellin f (z i))) -
      Real.sqrt (mellinInverseCapacity z (fun i => qMellin g (z i)))) ^ 2 +
      metricCorrection (f - g) ≤ zetaTwo * ‖f - g‖ ^ 2 := by
  apply qMellin_source_metric_lower (f - g) z _ _ hz hinj
  intro i
  exact (qMellinContinuous (z i) (hz i)).map_sub f g

end RiemannResearch.RH.QMellinTransfer

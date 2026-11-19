import RiemannResearch.Analysis.ActualOrdinateAngularLaw
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroFixedStripConcentration
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Joint angular and horizontal law of uniformly sampled zeta-zero occurrences

The angle is the ordinate modulo `2π`, and the real mark is the signed
displacement from the critical line. The full height limit is angular Haar
measure pushed forward to displacement zero. The quantitative coupling
bound is the mean absolute displacement times the Lipschitz constant.
For the underlying Fourier equidistribution of ordinates, see Hlawka as
described in Ford–Zaharescu, §1, https://arxiv.org/abs/math/0405459.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology NNReal
namespace RiemannResearch.Analysis.ActualZeroOrdinate

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private def copyAtoms {X : Type*} [MeasurableSpace X] (T : ℝ) (v : Copies T → X) : Measure X :=
  ∑ c : Copies T, ENNReal.ofReal ((Ncount 0 T : ℝ)⁻¹) • Measure.dirac (v c)

private theorem copyAtoms_probability {X : Type*} [MeasurableSpace X]
    (T : ℝ) (v : Copies T → X) (hN : 0 < Ncount 0 T) : IsProbabilityMeasure (copyAtoms T v) := by
  constructor
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  simp only [copyAtoms, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  simp [hn]

private theorem integral_copyAtoms {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : ℝ) (v : Copies T → X) (f : X → ℝ) :
    (∫ x, f x ∂copyAtoms T v) = (∑ c : Copies T, f (v c)) / (Ncount 0 T : ℝ) := by
  unfold copyAtoms
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Ncount 0 T : ℝ)⁻¹), smul_eq_mul,
    div_eq_mul_inv, mul_comm, Finset.mul_sum]

private def jointMark (T : ℝ) (c : Copies T) : OrdinateAngle × ℝ :=
  ((c.1.1.im : OrdinateAngle), c.1.1.re-1/2)

/-- The empirical probability measure with one atom for each occurrence. An
empty cutoff uses the atom at `(0,0)`. -/
def angleDisplacementLaw (T : ℝ) : ProbabilityMeasure (OrdinateAngle × ℝ) :=
  if hN : 0 < Ncount 0 T then ⟨copyAtoms T (jointMark T), copyAtoms_probability _ _ hN⟩
  else ⟨Measure.dirac (0,0), inferInstance⟩

theorem integral_angleDisplacementLaw (T : ℝ) (hN : 0 < Ncount 0 T)
    (f : OrdinateAngle × ℝ → ℝ) :
    (∫ x, f x ∂angleDisplacementLaw T) =
      (∑ c : Copies T, f ((c.1.1.im : OrdinateAngle), c.1.1.re-1/2)) / (Ncount 0 T : ℝ) := by
  have he : (angleDisplacementLaw T : Measure (OrdinateAngle × ℝ)) =
      copyAtoms T (jointMark T) := by simp [angleDisplacementLaw, hN]
  rw [he]
  exact integral_copyAtoms _ _ _

/-- Embed the angular law in the joint space, with zero horizontal displacement. -/
def onLineAngularLaw (μ : ProbabilityMeasure OrdinateAngle) :
    ProbabilityMeasure (OrdinateAngle × ℝ) :=
  μ.map (show Continuous (fun t : OrdinateAngle => (t,(0:ℝ))) by fun_prop).measurable.aemeasurable

/-- The first absolute moment bounds the cost of collapsing the horizontal mark
to zero while retaining the original ordinate of each occurrence. -/
theorem angular_coupling_le (T : ℝ) (hN : 0 < Ncount 0 T) (f : OrdinateAngle × ℝ → ℝ)
    {K : ℝ≥0} (hf : LipschitzWith K f) :
    |(∫ x, f x ∂angleDisplacementLaw T) - (∫ x, f x ∂onLineAngularLaw (angularLaw T))| ≤
      K * displacementMoment T 1 := by
  have ha : (angularLaw T : Measure OrdinateAngle) =
      copyAtoms T (fun c => (c.1.1.im : OrdinateAngle)) := by
    simp [angularLaw, hN]
    <;> rfl
  have hm : (∫ x, f x ∂onLineAngularLaw (angularLaw T)) =
      (∑ c : Copies T, f ((c.1.1.im : OrdinateAngle),0)) / (Ncount 0 T : ℝ) := by
    change (∫ x, f x ∂Measure.map (fun t : OrdinateAngle => (t,(0:ℝ)))
      (angularLaw T : Measure _)) = _
    rw [integral_map (by fun_prop) hf.continuous.aestronglyMeasurable, ha]
    exact integral_copyAtoms _ _ _
  rw [integral_angleDisplacementLaw T hN, hm, ← sub_div, ← Finset.sum_sub_distrib,
    abs_div,
    abs_of_nonneg (Nat.cast_nonneg (Ncount 0 T) : 0 ≤ (Ncount 0 T : ℝ))]
  unfold displacementMoment
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  simpa [Prod.dist_eq, Real.dist_eq, copyDisplacement] using
    hf.dist_le_mul ((c.1.1.im : OrdinateAngle), c.1.1.re-1/2) ((c.1.1.im : OrdinateAngle), 0)

/-- Joint weak convergence along all real heights. Fourier equidistribution
identifies the first marginal and the coupling collapses the second. -/
theorem tendsto_angleDisplacementLaw :
    Tendsto angleDisplacementLaw atTop (𝓝 (onLineAngularLaw angularHaar)) := by
  have hE : Tendsto (fun T : ℝ => horizontalEnergy T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
    simpa only [show 1+1 = (2:ℕ) by decide, displacementMoment_two] using
      tendsto_displacementMoment 1
  have hA := tendsto_angularLaw_haar (fixedStrip_of_relativeEnergy_tendsto_zero hE)
  have hZ : Tendsto (fun T => onLineAngularLaw (angularLaw T)) atTop
      (𝓝 (onLineAngularLaw angularHaar)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous angularLaw angularHaar hA
      (show Continuous (fun t : OrdinateAngle => (t,(0:ℝ))) by fun_prop)
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb hLip
  obtain ⟨K,hK⟩ := hLip
  have hbase := tendsto_iff_forall_lipschitz_integral_tendsto.mp hZ f hb ⟨K,hK⟩
  have hdiff : Tendsto (fun T : ℝ => (∫ x, f x ∂angleDisplacementLaw T) -
      (∫ x, f x ∂onLineAngularLaw (angularLaw T))) atTop (𝓝 0) := by
    have hlim := (tendsto_displacementMoment 0).const_mul (K:ℝ)
    simp only [zero_add, mul_zero] at hlim
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_count_pos] with T ht
    simpa only [Real.norm_eq_abs] using angular_coupling_le T ht f hK
  simpa only [sub_add_cancel, zero_add] using hdiff.add hbase

/-- Horizontal pushforward of the full joint empirical law. -/
def displacementLaw (T : ℝ) : ProbabilityMeasure ℝ :=
  (angleDisplacementLaw T).map measurable_snd.aemeasurable

theorem integral_abs_pow_displacementLaw (T : ℝ) (hN : 0 < Ncount 0 T) (k : ℕ) :
    (∫ x : ℝ, |x| ^ k ∂displacementLaw T) = displacementMoment T k := by
  change (∫ x : ℝ, |x| ^ k ∂Measure.map (Prod.snd : OrdinateAngle × ℝ → ℝ)
    (angleDisplacementLaw T : Measure (OrdinateAngle × ℝ))) = _
  rw [integral_map measurable_snd.aemeasurable
    (show Continuous (fun x : ℝ => |x| ^ k) by fun_prop).aestronglyMeasurable]
  exact integral_angleDisplacementLaw T hN (fun z => |z.2| ^ k)

theorem tendsto_displacementLaw :
    Tendsto displacementLaw atTop
      (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous angleDisplacementLaw
    (onLineAngularLaw angularHaar) tendsto_angleDisplacementLaw
    (continuous_snd : Continuous (Prod.snd : OrdinateAngle × ℝ → ℝ))
  have hzero : (onLineAngularLaw angularHaar).map measurable_snd.aemeasurable =
      (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    change Measure.map Prod.snd (Measure.map (fun x : OrdinateAngle => (x,(0:ℝ)))
      (angularHaar : Measure _)) = Measure.dirac 0
    rw [Measure.map_map measurable_snd (by fun_prop)]
    change Measure.map (fun _ : OrdinateAngle => (0:ℝ)) (angularHaar : Measure _) = _
    simp
  change Tendsto displacementLaw atTop
    (𝓝 ((onLineAngularLaw angularHaar).map measurable_snd.aemeasurable)) at h
  rwa [hzero] at h

end RiemannResearch.Analysis.ActualZeroOrdinate

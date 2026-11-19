import RiemannResearch.Analysis.ZeroDPPHorizontalAnticoncentration
import RiemannResearch.Probability.ZeroOrdinateQuotientDPP
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Horizontal reflection and all vertical observations

Reflection is a measure-preserving involution of the full sampled label
configuration. It fixes the entire selected ordinate set and negates the
signed, inverse-square-root-weighted horizontal statistic. Consequently every
integrable mixed moment against an arbitrary vertical observation vanishes.
-/

noncomputable section
open MeasureTheory Zeta23
open scoped BigOperators
namespace RiemannResearch.Analysis.ZeroDPPHorizontal
open ActualZeroOrdinate ActualZeroCollisionCertificate
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

private theorem label_ext {P : ℂ → Prop}
    {c d : (ρ : {z : ℂ // P z}) × Fin (zeroMult ρ.val)}
    (hρ : c.1.1 = d.1.1) (ha : c.2.val = d.2.val) : c = d := by
  obtain ⟨⟨z, hz⟩, a⟩ := c
  obtain ⟨⟨w, hw⟩, b⟩ := d
  change z = w at hρ
  subst w
  have h : a = b := Fin.ext ha
  subst b
  rfl

private def reflectedSite (i : Site) : Site := by
  let ρ := i.1.1
  have h : ρ ∈ cutoff (ordinate i) := mem_cutoff_iff_zeta.mpr ⟨i.1.2.1, i.1.2.2, le_rfl⟩
  have hr := mem_cutoff_iff_zeta.mp (reflect_mem h)
  refine ⟨⟨reflect ρ, hr.1, hr.2.1⟩, ⟨i.2.val, ?_⟩⟩
  rw [zetaSeam.mult_reflect ρ (mem_cutoff.mp h).1]
  exact i.2.isLt

private theorem reflectedSite_involutive : Function.Involutive reflectedSite := by
  intro i
  exact label_ext (reflect_reflect i.1.1) rfl

/-- The horizontal reflection of actual positive analytic-multiplicity labels. -/
def siteReflection : Site ≃ Site where
  toFun := reflectedSite
  invFun := reflectedSite
  left_inv := reflectedSite_involutive
  right_inv := reflectedSite_involutive

private theorem ordinate_siteReflection (i : Site) : ordinate (siteReflection i) = ordinate i :=
  reflect_im i.1.1

private def reflectedCopy (T : ℝ) (c : Copies T) : Copies T := by
  refine ⟨⟨reflect c.1.1, reflect_mem c.1.2⟩, ⟨c.2.val, ?_⟩⟩
  rw [zetaSeam.mult_reflect c.1.1 (mem_cutoff.mp c.1.2).1]
  exact c.2.isLt

private def copyReflection (T : ℝ) : Copies T ≃ Copies T where
  toFun := reflectedCopy T
  invFun := reflectedCopy T
  left_inv c := label_ext (reflect_reflect c.1.1) rfl
  right_inv c := label_ext (reflect_reflect c.1.1) rfl

/-- Reflection preserves the whole sampled zero-label law for every dictionary. -/
theorem measurePreserving_reflection (q : ℕ → ℝ) :
    MeasurePreserving (fun (x : Site → Bool) i => x (siteReflection i)) (limitingLaw q) (limitingLaw q) :=
  measurePreserving_relabel q siteReflection ordinate_siteReflection

theorem selectedOrdinates_reflection (x : Site → Bool) :
    selectedOrdinates (fun i => x (siteReflection i)) = selectedOrdinates x := by
  ext τ
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨siteReflection i, (ordinate_siteReflection i).trans hi, hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨siteReflection i, (ordinate_siteReflection i).trans hi, ?_⟩
    change x (reflectedSite (reflectedSite i)) = true
    rw [reflectedSite_involutive, hx]

/-- Reflection negates the signed horizontal statistic for every configuration. -/
theorem horizontalStatistic_reflection (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) (x : Site → Bool) :
    horizontalStatistic q T f (fun i => x (siteReflection i)) = -horizontalStatistic q T f x := by
  let e := copyReflection T
  let w := fun c : Copies T => f (copyOrdinate T c) * (c.1.1.re - 1 / 2) /
    Real.sqrt (limitingKernel q (liftCopy T c) (liftCopy T c))
  let o := fun c : Copies T => occupancyIndicator (fun y : Site → Bool => {i | y i = true}) (liftCopy T c) x
  have ho (c : Copies T) : copyOrdinate T (e c) = copyOrdinate T c := reflect_im c.1.1
  have hb (c : Copies T) : (e c).1.1.re = 1 - c.1.1.re := reflect_re c.1.1
  have hw (c : Copies T) : w (e c) = -w c := by
    have hγ : ordinate (liftCopy T (e c)) = ordinate (liftCopy T c) := ho c
    simp only [w, ho, hb, limitingKernel, kernelOfSpace, ProjectionDPP.kernel,
      collision_projection_eq q hγ]
    ring
  have hoc (c : Copies T) :
      occupancyIndicator (fun y : Site → Bool => {i | y i = true}) (liftCopy T c)
        (fun i => x (siteReflection i)) = o (e c) := by
    have he : siteReflection (liftCopy T c) = liftCopy T (e c) := label_ext rfl rfl
    by_cases h : x (liftCopy T (e c)) = true <;> simp [occupancyIndicator, o, he, h]
  unfold horizontalStatistic normalizedMark linearStatistic
  simp only [hoc]
  change (∑ c, w c * o (e c)) = -(∑ c, w c * o c)
  calc
    _ = ∑ c, -(w (e c) * o (e c)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hw, neg_mul, neg_neg]
    _ = ∑ c, -(w c * o c) := e.sum_comp (fun c => -(w c * o c))
    _ = _ := Finset.sum_neg_distrib (fun c => w c * o c)

/-- Every integrable test of the entire selected ordinate set pairs to zero
with signed horizontal displacement. The vertical test can be nonlinear and
can use all heights. -/
theorem integral_vertical_mul_horizontal_eq_zero (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ)
    (g : Set OrdinateSite → ℝ)
    (hg : Integrable (fun x => g (selectedOrdinates x) * horizontalStatistic q T f x) (limitingLaw q)) :
    (∫ x, g (selectedOrdinates x) * horizontalStatistic q T f x ∂limitingLaw q) = 0 := by
  let μ := limitingLaw q
  let R := fun (x : Site → Bool) i => x (siteReflection i)
  let F := fun x => g (selectedOrdinates x) * horizontalStatistic q T f x
  have hp : MeasurePreserving R μ μ := measurePreserving_reflection q
  have hF : AEStronglyMeasurable F (μ.map R) := hp.map_eq.symm ▸ hg.aestronglyMeasurable
  have he : (∫ x, F (R x) ∂μ) = ∫ x, F x ∂μ := by
    rw [← integral_map hp.measurable.aemeasurable hF, hp.map_eq]
  have hneg (x : Site → Bool) : F (R x) = -F x := by
    simp only [F, R, selectedOrdinates_reflection, horizontalStatistic_reflection, mul_neg]
  simp only [hneg, integral_neg] at he
  change (∫ x, F x ∂μ) = 0
  linarith

end RiemannResearch.Analysis.ZeroDPPHorizontal

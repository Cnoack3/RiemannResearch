import Mathlib.Analysis.Complex.Convex
import RiemannResearch.RH.ActualAnnularMellin
import RiemannResearch.RH.AnnularMellinPoleOrder
import RiemannResearch.Analysis.ActualAnnularLatticeWeighted

/-!
# Actual annular Mellin continuation and zero exclusion

Source: the October 10 annular research continuation. The classical
meromorphic identity principle propagates the proved Re(s)>1 identity.
Weighted membership is the sole remaining arithmetic premise in the actual
zero-exclusion theorem. Multiplicities and the centering pole are retained.
-/

set_option autoImplicit false
open Set

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.AnnularMellinContinuation
open RiemannResearch.Analysis.AnnularMellin
open RiemannResearch.RH.AnnularMellin
open RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
private lemma punctured_halfPlane_preconnected (a : ℝ) (ha : a < 1) :
    IsPreconnected {z : ℂ | a < z.re ∧ z ≠ 1} := by
  let U : Set ℂ := {z | a < z.re} ∩ {z | 0 < z.im}
  let R : Set ℂ := {z | 1 < z.re}
  let L : Set ℂ := {z | a < z.re} ∩ {z | z.im < 0}
  let Q : Set ℂ := {z | a < z.re} ∩ {z | z.re < 1}
  have hU : IsPreconnected U :=
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hR : IsPreconnected R := (convex_halfSpace_re_gt 1).isPreconnected
  have hL : IsPreconnected L :=
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hQ : IsPreconnected Q :=
    ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hUR : IsPreconnected (U ∪ R) := by
    apply IsPreconnected.union' (s := U) (t := R) _ hU hR
    refine ⟨2 + Complex.I, ?_⟩
    change (a < (2 + Complex.I).re ∧ 0 < (2 + Complex.I).im) ∧
      1 < (2 + Complex.I).re
    norm_num
    linarith
  have hURL : IsPreconnected ((U ∪ R) ∪ L) := by
    apply IsPreconnected.union' (s := U ∪ R) (t := L) _ hUR hL
    refine ⟨2 - Complex.I, ?_⟩
    constructor
    · exact Or.inr (by change 1 < (2 - Complex.I).re; norm_num)
    · change a < (2 - Complex.I).re ∧ (2 - Complex.I).im < 0
      norm_num
      linarith
  have hall : IsPreconnected (((U ∪ R) ∪ L) ∪ Q) := by
    apply IsPreconnected.union' (s := (U ∪ R) ∪ L) (t := Q) _ hURL hQ
    refine ⟨(((a + 1) / 2 : ℝ) : ℂ) + Complex.I, ?_⟩
    constructor
    · apply Or.inl; apply Or.inl
      change a < ((((a + 1) / 2 : ℝ) : ℂ) + Complex.I).re ∧
        0 < ((((a + 1) / 2 : ℝ) : ℂ) + Complex.I).im
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, add_zero, zero_add]
      constructor <;> linarith
    · change a < ((((a + 1) / 2 : ℝ) : ℂ) + Complex.I).re ∧
        ((((a + 1) / 2 : ℝ) : ℂ) + Complex.I).re < 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      constructor <;> linarith
  have heq : {z : ℂ | a < z.re ∧ z ≠ 1} = (((U ∪ R) ∪ L) ∪ Q) := by
    ext z
    change (a < z.re ∧ z ≠ 1) ↔
      (((a < z.re ∧ 0 < z.im) ∨ 1 < z.re) ∨
        (a < z.re ∧ z.im < 0)) ∨ (a < z.re ∧ z.re < 1)
    constructor
    · rintro ⟨hz, hz1⟩
      rcases lt_trichotomy z.re 1 with hlt | he | hgt
      · exact Or.inr ⟨hz, hlt⟩
      · have hi : z.im ≠ 0 := by
          intro hi
          apply hz1
          apply Complex.ext <;> simp_all
        rcases lt_or_gt_of_ne hi with hneg | hpos
        · exact Or.inl (Or.inr ⟨hz, hneg⟩)
        · exact Or.inl (Or.inl (Or.inl ⟨hz, hpos⟩))
      · exact Or.inl (Or.inl (Or.inr hgt))
    · rintro (((⟨hz, hi⟩ | hz) | ⟨hz, hi⟩) | ⟨hz, hr⟩)
      · exact ⟨hz, fun he => by simp [he] at hi⟩
      · exact ⟨by linarith, fun he => by simp [he] at hz⟩
      · exact ⟨hz, fun he => by simp [he] at hi⟩
      · exact ⟨hz, fun he => by simp [he] at hr⟩
  simpa only [heq] using hall

theorem expression_meromorphicAt {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    MeromorphicAt meromorphicExpression z := by
  have hζ := Zeta23.riemannZeta_analyticOnNhd_compl_one z hz1
  have hl : MeromorphicAt (logDeriv riemannZeta) z := by
    change MeromorphicAt (deriv riemannZeta / riemannZeta) z
    exact hζ.deriv.meromorphicAt.div hζ.meromorphicAt
  exact ((multiplier_analyticAt hz).neg.meromorphicAt.mul hl).sub
    (analyticAt_const.meromorphicAt.div
      (analyticAt_id.sub analyticAt_const).meromorphicAt)

/-- Initial-half-plane equality propagates as a meromorphic germ. The
analyticity hypothesis is substantive; the local identity is proved here. -/
theorem local_identity_of_analytic_initial_identity {a : ℝ} {F : ℂ → ℂ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hF : ∀ z : ℂ, a < z.re → AnalyticAt ℂ F z)
    (hidentity : ∀ z : ℂ, 1 < z.re → F z = meromorphicExpression z)
    {z : ℂ} (hz : a < z.re) (hz1 : z ≠ 1) :
    F =ᶠ[𝓝[≠] z] meromorphicExpression := by
  let D : Set ℂ := {w | a < w.re ∧ w ≠ 1}
  let G : ℂ → ℂ := fun w => F w - meromorphicExpression w
  have hm : MeromorphicOn G D := by
    intro w hw
    exact (hF w hw.1).meromorphicAt.sub
      (expression_meromorphicAt (by linarith [hw.1]) hw.2)
  have htwo : meromorphicOrderAt G (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ w : ℂ in 𝓝 (2 : ℂ), 1 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with w hw
    exact sub_eq_zero.mpr (hidentity w hw)
  have hzD : z ∈ D := ⟨hz, hz1⟩
  have ht : meromorphicOrderAt G z = ⊤ := by
    by_contra h
    have hh := hm.meromorphicOrderAt_ne_top_of_isPreconnected
      (punctured_halfPlane_preconnected a ha1) hzD
      (show (2 : ℂ) ∈ D by constructor <;> norm_num; linarith) h
    exact hh htwo
  have he := meromorphicOrderAt_eq_top_iff.mp ht
  filter_upwards [he] with w hw
  exact sub_eq_zero.mp hw

/-- No simplicity assumption is used: every positive-real-part zero has
logarithmic-derivative pole order -1, whatever its multiplicity. -/
theorem zeta_ne_zero_of_analytic_initial_identity {a : ℝ} {F : ℂ → ℂ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hF : ∀ z : ℂ, a < z.re → AnalyticAt ℂ F z)
    (hidentity : ∀ z : ℂ, 1 < z.re → F z = meromorphicExpression z)
    {z : ℂ} (hz : a < z.re) (hz1 : z ≠ 1) : riemannZeta z ≠ 0 := by
  intro hzero
  have he := local_identity_of_analytic_initial_identity ha0 ha1 hF hidentity hz hz1
  have hn := (hF z hz).meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr he, expression_order_at_zero (by linarith) hz1 hzero] at hn
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hn

theorem actual_transform_initial_identity {z : ℂ} (hz : 1 < z.re) :
    transform actualAnnularVector z = meromorphicExpression z := by
  simpa only [transform, actualAnnularVector,
    show -z - 1 = -(z + 1) by ring, meromorphicExpression] using
    RiemannResearch.RH.ActualAnnularMellin.actualPrimeSignal_mellin_identity hz

/-- Weighted membership of the actual infinite signal excludes every zero
strictly beyond its weight; no local identity provider remains. -/
theorem zeta_ne_zero_of_actualAnnular_Ha {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hf : Ha a actualAnnularVector) {z : ℂ} (hz : a < z.re) (hz1 : z ≠ 1) :
    riemannZeta z ≠ 0 := by
  apply zeta_ne_zero_of_analytic_initial_identity ha0 ha1
    (fun w hw => transform_analyticAt hf (by linarith))
    (fun w hw => actual_transform_initial_identity hw) hz hz1

theorem not_actualAnnular_Ha_of_zero {a : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hz : a < z.re) (hz1 : z ≠ 1)
    (hzero : riemannZeta z = 0) : ¬ Ha a actualAnnularVector := by
  intro hf
  exact zeta_ne_zero_of_actualAnnular_Ha ha0 ha1 hf hz hz1 hzero

/-- Conditional research reduction with one actual arithmetic premise:
membership for every weight strictly above 1/2. -/
theorem riemannHypothesis_of_actualAnnular_all_damping
    (h : ∀ a : ℝ, (1/2:ℝ) < a → Ha a actualAnnularVector) : RiemannHypothesis := by
  apply RiemannResearch.RH.AnnularMellin.riemannHypothesis_iff_expression_analytic.mpr
  intro z hz hzone
  have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzone
  apply (analyticAt_expression_iff_zeta_ne_zero (by linarith) hz1).mpr
  exact zeta_ne_zero_of_actualAnnular_Ha
    (a := (z.re + 1/2) / 2) (by linarith) (by linarith)
    (h _ (by linarith)) (by linarith) hz1

theorem riemannHypothesis_of_actualCentered_all_damping
    (h : ∀ a : ℝ, (1/2:ℝ) < a → Ha a actualCenteredAnnularVector) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_actualAnnular_all_damping
  intro a ha
  exact (actualCentered_Ha_iff_actualPrimeSignal_Ha (by linarith)).mp (h a ha)

end RiemannResearch.RH.AnnularMellinContinuation

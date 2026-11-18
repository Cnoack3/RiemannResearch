import RiemannResearch.Analysis.ActualMollifierSignedBoundaryBudget
import RiemannResearch.Analysis.ActualZeroDensityCauchyDetector
import Mathlib.Tactic

/-!
# An actual Littlewood rectangle and its signed counting inequality

Chourasiya and Simonič, <https://arxiv.org/html/2507.15184v2>, equation (32),
use signed horizontal arguments with matching additive constants. We choose
a single outward, zero-free rectangle and its compatible logarithm lifts.
The bound holds simultaneously for every left moment of order in [1,2].
It preserves the original heights, analytic multiplicity and the signed
top-minus-bottom argument integral.
-/

noncomputable section
open Complex Set MeasureTheory
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

private theorem left_integrals_on_detector_rectangle (X : ℕ) {a H T p : ℝ}
    (ha : a ≤ 3 / 2) (hH : 0 < H) (hHT : H ≤ T) (hp : 0 ≤ p)
    (hborder : ∀ z ∈ RectangleBorder ((a : ℂ) + (H : ℂ) * I)
      (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * I), zetaDetector X z ≠ 0) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖zetaDetector X ((a:ℂ)+(t:ℂ)*I)‖) volume H T ∧
    IntervalIntegrable (fun t : ℝ => ‖mollifiedError X ((a:ℂ)+(t:ℂ)*I)‖^p) volume H T := by
  let φ : ℝ → ℂ := fun t => (a:ℂ)+(t:ℂ)*I
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have hf := zetaDetector_analyticOnNhd_rectangle X ha hH hHT
  constructor
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have hm : φ t ∈ RectangleBorder ((a:ℂ)+(H:ℂ)*I) (((3/2 : ℝ):ℂ)+(T:ℂ)*I) :=
      Or.inl (Or.inl (Or.inr ⟨by simp [φ], by simpa [φ] using ht⟩))
    have hc : ContinuousAt (zetaDetector X) (φ t) :=
      (hf _ (rectangleBorder_subset_rectangle _ _ hm)).continuousAt
    exact ((hc.comp hφ.continuousAt).norm.log
      (norm_ne_zero_iff.mpr (hborder _ hm))).continuousWithinAt
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hHT] at ht
    have htpos := hH.trans_le ht.1
    have hn : φ t ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [φ] at this
      linarith
    have he : AnalyticAt ℂ (mollifiedError X) (φ t) :=
      ((analyticAt_riemannZeta hn).mul (mollifier_analyticAt X _)).sub analyticAt_const
    exact ((he.continuousAt.comp hφ.continuousAt).norm.rpow_const (Or.inr hp)).continuousWithinAt

/-- All auxiliary contour premises and both integrability premises are
constructed. The right boundary keeps its exact logarithmic upper bound. -/
theorem exists_actual_littlewood_moment_count {X : ℕ} (hX : 37 ≤ X)
    {H T a σ ε : ℝ} (ha : a < 3/2) (haσ : a < σ)
    (hHT : H ≤ T) (hε : 0 < ε) (hεH : ε < H) :
    ∃ a' ∈ Ioo (a-ε) a, ∃ H' ∈ Ioo (H-ε) H, ∃ T' ∈ Ioo T (T+ε),
      (∀ z ∈ RectangleBorder ((a':ℂ)+(H':ℂ)*I) (((3/2 : ℝ):ℂ)+(T':ℂ)*I),
        zetaDetector X z ≠ 0) ∧
      ∃ B U : ℝ → ℂ, Continuous B ∧ Continuous U ∧
        (∀ u ∈ Icc a' (3/2), exp (B u) = zetaDetector X ((u:ℂ)+(H':ℂ)*I)) ∧
        (∀ u ∈ Icc a' (3/2), exp (U u) = zetaDetector X ((u:ℂ)+(T':ℂ)*I)) ∧
        (RectangleIntegral' (fun z => (z-((a':ℂ)+(H':ℂ)*I))*logDeriv (zetaDetector X) z)
          ((a':ℂ)+(H':ℂ)*I) (((3/2 : ℝ):ℂ)+(T':ℂ)*I)).re =
            logRectangleBoundary (zetaDetector X) (fun u => (B u).im) (fun u => (U u).im)
              a' (3/2) H' T' / (2*Real.pi) ∧
        ∀ p ∈ Icc (1:ℝ) 2, rightInclusiveCount T σ - rightInclusiveCount H σ ≤
          ((∫ t in H'..T', ‖mollifiedError X ((a':ℂ)+(t:ℂ)*I)‖ ^ p) +
            ((∫ u in a'..(3/2), (U u).im)-(∫ u in a'..(3/2), (B u).im)) +
            (T'-H')*(-Real.log (1-36/(X:ℝ)))) / (2*Real.pi*(σ-a')) := by
  obtain ⟨a', H', T', haa, hh, ht, hborder, _⟩ :=
    zetaDetector_exists_zeroFreeRectangle_expansion hX ha hHT hε hεH
  have hab : a' ≤ 3/2 := (haa.2.trans ha).le
  have hH : 0 < H' := by linarith [hh.1]
  have hH'T' := hh.2.le.trans (hHT.trans ht.1.le)
  have hgap := haa.2.trans haσ
  obtain ⟨B,U,hB,hU,heB,heU,hn,_,_⟩ :=
    exists_logRectangleBoundary_eq_contour hab hH'T'
      (zetaDetector_analyticOnNhd_rectangle X hab hH hH'T') hborder
  refine ⟨a',haa,H',hh,T',ht,hborder,B,U,hB,hU,heB,heU,hn,?_⟩
  intro p hp
  obtain ⟨hlog,hmi⟩ := left_integrals_on_detector_rectangle X hab hH hH'T'
    (show 0 ≤ p by linarith [hp.1]) hborder
  have hleft := zetaDetector_left_log_integral_le_moment X hH'T' hp.1 hp.2 hlog hmi
  let M := ∫ t in H'..T', ‖mollifiedError X ((a':ℂ)+(t:ℂ)*I)‖ ^ p
  let A := (∫ u in a'..(3/2), (U u).im) - (∫ u in a'..(3/2), (B u).im)
  let R := (T'-H')*(-Real.log (1-36/(X:ℝ)))
  let D := 2*Real.pi*(σ-a')
  let F := (M+A+R)/D
  have hD : 0 < D := by dsimp [D]; positivity
  have hDF : D*F - R = M+A := by dsimp [F]; field_simp; ring
  have hcount : rightInclusiveCount T' σ - rightInclusiveCount H' σ ≤ F := by
    apply densityDifference_le_of_normalizedContour_signedBudget hX B U hab hH hH'T' hgap hborder hn
    change _ ≤ D*F-R
    rw [hDF]
    change _ ≤ M at hleft
    dsimp only [A]
    linarith
  have hw := rightInclusiveDifference_le_expandedWindow hh.2.le hHT ht.1.le σ
  rw [rightInclusiveWindow_eq_sub hH'T'] at hw
  exact hw.trans hcount

end RiemannResearch.Analysis.ActualZeroOrdinate

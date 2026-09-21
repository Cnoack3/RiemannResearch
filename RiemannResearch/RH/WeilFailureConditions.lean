import Mathlib.Order.LiminfLimsup
import RiemannResearch.RH.PolynomialWeilCriterion
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Exact failure conditions for the fixed-width Weil program

Source: user-provided stringent not-RH conditions, 2026-09-21, groups 30--32.
The proved polynomial obstructions retain the two OPEN analytic providers of
`PolynomialWeilCriterion`. The stronger exponential and spectral statements
below are proposition definitions only; no provider is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.FixedWidthWeilDiscrepancy

/-- Conditional research reduction: at arbitrarily late locations the actual
completed two-hat form breaks every proposed polynomial lower envelope. -/
theorem not_RH_twoHat_polynomial_lower_failure
    (hRH : ¬ RiemannHypothesis) (h : ℝ)
    (hidentity : TwoHatWeilIdentity h) (hdetect : FixedWidthLandauDetection h)
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (R : ℝ) :
    ∃ x : ℝ, R ≤ x ∧
      completedWeilForm (twoHatTest h x) < -(C * (1 + x) ^ A) := by
  classical
  by_contra hn
  push Not at hn
  exact hRH (riemannHypothesis_of_twoHat_polynomial_lower
    h hidentity hdetect C hC A R hn)

/-- The exact logical alternative when a polynomial lower bound is supplied:
at least one analytic provider must fail. Neither failure is asserted alone. -/
theorem not_RH_twoHat_provider_alternative
    (hRH : ¬ RiemannHypothesis) (h : ℝ)
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (R : ℝ)
    (hlower : ∀ x, R ≤ x →
      -(C * (1 + x) ^ A) ≤ completedWeilForm (twoHatTest h x)) :
    ¬ TwoHatWeilIdentity h ∨ ¬ FixedWidthLandauDetection h := by
  classical
  by_cases hi : TwoHatWeilIdentity h
  · exact Or.inr (fun hd => hRH
      (riemannHypothesis_of_twoHat_polynomial_lower h hi hd C hC A R hlower))
  · exact Or.inl hi

/-- Conditional research reduction with the complete reference-energy factor.
The boundedness of that reference energy is explicit. -/
theorem not_RH_twoHat_energy_lower_failure
    (hRH : ¬ RiemannHypothesis) (h : ℝ)
    (hidentity : TwoHatWeilIdentity h) (hdetect : FixedWidthLandauDetection h)
    (D : (ℝ → ℂ) → ℝ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (A : ℕ) (R : ℝ)
    (henergy : ∀ x, R ≤ x → D (twoHatTest h x) ≤ B) :
    ∃ x : ℝ, R ≤ x ∧ completedWeilForm (twoHatTest h x) <
      -(C * (1 + x) ^ A) * D (twoHatTest h x) := by
  classical
  by_contra hn
  push Not at hn
  exact hRH (riemannHypothesis_of_twoHat_energy_polynomial_lower
    h hidentity hdetect D B C hB hC A R henergy hn)

/-- OPEN analytic target: the asserted two-sided exponential excursions of
the actual fixed-width arithmetic discrepancy. Quantifiers encode the two
infinite limsup/liminf conclusions without replacing identities by O notation. -/
def FixedWidthTwoSidedExponentialDetectionTarget (h : ℝ) : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → (1 / 2 : ℝ) < ρ.re → ρ.re < 1 →
    ∀ c : ℝ, 0 ≤ c → c < ρ.re - 1 / 2 →
      ∀ C : ℝ, 0 ≤ C → ∀ R : ℝ,
        (∃ x : ℝ, R ≤ x ∧ C * Real.exp (c * x) < hatPrimeDiscrepancy h x) ∧
        (∃ x : ℝ, R ≤ x ∧ hatPrimeDiscrepancy h x < -C * Real.exp (c * x))

/-- The two exact exponential moments used to remove the pole terms. -/
def weilMoment (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp (s * (u : ℂ))

/-- Smooth compactly supported tests in the stated open window, with both
moment conditions retained. No positivity or arithmetic estimate is included. -/
def WeilWindowTest (L : ℝ) (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ g ∧ HasCompactSupport g ∧
    Function.support g ⊆ Ioo (-L / 2) (L / 2) ∧
    weilMoment g (1 / 2) = 0 ∧ weilMoment g (-1 / 2) = 0

/-- Enlarging the support window preserves both exact moment constraints. -/
theorem WeilWindowTest.mono {L M : ℝ} (hLM : L ≤ M) {g : ℝ → ℂ}
    (hg : WeilWindowTest L g) : WeilWindowTest M g := by
  refine ⟨hg.1, hg.2.1, ?_, hg.2.2.2⟩
  intro u hu
  have hx := hg.2.2.1 hu
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

def weilL2Energy (g : ℝ → ℂ) : ℝ := ∫ u : ℝ, ‖g u‖ ^ 2

/-- Exact positive reference form in the research catalogue, including the
archimedean difference energy. Integrability and its identification with
A(g)+(1-a0)||g||^2 are separate analytic obligations. -/
def weilReferenceEnergy (g : ℝ → ℂ) : ℝ :=
  weilL2Energy g + ∫ v in Ioi (0 : ℝ),
    (Real.exp (-v / 2) / (1 - Real.exp (-2 * v))) *
      ∫ u : ℝ, ‖g u - g (u - v)‖ ^ 2

def weilWindowBottomValues (L : ℝ) : Set ℝ :=
  {x : ℝ | ∃ g : ℝ → ℂ, WeilWindowTest L g ∧ 0 < weilL2Energy g ∧
    x = completedWeilForm g / weilL2Energy g}

def weilWindowTopValues (L : ℝ) : Set ℝ :=
  {x : ℝ | ∃ g : ℝ → ℂ, WeilWindowTest L g ∧ 0 < weilReferenceEnergy g ∧
    x = 1 - completedWeilForm g / weilReferenceEnergy g}

theorem weilWindowBottomValues_mono : Monotone weilWindowBottomValues := by
  intro L M hLM x hx
  obtain ⟨g, hg, hpos, heq⟩ := hx
  exact ⟨g, WeilWindowTest.mono hLM hg, hpos, heq⟩

theorem weilWindowTopValues_mono : Monotone weilWindowTopValues := by
  intro L M hLM x hx
  obtain ⟨g, hg, hpos, heq⟩ := hx
  exact ⟨g, WeilWindowTest.mono hLM hg, hpos, heq⟩

def weilWindowBottom (L : ℝ) : ℝ := sInf (weilWindowBottomValues L)

def weilWindowTop (L : ℝ) : ℝ := sSup (weilWindowTopValues L)

def zetaHorizontalDefect : ℝ :=
  sSup {x : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    x = |ρ.re - 1 / 2|}

/-- OPEN research target for the exact window normalization. The finite-window
nonemptiness and bounds are part of the formal statement, preventing totalized
real infima/suprema from masquerading as spectral extrema. Monotonicity is
restricted to positive window lengths. -/
def WeilWindowSpectralGrowthTarget : Prop :=
  ¬ RiemannHypothesis →
    (∀ L : ℝ, 0 < L →
      (weilWindowBottomValues L).Nonempty ∧ BddBelow (weilWindowBottomValues L) ∧
      (weilWindowTopValues L).Nonempty ∧ BddAbove (weilWindowTopValues L)) ∧
    AntitoneOn weilWindowBottom (Ioi 0) ∧ MonotoneOn weilWindowTop (Ioi 0) ∧
    Tendsto weilWindowBottom atTop atBot ∧
    Tendsto weilWindowTop atTop atTop ∧
    Filter.limsup (fun L : ℝ => Real.log (2 + weilWindowTop L) / L) atTop =
      zetaHorizontalDefect

/-- The integer-order Sobolev squared norm used to state the complete family
of lower-bound failures. It includes every derivative through order k. -/
def weilSobolevEnergy (k : ℕ) (g : ℝ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∫ u : ℝ, ‖iteratedDeriv j g u‖ ^ 2

/-- OPEN research target: no fixed Sobolev norm supplies a support-independent
lower bound for the completed signed form on the two-moment test class. -/
def WeilSobolevSemiboundFailureTarget : Prop :=
  ¬ RiemannHypothesis → ∀ k : ℕ, ∀ A : ℝ, 0 ≤ A →
    ∃ L : ℝ, 0 < L ∧ ∃ g : ℝ → ℂ,
      WeilWindowTest L g ∧ completedWeilForm g < -A * weilSobolevEnergy k g

end RiemannResearch.RH.FixedWidthWeilDiscrepancy

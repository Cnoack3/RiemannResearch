import RiemannResearch.RH.AnnularArithmeticWeight
import RiemannResearch.LinearAlgebra.FinitePrimePairResidual
import RiemannResearch.Analysis.CenteredResidualTransfer
import RiemannResearch.Analysis.AnnularMellinMultiplier
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.NumberTheory.PrimePairEulerProduct
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Actual annular arithmetic definitions and explicit analytic obligations

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Definitions of propositions do not assert their proofs.

Source: RH_Centered_Arithmetic_Zero_Ordinates_20261009.md, Sections 14--22.
All coefficients here are Mathlib's actual von Mangoldt coefficients.
The Euler product has an unconditional convergence proof. Companion modules
supply actual finite-kernel integrability, the integral/quadratic identity,
and the actual annular Mellin identity on Re(s)>1. Explicit formulas, model
asymptotics, the RH-energy criterion, and arithmetic residual estimates remain
open. No local axiom supplies any obligation.

In particular, the RH-energy criterion below is a conditional reduction
with its exact domain-specific premises; it is not a new proof of RH.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.CenteredResidualTransfer
open RiemannResearch.NumberTheory.PrimePairEulerProduct

/-- The actual Euler product convergence proposition. The theorem below
supplies its unconditional proof rather than relying on totalized tprod. -/
def TwinPrimeProductConverges : Prop := Multipliable primePairEulerFactor

theorem twinPrimeProductConverges : TwinPrimeProductConverges :=
  primePairEulerFactor_multipliable

def singularSeries (h : ℕ) : ℝ :=
  if h % 2 = 1 then 0 else
    2 * twinPrimeConstant *
      ∏ p ∈ h.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

theorem singularSeries_eq_zero_of_odd_gap (h : ℕ) (hodd : h % 2 = 1) :
    singularSeries h = 0 := by
  simp only [singularSeries, hodd, if_true]

theorem one_le_singularSeries_of_even_gap (h : ℕ) (heven : h % 2 = 0) :
    (1 : ℝ) ≤ singularSeries h := by
  have hfactor (p : ℕ) :
      (1 : ℝ) ≤ if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
    by_cases hp : 2 < p
    · rw [if_pos hp]
      have hpR : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      apply (le_div_iff₀ (by linarith)).2
      linarith
    · simp only [if_neg hp, le_refl]
  have hprod : (1 : ℝ) ≤
      ∏ p ∈ h.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 :=
    Finset.one_le_prod (fun p _ => hfactor p)
  have hC := one_half_le_twinPrimeConstant
  have hC1 : (1 : ℝ) ≤ 2 * twinPrimeConstant := by linarith
  have hCn : 0 ≤ 2 * twinPrimeConstant := zero_le_one.trans hC1
  have hmul := mul_le_mul_of_nonneg_left hprod hCn
  have hodd : ¬h % 2 = 1 := by omega
  simp only [singularSeries, if_neg hodd]
  exact hC1.trans (by simpa only [mul_one] using hmul)

theorem singularSeries_nonneg (h : ℕ) : 0 ≤ singularSeries h := by
  by_cases hodd : h % 2 = 1
  · simpa only [singularSeries_eq_zero_of_odd_gap h hodd] using (le_refl (0 : ℝ))
  · have heven : h % 2 = 0 := by omega
    exact zero_le_one.trans (one_le_singularSeries_of_even_gap h heven)

theorem singularSeries_sub_one_eq_neg_one_of_odd_gap
    (h : ℕ) (hodd : h % 2 = 1) : singularSeries h - 1 = -1 := by
  rw [singularSeries_eq_zero_of_odd_gap h hodd]
  simp

theorem singularSeries_sub_one_nonneg_of_even_gap
    (h : ℕ) (heven : h % 2 = 0) : 0 ≤ singularSeries h - 1 :=
  sub_nonneg.mpr (one_le_singularSeries_of_even_gap h heven)

/-- The exact singular-series triangular average, retaining the linear
constant. This proposition is an open formalization obligation, not a
Hardy--Littlewood assumption about actual prime pairs. -/
def TriangularSingularSeriesProvider : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ H : ℕ, 2 ≤ H →
    |(∑ h ∈ Finset.Icc 1 (H - 1),
        ((H : ℝ) - (h : ℝ)) * (singularSeries h - 1)) -
      (-(H : ℝ) * Real.log (H : ℝ) / 2 +
        ((2 - Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) / 2) *
          (H : ℝ))| ≤ C * Real.rpow (H : ℝ) (1 / 2 + ε)

def indices (X : ℝ) : Finset ℕ := Finset.Icc 1 (Nat.floor X)

def actualCentered (X : ℝ) : ℝ := annularCenteredFinite (indices X) X

def actualPrimeSignal (X : ℝ) : ℝ := annularPrimeFinite (indices X) X

def actualLatticeCorrection (X : ℝ) : ℝ := annularLatticeFinite (indices X) X

theorem actualPrimeSignal_eq_centered_add_lattice (X : ℝ) :
    actualPrimeSignal X = actualCentered X + actualLatticeCorrection X :=
  annularPrimeFinite_eq_centered_add_lattice (indices X) X

/-- A set integral keeps the finite cutoff and has an empty-domain value
for X < 1. Its local integrability is separately recorded below. -/
def kernel (X : ℝ) (n k : ℕ) : ℝ :=
  ∫ x in Set.Icc (1 : ℝ) X,
    annularArithmeticWeight ((n : ℝ) / x) *
      annularArithmeticWeight ((k : ℝ) / x) / x ^ 2

def actualIntegralEnergy (X : ℝ) : ℝ :=
  ∫ x in Set.Icc (1 : ℝ) X, actualCentered x ^ 2 / x ^ 2

def actualQuadraticEnergy (X : ℝ) : ℝ :=
  centeredKernelEnergy (indices X) ArithmeticFunction.vonMangoldt (fun _ => 1) (kernel X)

def actualModel (X : ℝ) : ℝ :=
  centeredKernelModel (indices X) ArithmeticFunction.vonMangoldt (fun _ => 1)
    (fun n k => singularSeries (Nat.dist n k)) (kernel X)

def actualResidual (X : ℝ) : ℝ :=
  centeredKernelResidual (indices X) ArithmeticFunction.vonMangoldt (fun _ => 1)
    (fun n k => singularSeries (Nat.dist n k)) (kernel X)

/-- This exact matrix identity does not require an estimate or an integrability
provider. It preserves the actual diagonal and both singleton centering terms. -/
theorem actualQuadraticEnergy_eq_model_add_residual (X : ℝ) :
    actualQuadraticEnergy X = actualModel X + actualResidual X :=
  centeredKernelEnergy_eq_model_add_residual (indices X)
    ArithmeticFunction.vonMangoldt (fun _ => 1)
    (fun n k => singularSeries (Nat.dist n k)) (kernel X)

def LocalKernelIntegrability : Prop :=
  ∀ X : ℝ, 1 ≤ X → ∀ n k : ℕ,
    IntegrableOn
      (fun x : ℝ =>
        annularArithmeticWeight ((n : ℝ) / x) *
          annularArithmeticWeight ((k : ℝ) / x) / x ^ 2)
      (Set.Icc 1 X)

def ActualIntegralQuadraticIdentity : Prop :=
  ∀ X : ℝ, 1 ≤ X → actualIntegralEnergy X = actualQuadraticEnergy X

def ModelCoefficient : ℝ :=
  -(287 / 2560 : ℝ) + (237 / 640 : ℝ) * Real.log 2 +
    (5103 / 40960 : ℝ) * Real.log 3 -
    (16807 / 122880 : ℝ) * Real.log 7 -
    (35 / 1536 : ℝ) * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi))

/-- Elementary logarithm estimates are explicit; the Euler-constant lower
bound is supplied by Mathlib. No RH-strength hypothesis is used here. -/
theorem ModelCoefficient_lt_rational_of_log_bounds
    (h2 : Real.log 2 < (7 / 10 : ℝ))
    (h3 : Real.log 3 < (11 / 10 : ℝ))
    (h7 : (19 / 10 : ℝ) < Real.log 7)
    (hpi : (17 / 10 : ℝ) < Real.log (2 * Real.pi)) :
    ModelCoefficient < -(15883 / 614400 : ℝ) := by
  have hgamma := Real.one_half_lt_eulerMascheroniConstant
  unfold ModelCoefficient
  nlinarith

/-- Open analytic obligation: effective PNT plus the transported
Montgomery--Soundararajan singular-series identity. -/
def ModelConvergentRemainder : Prop :=
  ∃ C : ℝ, Tendsto
    (fun X : ℝ => actualModel X - ModelCoefficient * Real.log X)
    atTop (𝓝 C)

/-- Open quantitative obligation. It is equivalent to RH only after the
actual analytic criterion is independently proved. -/
def ActualSignedResidualUpperBound : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → actualResidual X ≤ C * Real.log X

def ActualEnergyUpperBound : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → actualQuadraticEnergy X ≤ C * Real.log X

def ActualModelLogBound : Prop :=
  ∃ B : ℝ, ∀ X : ℝ, 2 ≤ X → |actualModel X| ≤ B * Real.log X

/-- The two actual bounds are equivalent once the model estimate is supplied.
This proves no estimate for the prime residual. -/
theorem actualEnergyUpperBound_iff_signedResidualUpperBound
    (hmodel : ActualModelLogBound) :
    ActualEnergyUpperBound ↔ ActualSignedResidualUpperBound := by
  obtain ⟨B, hB⟩ := hmodel
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, ?_⟩
    intro X hX
    have hid := actualQuadraticEnergy_eq_model_add_residual X
    have hm := (abs_le.mp (hB X hX)).1
    have he := hC X hX
    nlinarith
  · rintro ⟨C, hC⟩
    refine ⟨C + B, ?_⟩
    intro X hX
    have hid := actualQuadraticEnergy_eq_model_add_residual X
    have hm := (abs_le.mp (hB X hX)).2
    have he := hC X hX
    nlinarith

/-- Open analytic identification; a definition is not a theorem provider. -/
def ActualRHEnergyCriterion : Prop :=
  RiemannHypothesis ↔ ActualEnergyUpperBound

theorem riemannHypothesis_iff_signedResidualUpperBound
    (hmodel : ActualModelLogBound) (hcriterion : ActualRHEnergyCriterion) :
    RiemannHypothesis ↔ ActualSignedResidualUpperBound :=
  hcriterion.trans (actualEnergyUpperBound_iff_signedResidualUpperBound hmodel)

/-- Inverse-square lattice property, discharged by the companion theorem
`AnnularCriticalEnergy.actualLatticeDecay`. -/
def ActualLatticeDecay : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |actualLatticeCorrection x| ≤ C / x ^ 2

/-- The all-X target is an actual nonnegative density's integrability,
not a silently totalized integral assigned a finite real value. -/
def ActualFiniteDampedEnergy (ε : ℝ) : Prop :=
  IntegrableOn
    (fun x : ℝ => actualPrimeSignal x ^ 2 * Real.rpow x (-2 - ε))
    (Set.Ioi 1)

/-- Initial-half-plane arithmetic identity supplied by ActualAnnularMellin.
The domain Re(s)>1 is deliberately retained; this definition supplies no proof
or continuation at a full zero. -/
def ActualAnnularMellinIdentity : Prop :=
  ∀ s : ℂ, 1 < s.re →
    (∫ x in Set.Ioi (1 : ℝ),
      (actualPrimeSignal x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      -RiemannResearch.Analysis.AnnularMellin.multiplier s *
        logDeriv riemannZeta s - (7 / 64 : ℂ) / (s - 1)

end RiemannResearch.RH.AnnularPrimePair

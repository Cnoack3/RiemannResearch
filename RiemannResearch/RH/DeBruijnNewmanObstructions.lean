import RiemannResearch.RH.LiCoefficientObstructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Actual de Bruijn--Newman heat family and open positivity obligations

Source: Rodgers--Tao, The de Bruijn--Newman constant is non-negative,
https://arxiv.org/abs/1801.05914. The heat-kernel normalization and the
threshold terminology are taken from that source. Its proof is not
formalized here. Group 35 of the user-provided 2026-09-21 catalogue requests
strict positivity conditional on failure of RH.

The series and integral are concrete formulas. Their convergence, the
zero-time identification, and the threshold theorem remain separately named
OPEN providers. In particular, default values of a divergent tsum, an
undefined Bochner integral, or an unbounded sInf prove none of these targets.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.ClassicalObstruction

/-- The summation index n denotes the conventional positive integer n+1. -/
def newmanKernelTerm (u : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (4 * u))

def newmanKernel (u : ℝ) : ℝ := ∑' n : ℕ, newmanKernelTerm u n

def newmanHeatIntegrand (t : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (t * u ^ 2) * newmanKernel u : ℝ) : ℂ) * Complex.cos (z * u)

def newmanHeat (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), newmanHeatIntegrand t z u

def newmanAllZerosReal (t : ℝ) : Prop :=
  ∀ z : ℂ, newmanHeat t z = 0 → z.im = 0

def newmanRealZeroTimes : Set ℝ := {t | newmanAllZerosReal t}

def deBruijnNewmanConstant : ℝ := sInf newmanRealZeroTimes

/-- Convergence and entire dependence needed to use the displayed formulas. -/
def NewmanHeatConvergenceTarget : Prop :=
  (∀ u : ℝ, 0 ≤ u → Summable (newmanKernelTerm u)) ∧
  (∀ t : ℝ, ∀ z : ℂ, IntegrableOn (newmanHeatIntegrand t z) (Ioi 0)) ∧
  (∀ t : ℝ, Differentiable ℂ (newmanHeat t))

/-- The zero-time identification in the standard z/2 normalization. -/
def NewmanZeroTimeIdentificationTarget : Prop :=
  ∀ z : ℂ, newmanHeat 0 z = 0 ↔ liXi (1 / 2 + Complex.I * z / 2) = 0

/-- Finiteness and exact threshold behavior, with no default-infimum shortcut. -/
def NewmanThresholdTarget : Prop :=
  newmanRealZeroTimes.Nonempty ∧ BddBelow newmanRealZeroTimes ∧
  ∀ t : ℝ, newmanAllZerosReal t ↔ deBruijnNewmanConstant ≤ t

/-- Group 35: strict positivity and every nonnegative subcritical time has
an actual nonreal zero. This is an open target, not a Lean theorem. -/
def NewmanFailureRHPositiveTarget : Prop :=
  ¬ RiemannHypothesis →
    0 < deBruijnNewmanConstant ∧ ∀ t : ℝ, 0 ≤ t → t < deBruijnNewmanConstant →
      ∃ z : ℂ, newmanHeat t z = 0 ∧ z.im ≠ 0

end RiemannResearch.RH.ClassicalObstruction

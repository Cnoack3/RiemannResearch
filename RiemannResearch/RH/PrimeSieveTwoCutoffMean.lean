import RiemannResearch.RH.PrimeSieveTwoCutoffHead
import RiemannResearch.RH.PrimeSieveSecantAlgebra
import RiemannResearch.RH.NaturalMobiusSourceLimits

/-!
# Actual Pareto means of the two-cutoff factorial sieves

Source: user-directed research continuation; see
`IndependentPrimeResearchContinuation20261007.md` for the statements
and their mathematical interpretation.


The actual normalized-residue mean `log d / d` identifies every finite
factorial sieve mean with its divisor-log sum. The actual two-cutoff
interpolant then has a secant mean after dividing these logarithmic sums
by the positive sieve reciprocals.

This file does not identify the normalized divisor-log sum with a prime
sum, or assume any Mertens asymptotic. Those are separate arithmetic and
asymptotic steps.

-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

/-- The finite factorial-divisor logarithmic mass, with the sign of the
actual primitive `derivativeSievePrimitive`. -/
def sieveLogarithmicMass (Y : ℕ) : ℝ :=
  -(∑ d ∈ Y.factorial.divisors,
    (ArithmeticFunction.moebius d : ℝ) * (Real.log d / (d : ℝ)))

/-- Exact complete Pareto mean of the actual finite Hilbert sieve. -/
theorem derivativeSieveHilbert_inner_one (Y : ℕ) :
    inner ℝ (derivativeSieveHilbert Y) hilbertOne = sieveLogarithmicMass Y := by
  unfold derivativeSieveHilbert sieveLogarithmicMass
  rw [sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hd2 : 2 ≤ d
  · simp only [if_pos hd2, real_inner_smul_left, residueAtom,
      normalizedResidueHilbert_inner_one, Nat.sub_add_cancel hd2]
    ring
  · have hd1 : d = 1 := by
      have := Nat.pos_of_mem_divisors hd
      omega
    subst d
    simp

/-- The same exact mean for the actual sequence, not an abstract proxy. -/
theorem derivativeSievePrimitive_paretoMean (Y : ℕ) :
    paretoMean (derivativeSievePrimitive Y) = sieveLogarithmicMass Y := by
  rw [← derivativeSieveHilbert_sequence, ← hilbert_inner_one]
  exact derivativeSieveHilbert_inner_one Y

/-- The complete mean of the actual signed head interpolant. -/
theorem twoCutoffSieveHilbert_inner_one (Y W : ℕ) :
    inner ℝ (twoCutoffSieveHilbert Y W) hilbertOne =
      (sieveReciprocal Y.factorial * sieveLogarithmicMass W -
        sieveReciprocal W.factorial * sieveLogarithmicMass Y) /
          (sieveReciprocal Y.factorial - sieveReciprocal W.factorial) := by
  unfold twoCutoffSieveHilbert
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    derivativeSieveHilbert_inner_one, derivativeSieveHilbert_inner_one]
  ring

theorem twoCutoffSievePrimitive_paretoMean (Y W : ℕ) :
    paretoMean (twoCutoffSievePrimitive Y W) =
      (sieveReciprocal Y.factorial * sieveLogarithmicMass W -
        sieveReciprocal W.factorial * sieveLogarithmicMass Y) /
          (sieveReciprocal Y.factorial - sieveReciprocal W.factorial) := by
  rw [← twoCutoffSieveHilbert_sequence, ← hilbert_inner_one]
  exact twoCutoffSieveHilbert_inner_one Y W

/-- Dividing the actual logarithmic mass by the positive reciprocal mass
gives the vertical coordinate for the exact mean secant. -/
def sieveNormalizedLogarithmicMass (Y : ℕ) : ℝ :=
  sieveLogarithmicMass Y / sieveReciprocal Y.factorial

/-- Actual two-cutoff mean as an exact secant; no prime-sum identification
or limiting theorem is used. -/
theorem twoCutoffSievePrimitive_paretoMean_secant (Y W : ℕ)
    (hneq : sieveReciprocal Y.factorial ≠ sieveReciprocal W.factorial) :
    paretoMean (twoCutoffSievePrimitive Y W) =
      (sieveNormalizedLogarithmicMass W - sieveNormalizedLogarithmicMass Y) /
        (1 / sieveReciprocal W.factorial - 1 / sieveReciprocal Y.factorial) := by
  have hY : sieveReciprocal Y.factorial ≠ 0 :=
    ne_of_gt (sieveReciprocal_pos _ (Nat.factorial_pos Y))
  have hW : sieveReciprocal W.factorial ≠ 0 :=
    ne_of_gt (sieveReciprocal_pos _ (Nat.factorial_pos W))
  have hscaleY : sieveReciprocal Y.factorial *
      sieveNormalizedLogarithmicMass Y = sieveLogarithmicMass Y := by
    unfold sieveNormalizedLogarithmicMass
    field_simp [hY]
  have hscaleW : sieveReciprocal W.factorial *
      sieveNormalizedLogarithmicMass W = sieveLogarithmicMass W := by
    unfold sieveNormalizedLogarithmicMass
    field_simp [hW]
  rw [twoCutoffSievePrimitive_paretoMean]
  simpa only [hscaleY, hscaleW] using
    (RiemannResearch.RH.PrimeSieveSecant.two_cutoff_secant_identity
      (sieveReciprocal Y.factorial) (sieveReciprocal W.factorial)
      (sieveNormalizedLogarithmicMass Y) (sieveNormalizedLogarithmicMass W)
      hY hW hneq)

end RiemannResearch.RH.Pareto

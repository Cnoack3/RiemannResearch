import RiemannResearch.RH.CanonicalTailHistoricalTargets

/-!
# Open noncommuting Abel and sieve limits of the canonical certificate

Source: user-provided stringent-condition catalogue, condition 10, 2026-09-21.
These are concrete OPEN analytic targets. Finite sieve identities in the
existing project do not prove these infinite iterated limits.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

def canonicalSievePrimes (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

def canonicalSieveModulus (y : ℕ) : ℕ := ∏ p ∈ canonicalSievePrimes y, p

def canonicalSieveDensity (y : ℕ) : ℝ :=
  ∏ p ∈ canonicalSievePrimes y, (1 - 1 / (p : ℝ))

def canonicalPrimitiveAbel (t : ℝ) : ℝ :=
  ∑' n : ℕ, canonicalPrimitive n * Real.exp (-(n : ℝ) * t)

def canonicalSieveAbelRemainder (m y : ℕ) (t : ℝ) : ℝ :=
  (∑' k : ℕ, if Nat.Coprime k (canonicalSieveModulus y)
    then canonicalPrimitive (m * k) * Real.exp (-((m * k : ℕ) : ℝ) * t) else 0) -
    (canonicalSieveDensity y / (m : ℝ)) * canonicalPrimitiveAbel t

/-- OPEN absolute convergence of all positively damped signed series. This
prevents reliance on the default value of a nonsummable real tsum. -/
def CanonicalAbelSummabilityTarget : Prop :=
  ∀ t : ℝ, 0 < t →
    Summable (fun n : ℕ => canonicalPrimitive n * Real.exp (-(n : ℝ) * t)) ∧
    (∀ m y : ℕ, 2 ≤ m → Summable (fun k : ℕ =>
      if Nat.Coprime k (canonicalSieveModulus y)
      then canonicalPrimitive (m * k) * Real.exp (-((m * k : ℕ) : ℝ) * t) else 0))

/-- OPEN: the finite-sieve Abel limits tend to zero as the sieve grows, while
the growing sieve at positive damping isolates the actual mth primitive
coordinate. No fixed-sieve Abel limit is asserted to vanish individually.
A nonzero coordinate is asserted for the same canonical certificate. -/
def CanonicalSieveAbelNoncommutationTarget : Prop :=
  ¬ RiemannHypothesis →
    (∃ m : ℕ, 2 ≤ m ∧ canonicalPrimitive m ≠ 0) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∃ L : ℕ → ℝ,
        (∀ y : ℕ, Tendsto (canonicalSieveAbelRemainder m y)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (L y))) ∧
        Tendsto L atTop (𝓝 0)) ∧
      (∀ t : ℝ, 0 < t →
        Tendsto (fun y => canonicalSieveAbelRemainder m y t) atTop
          (𝓝 (canonicalPrimitive m * Real.exp (-(m : ℝ) * t)))))

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

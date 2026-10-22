import RiemannResearch.RH.RHFalseTailConstraints
import RiemannResearch.RH.ParetoReciprocalDifference

/-!
# Canonical-tail assertions from the historical condition list

Source: user-provided stringent-condition catalogue, conditions 2, 6--9,
2026-09-21. These definitions record exact additional assertions on the actual
canonical arithmetic objects. Most remain OPEN formalization targets; their
definability does not establish them. The elementary physical-sublinearity
target now has a checked provider below.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- OPEN: both quantitative comparisons must concern the same two residuals. -/
def PointConstantResidualComparisonTarget : Prop :=
  (1 - 1 / Real.sqrt 2) ^ 2 * limitEnergy ≤ ‖pointDualResidual‖ ^ 2 ∧
  ‖pointDualResidual‖ ^ 2 ≤ (1 + 1 / Real.sqrt 2) ^ 2 * limitEnergy

/-- OPEN: the canonical certificate's extended annihilator has this signed
mean. This is stronger than first-coordinate positivity. -/
def CanonicalAnnihilatorMeanTarget : Prop :=
  ¬ RiemannHypothesis →
    -(2 + Real.sqrt 2) ≤
      inner ℝ (tailCertificateAnnihilator canonicalTailCertificate) hilbertOne ∧
    inner ℝ (tailCertificateAnnihilator canonicalTailCertificate) hilbertOne ≤
      -(2 - Real.sqrt 2)

/-- The historical normalization with first coordinate one. -/
def canonicalFirstCoordinateMinimizer : ThresholdHilbert :=
  paretoPointHilbert 0 + (‖canonicalTailCertificate‖ ^ 2)⁻¹ • canonicalTailCertificate

/-- OPEN exact identification and dilation orthogonality in the normalization
used in the prose, including its complete norm. -/
def CanonicalNormalizedDilationTarget : Prop :=
  ¬ RiemannHypothesis →
    canonicalFirstCoordinateMinimizer ∈ closedSpace ∧
    ‖canonicalFirstCoordinateMinimizer‖ ^ 2 =
      1 / 2 + 1 / ‖canonicalTailCertificate‖ ^ 2 ∧
    (∀ m : ℕ, ∀ hm : 2 ≤ m,
      inner ℝ canonicalFirstCoordinateMinimizer
        ((m : ℝ)⁻¹ • hilbertDilation m (by omega) canonicalFirstCoordinateMinimizer) = 0)

/-- The actual signed primitive; physical coordinate zero is anchored at zero. -/
def canonicalPrimitive (n : ℕ) : ℝ :=
  anchoredSignedTail (hilbertSequence canonicalTailCertificate) n

/-- OPEN: the pointwise canonical bound has a norm-independent constant. -/
def CanonicalPrimitivePointwiseTarget : Prop :=
  ¬ RiemannHypothesis → ∀ n : ℕ, 2 ≤ n →
    |canonicalPrimitive n| ≤
      1 / ((1 - 1 / Real.sqrt 2) * Real.sqrt (n : ℝ))

/-- Absolute primitive mass in the actual dyadic block `[2^j,2^(j+1))`. -/
def canonicalPrimitiveDyadicMass (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |canonicalPrimitive n|

/-- OPEN: the dyadic masses have infinite total but a finite weighted square
sum. These two statements do not assert any pointwise lower rate. -/
def CanonicalPrimitiveDyadicTarget : Prop :=
  ¬ RiemannHypothesis →
    ¬ Summable canonicalPrimitiveDyadicMass ∧
    Summable (fun j : ℕ => (2 : ℝ) ^ (-(j : ℤ)) * canonicalPrimitiveDyadicMass j ^ 2) ∧
    (∑' j : ℕ, (2 : ℝ) ^ (-(j : ℤ)) * canonicalPrimitiveDyadicMass j ^ 2) ≤
      4 * ‖canonicalTailCertificate‖ ^ 2

/-- OPEN: separate divergence of both signed first moments. Absolute-moment
divergence and recurrence of both signs do not by themselves prove this. -/
def CanonicalSeparateSignedMomentTarget : Prop :=
  ¬ RiemannHypothesis →
    ¬ Summable (fun n : ℕ =>
      max (hilbertSequence canonicalTailCertificate n) 0 / ((n : ℝ) + 1)) ∧
    ¬ Summable (fun n : ℕ =>
      max (-hilbertSequence canonicalTailCertificate n) 0 / ((n : ℝ) + 1))

/-- OPEN: exact global energy of the signed primitive's differences. -/
def CanonicalPrimitiveEnergyTarget : Prop :=
  ¬ RiemannHypothesis →
    (∑' n : ℕ, (n : ℝ) * ((n : ℝ) + 1) *
      (canonicalPrimitive n - canonicalPrimitive (n + 1)) ^ 2) =
      ‖canonicalTailCertificate‖ ^ 2

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- OPEN: every nonzero actual annihilator violates every prescribed
subexponential-logarithmic envelope in the stated range. -/
def AnnihilatorSubexponentialExcursionTarget : Prop :=
  ∀ u : ThresholdHilbert, u ∈ closedSpaceᗮ → u ≠ 0 →
    ∀ θ : ℝ, 0 < θ → θ < 3 / 5 → ∀ C : ℝ, ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ 2 ≤ n ∧
        C * (Real.log (n : ℝ)) ^ θ <
          Real.log (1 + |hilbertSequence u n|)

/-- Historical elementary Hilbert-coordinate growth target, now proved below. -/
def HilbertPhysicalSublinearTarget : Prop :=
  ∀ u : ThresholdHilbert,
    Tendsto (fun n : ℕ => hilbertSequence u n / (n : ℝ)) atTop (𝓝 0)

/-- Every physical Hilbert sequence is sublinear, without RH assumptions. -/
theorem hilbertPhysicalSublinear : HilbertPhysicalSublinearTarget :=
  hilbert_physical_sublinear

end RiemannResearch.RH.Pareto.CoefficientStabilization

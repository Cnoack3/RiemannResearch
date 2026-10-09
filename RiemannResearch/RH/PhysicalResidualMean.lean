import RiemannResearch.RH.ArithmeticCoreAlgebraicity
import RiemannResearch.RH.PhysicalSourceProjection

/-!
# Actual projection residual mean and the remaining Baker input

The existing finite cotangent/core/algebraicity providers discharge the
finite inverse and algebraicity inputs. Nonzero residual mean remains a
conditional research reduction with the explicitly named Baker separation
property as its Open formal arithmetic provider.

Source: paper continuation `crt_baker_mean_source_handoff.txt`, Sections 3--4,
8 October 2026. Baker's linear independence theorem supports the separation
property: A. Baker, Mathematika 13 (1966), 204--216,
https://doi.org/10.1112/S0025579300003971; explicit modern statement in
S. Dasgupta, arXiv:2303.02037, Theorem 1.2. Its formal provider remains open.
No RH endpoint or uniform source lower bound is asserted.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalResidualMean
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection
open ArithmeticCoreAlgebraicity

/-- Finite consequence of Baker: an algebraic combination of positive-prime
logarithms cannot equal the nonzero algebraic multiple `-2*pi`.
This is an explicit domain-specific hypothesis, not an inserted axiom. -/
def BakerVonMangoldtSeparation : Prop :=
  ∀ (s : Finset ℕ) (a : s → ℝ),
    (∀ i, IsAlgebraic ℚ (a i)) →
      ramanujanVonMangoldtVector s ⬝ᵥ a ≠ -2 * Real.pi

/-- Every coordinate of the actual inverse-core totient vector is algebraic.
The core identity, inverse entries and finite sum are already established. -/
theorem coreTotient_entry_algebraic (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (i : s) :
    IsAlgebraic ℚ (coreTotient s i) := by
  unfold coreTotient Matrix.mulVec dotProduct
  apply (IsIntegral.sum _ _).isAlgebraic
  intro j _
  apply IsAlgebraic.isIntegral
  apply (derivedCore_inverse_entry_algebraic s hs i j).mul
  change IsAlgebraic ℚ (Nat.totient j.val : ℝ)
  simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ)
    (Nat.totient j.val : ℚ))

/-- Baker is applied only after discharging algebraicity of every coefficient. -/
theorem mixedCharge_ne_neg_two_pi_of_baker
    (hBaker : BakerVonMangoldtSeparation) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) : mixedCharge s ≠ -2 * Real.pi := by
  exact hBaker s (coreTotient s) (coreTotient_entry_algebraic s hs)

theorem shiftedMixedCharge_ne_zero_of_baker
    (hBaker : BakerVonMangoldtSeparation) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) : 2 * Real.pi + mixedCharge s ≠ 0 := by
  have hb := mixedCharge_ne_neg_two_pi_of_baker hBaker s hs
  intro he
  apply hb
  linarith only [he]

/-- Ordinary periodic residual mean for the explicit projection coefficients.
Under the legal-set and odd-prime hypotheses below these coefficients are the
actual projection. Its full Pareto residual mean is a different functional. -/
def projectionResidualMean (s : Finset ℕ) : ℝ :=
  1 - (ramanujanTotientVector s ⬝ᵥ projectionCoefficients s) / 2

/-- The definition agrees with the literal residual sum on every common period. -/
theorem projectionResidualMean_eq_period_sum (s : Finset ℕ) (Q : ℕ)
    (hQ : 0 < Q) (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    (∑ r : Fin Q, (1 - synthesis s (projectionCoefficients s) r.val)) / (Q : ℝ) =
      projectionResidualMean s := by
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [sub_div, div_self hQR,
    RiemannResearch.RH.Pareto.synthesis_period_mean Q s (projectionCoefficients s) hQ hs hsQ]
  rfl

/-- Complete signed numerator for the actual residual mean. -/
theorem projectionResidualMean_formula (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    projectionResidualMean s =
      -2 * Real.pi * (2 * Real.pi + mixedCharge s) / shiftedDeterminant s := by
  unfold projectionResidualMean
  rw [projectionCoefficients]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, coreLambda_totient_pair]
  change 1 - ((2 / shiftedDeterminant s) *
    (logarithmicCharge s * inverseCharge s -
      (2 * Real.pi + mixedCharge s) * mixedCharge s)) / 2 = _
  field_simp [ne_of_gt (shiftedDeterminant_pos s hs ho)]
  unfold shiftedDeterminant
  ring

/-- Actual nonzero ordinary residual mean, conditional only on the named Baker
provider and ordinary legal-stage hypotheses. All finite inverses are genuine. -/
theorem projectionResidualMean_ne_zero_of_baker
    (hBaker : BakerVonMangoldtSeparation) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    projectionResidualMean s ≠ 0 := by
  rw [projectionResidualMean_formula s hs ho]
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero)
      (shiftedMixedCharge_ne_zero_of_baker hBaker s hs)
  · exact ne_of_gt (shiftedDeterminant_pos s hs ho)

/-- Baker also makes the exact finite mean-one penalty strictly positive.
The complete correction square from PhysicalSourceProjection is retained. -/
theorem meanOne_projection_error_gap_pos_of_baker
    (hBaker : BakerVonMangoldtSeparation) (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    0 < paretoError (synthesis s (constrainedOptimizer s)) -
      paretoError (synthesis s (projectionCoefficients s)) := by
  rw [meanOne_projection_error_gap s hs ho]
  apply div_pos
  · exact mul_pos (by positivity : 0 < 4 * Real.pi)
      (sq_pos_of_ne_zero (shiftedMixedCharge_ne_zero_of_baker hBaker s hs))
  · exact mul_pos (neg_pos.mpr (inverseCharge_neg s hs ho))
      (shiftedDeterminant_pos s hs ho)

/-- Full squarefree divisor stages discharge every finite stage hypothesis. -/
theorem divisor_projectionResidualMean_ne_zero_of_baker
    (hBaker : BakerVonMangoldtSeparation) (L : ℕ)
    (hL : 2 < L) (hsq : Squarefree L) :
    projectionResidualMean (divisorPackets L) ≠ 0 :=
  projectionResidualMean_ne_zero_of_baker hBaker _
    (divisorPackets_legal L) (divisorPackets_odd L hL hsq)

end RiemannResearch.RH.Pareto.PhysicalResidualMean

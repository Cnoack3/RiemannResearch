import RiemannResearch.Analysis.FiniteCollocationCertificate
import RiemannResearch.RH.QCRTScreenedCoordinates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Certified signed growth of actual canonical CRT lifts

Source: the user's GROW-001 proof-obligation investigation, 13 November 2026.
The predictor is arbitrary. Its residual uses the actual nonsymmetric
difference-test system, and its error radius uses that system's inverse columns.
The exact signed old/predictor correlation is retained. These finite-stage
certificates do not supply a uniform prime-power growth budget.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTCanonicalGrowthCertificate
open ZetaTwoHilbert QCRTFiniteCollocation QCRTScreenedCoordinates QPhysicalDifference
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteScreenedCollocation
open RiemannResearch.Analysis.FiniteCollocationCertificate

/-- Any proposed increment, in the actual physically screened coordinates. -/
def predictor (L M : ℕ) (z : Old L ⊕ New L M → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (joinedFamily L M) z

/-- Prescribed observations; they use only the old canonical vector and the new target. -/
def testSource (L M : ℕ) (hL : 2 ≤ L) : Old L ⊕ New L M → ℝ :=
  observe differenceCLM.toLinearMap (joinedFamily L M) (source L M hL)

/-- Computable equation defect of a proposed update, not the unknown response pairing. -/
def testResidual (L M : ℕ) (hL : 2 ≤ L) (z : Old L ⊕ New L M → ℝ) :=
  testSource L M hL - collocationInverse L M z

/-- Inverse-column error radius. It includes the full physical Q tail. -/
def errorRadius (L M : ℕ) (hL : 2 ≤ L) (z : Old L ⊕ New L M → ℝ) : ℝ :=
  residualRadius (collocationInverse L M) (joinedFamily L M) (testResidual L M hL z)

theorem canonical_increment_response (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) :
    response (collocationInverse L M) (joinedFamily L M) (testSource L M hL) =
      (canonical M hM : QHilbert) - canonical L hL := by
  change Fintype.linearCombination ℝ (joinedFamily L M) (coordinates L M hL) = _
  have hc : coordinates L M hL =
      Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL) := by
    ext k
    cases k <;> rfl
  rw [hc]
  change Fintype.linearCombination ℝ
    (Sum.elim (oldFamily L) (screenedFamily L M))
    (Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL)) = _
  rw [synthesis_join, canonical_assembly L M hL hM hLM]

/-- Complete signed identity for the prediction and its actual inverse-response error. -/
theorem canonical_signed_residual_exact
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 - ‖(canonical L hL : QHilbert)‖ ^ 2 =
      2 * inner ℝ (canonical L hL : QHilbert) (predictor L M z) +
      ‖predictor L M z‖ ^ 2 +
      2 * inner ℝ ((canonical L hL : QHilbert) + predictor L M z)
        (response (collocationInverse L M) (joinedFamily L M) (testResidual L M hL z)) +
      ‖response (collocationInverse L M) (joinedFamily L M) (testResidual L M hL z)‖ ^ 2 := by
  have he := signed_energy_residual (collocationInverse L M) (joinedFamily L M)
    (canonical L hL : QHilbert) (testSource L M hL) z
  rw [canonical_increment_response L M hL hM hLM, ← add_sub_assoc, add_sub_cancel_left] at he
  exact he

/-- A quantitative bound on the actual canonical response, with no unproved
inverse estimate assumed: the finite inverse-column cost remains explicit. -/
theorem canonical_signed_residual_bound
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 - ‖(canonical L hL : QHilbert)‖ ^ 2 ≤
      2 * inner ℝ (canonical L hL : QHilbert) (predictor L M z) +
      ‖predictor L M z‖ ^ 2 +
      2 * ‖(canonical L hL : QHilbert) + predictor L M z‖ * errorRadius L M hL z +
      errorRadius L M hL z ^ 2 := by
  have he := signed_energy_le_radius (collocationInverse L M) (joinedFamily L M)
    (canonical L hL : QHilbert) (testSource L M hL) z
  rw [canonical_increment_response L M hL hM hLM, ← add_sub_assoc, add_sub_cancel_left] at he
  exact he

/-- Conditional research reduction: supplying this concrete finite certificate
proves the desired multiplicative budget for the actual canonical vectors. -/
theorem canonical_growth_of_residual_certificate
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) (α : ℝ)
    (hcert :
      2 * inner ℝ (canonical L hL : QHilbert) (predictor L M z) +
      ‖predictor L M z‖ ^ 2 +
      2 * ‖(canonical L hL : QHilbert) + predictor L M z‖ * errorRadius L M hL z +
      errorRadius L M hL z ^ 2 ≤ α * ‖(canonical L hL : QHilbert)‖ ^ 2) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 ≤
      (1 + α) * ‖(canonical L hL : QHilbert)‖ ^ 2 := by
  have he := canonical_signed_residual_bound L M hL hM hLM z
  nlinarith

/-- Zero error radius gives an exact update, without dividing by energy or capacity. -/
theorem canonical_eq_predictor_of_zero_radius
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) (hzero : errorRadius L M hL z = 0) :
    (canonical M hM : QHilbert) = canonical L hL + predictor L M z := by
  have he := response_eq_of_radius_zero (collocationInverse L M) (joinedFamily L M)
    (testSource L M hL) z hzero
  rw [canonical_increment_response L M hL hM hLM] at he
  change (canonical M hM : QHilbert) - canonical L hL = predictor L M z at he
  rw [← he]
  abel

/-- The actual prediction error is the inverse response to the known equation defect. -/
theorem canonical_prediction_error_eq_response
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) :
    (canonical M hM : QHilbert) - (canonical L hL + predictor L M z) =
      response (collocationInverse L M) (joinedFamily L M) (testResidual L M hL z) := by
  have he := response_residual (collocationInverse L M) (joinedFamily L M)
    (testSource L M hL) z
  rw [canonical_increment_response L M hL hM hLM] at he
  change (canonical M hM : QHilbert) - canonical L hL =
    predictor L M z +
      response (collocationInverse L M) (joinedFamily L M) (testResidual L M hL z) at he
  calc
    (canonical M hM : QHilbert) - (canonical L hL + predictor L M z) =
        ((canonical M hM : QHilbert) - canonical L hL) - predictor L M z := by abel
    _ = _ := by rw [he, add_sub_cancel_left]

theorem canonical_prediction_error_le_radius
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) :
    ‖(canonical M hM : QHilbert) - (canonical L hL + predictor L M z)‖ ≤
      errorRadius L M hL z := by
  rw [canonical_prediction_error_eq_response L M hL hM hLM z]
  exact response_norm_le (collocationInverse L M) (joinedFamily L M) _

/-- Squared raw residuals are useful only together with the actual inverse-column energy. -/
theorem canonical_prediction_error_sq_le
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (z : Old L ⊕ New L M → ℝ) :
    ‖(canonical M hM : QHilbert) - (canonical L hL + predictor L M z)‖ ^ 2 ≤
      (∑ i, testResidual L M hL z i ^ 2) *
        (∑ i, ‖responseColumn (collocationInverse L M) (joinedFamily L M) i‖ ^ 2) := by
  rw [canonical_prediction_error_eq_response L M hL hM hLM z]
  exact response_norm_sq_le_column_energy (collocationInverse L M) (joinedFamily L M) _

/-- The predictor's signed energy retains exactly the old refit correlation. -/
theorem predictor_signed_energy (L M : ℕ) (hL : 2 ≤ L)
    (x : Old L → ℝ) (y : New L M → ℝ) :
    2 * inner ℝ (canonical L hL : QHilbert) (predictor L M (Sum.elim x y)) +
      ‖predictor L M (Sum.elim x y)‖ ^ 2 =
      2 * (∑ i, baseCoordinates L i * gram (oldFamily L) x i) +
        (∑ i, x i * gram (oldFamily L) x i) +
        (∑ j, y j * gram (screenedFamily L M) y j) := by
  calc
    _ = ‖(canonical L hL : QHilbert) + predictor L M (Sum.elim x y)‖ ^ 2 -
        ‖(canonical L hL : QHilbert)‖ ^ 2 := by rw [norm_add_sq_real]; ring
    _ = _ := by
      change ‖(canonical L hL : QHilbert) +
          Fintype.linearCombination ℝ (Sum.elim (oldFamily L) (screenedFamily L M))
            (Sum.elim x y)‖ ^ 2 - ‖(canonical L hL : QHilbert)‖ ^ 2 = _
      rw [synthesis_join, ← add_assoc, ← base_synthesis L hL]
      exact signed_energy (old_independent L) (newFamily L M) (baseCoordinates L) x y

/-- Old-only predictor obtained by solving the old block exactly. -/
def oldPredictorCoordinates (L M : ℕ) (hL : 2 ≤ L) : Old L ⊕ New L M → ℝ :=
  Sum.elim ((oldCollocationInverse L).symm (beta0 L M hL)) 0

/-- The actual oblique Schur source, with both nonsymmetric cross blocks retained. -/
def schurSource (L M : ℕ) (hL : 2 ≤ L) : New L M → ℝ :=
  beta1 L M hL - A10 L M ((oldCollocationInverse L).symm (beta0 L M hL))

/-- Exact old-block solution leaves precisely the Schur source in the new rows. -/
theorem old_predictor_residual (L M : ℕ) (hL : 2 ≤ L) :
    testResidual L M hL (oldPredictorCoordinates L M hL) =
      Sum.elim (0 : Old L → ℝ) (schurSource L M hL) := by
  ext k
  cases k with
  | inl i =>
    change beta0 L M hL i -
      inner ℝ (Fintype.linearCombination ℝ
        (Sum.elim (oldFamily L) (screenedFamily L M))
        (Sum.elim ((oldCollocationInverse L).symm (beta0 L M hL)) 0))
        (differenceCLM (oldFamily L i)) = 0
    rw [synthesis_join, map_zero, add_zero]
    change beta0 L M hL i -
      oldCollocationInverse L ((oldCollocationInverse L).symm (beta0 L M hL)) i = 0
    rw [LinearEquiv.apply_symm_apply, sub_self]
  | inr j =>
    change beta1 L M hL j -
      inner ℝ (Fintype.linearCombination ℝ
        (Sum.elim (oldFamily L) (screenedFamily L M))
        (Sum.elim ((oldCollocationInverse L).symm (beta0 L M hL)) 0))
        (differenceCLM (screenedFamily L M j)) = schurSource L M hL j
    rw [synthesis_join, map_zero, add_zero]
    rfl

/-- Only new-row response columns contribute after exact old-block elimination.
These are columns of the full nonsymmetric inverse, not columns of H⁻¹. -/
theorem old_predictor_radius (L M : ℕ) (hL : 2 ≤ L) :
    errorRadius L M hL (oldPredictorCoordinates L M hL) =
      ∑ j, |schurSource L M hL j| *
        ‖responseColumn (collocationInverse L M) (joinedFamily L M) (Sum.inr j)‖ := by
  unfold errorRadius
  rw [old_predictor_residual]
  simp [residualRadius, Fintype.sum_sum_type]

/-- A known zero Schur source closes the update exactly, including an empty new block. -/
theorem canonical_eq_old_predictor_of_schur_zero
    (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M)
    (hzero : schurSource L M hL = 0) :
    (canonical M hM : QHilbert) =
      canonical L hL + predictor L M (oldPredictorCoordinates L M hL) := by
  apply canonical_eq_predictor_of_zero_radius L M hL hM hLM
  rw [old_predictor_radius, hzero]
  simp

end RiemannResearch.RH.QCRTCanonicalGrowthCertificate

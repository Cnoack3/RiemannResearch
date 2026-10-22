/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSchurCoupling
import RiemannResearch.Analysis.CompensatedSourceCertificate

/-!
# Actual physical rank-two projection and ordinary-mean dual

The scalar source projection charge is identified with the actual full Pareto
Gram solve. The explicit projection and ordinary-mean dual satisfy their
normal equations with no supplied inverse equation. The complete projection
error retains its nonnegative Gram remainder; the mean-one error difference
retains the full signed-source square.

Source: user-directed continuation of PhysicalArithmeticObservations20261008.md.
The finite algebra is developed from the already proved physical core identity,
inertia and signed Schur coupling. No RH or analytic limit is assumed here.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalSourceProjection
open PhysicalPacketCore PhysicalSchurCoupling
open RiemannResearch.LinearAlgebra.RankTwoWoodbury
open RiemannResearch.LinearAlgebra.MeanOneSchurCoupling

def coreLambda (s : Finset ℕ) : s → ℝ :=
  (derivedCore s)⁻¹ *ᵥ ramanujanVonMangoldtVector s

def coreTotient (s : Finset ℕ) : s → ℝ :=
  (derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s

def projectionCoefficients (s : Finset ℕ) : s → ℝ :=
  (2 / shiftedDeterminant s) •
    (logarithmicCharge s • coreTotient s -
      (2 * Real.pi + mixedCharge s) • coreLambda s)

def totientDual (s : Finset ℕ) : s → ℝ :=
  (2 / shiftedDeterminant s) •
    (inverseCharge s • coreLambda s -
      (2 * Real.pi + mixedCharge s) • coreTotient s)

theorem coreLambda_totient_pair (s : Finset ℕ) :
    ramanujanTotientVector s ⬝ᵥ coreLambda s = mixedCharge s := by
  unfold coreLambda mixedCharge
  simpa only [inverseCore_transpose s] using
    Matrix.dotProduct_transpose_mulVec (derivedCore s)⁻¹
      (ramanujanTotientVector s) (ramanujanVonMangoldtVector s)

theorem coreLambda_action (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ coreLambda s =
      (Real.pi + mixedCharge s / 2) • ramanujanVonMangoldtVector s +
        (logarithmicCharge s / 2) • ramanujanTotientVector s := by
  have hF : derivedCore s *ᵥ coreLambda s = ramanujanVonMangoldtVector s := by
    rw [coreLambda, Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs ho,
      Matrix.one_mulVec]
  rw [gram_eq_rankTwo_derivedCore, rankTwoMatrix_mulVec, hF,
    coreLambda_totient_pair]
  change Real.pi • ramanujanVonMangoldtVector s +
    (mixedCharge s / 2) • ramanujanVonMangoldtVector s +
    (logarithmicCharge s / 2) • ramanujanTotientVector s = _
  rw [add_smul]

theorem coreTotient_action (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ coreTotient s =
      (inverseCharge s / 2) • ramanujanVonMangoldtVector s +
        (Real.pi + mixedCharge s / 2) • ramanujanTotientVector s := by
  have hF : derivedCore s *ᵥ coreTotient s = ramanujanTotientVector s := by
    rw [coreTotient, Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs ho,
      Matrix.one_mulVec]
  rw [gram_eq_rankTwo_derivedCore, rankTwoMatrix_mulVec, hF]
  change Real.pi • ramanujanTotientVector s +
    (inverseCharge s / 2) • ramanujanVonMangoldtVector s +
    (mixedCharge s / 2) • ramanujanTotientVector s = _
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem projection_normalEquation (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ projectionCoefficients s = ramanujanVonMangoldtVector s := by
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [projectionCoefficients, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    coreTotient_action s hs ho, coreLambda_action s hs ho]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hT]
  unfold shiftedDeterminant
  ring

theorem totientDual_normalEquation (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ramanujanGramMatrix s *ᵥ totientDual s = ramanujanTotientVector s := by
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [totientDual, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul,
    coreLambda_action s hs ho, coreTotient_action s hs ho]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hT]
  unfold shiftedDeterminant
  ring

theorem projection_pairing (s : Finset ℕ) :
    ramanujanVonMangoldtVector s ⬝ᵥ projectionCoefficients s = sourceProjectionCharge s := by
  rw [projectionCoefficients]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul]
  change (2 / shiftedDeterminant s) *
    (logarithmicCharge s * mixedCharge s -
      (2 * Real.pi + mixedCharge s) * logarithmicCharge s) = _
  unfold sourceProjectionCharge
  ring

theorem totientDual_pairing (s : Finset ℕ) :
    ramanujanTotientVector s ⬝ᵥ totientDual s =
      -4 * Real.pi * inverseCharge s / shiftedDeterminant s := by
  rw [totientDual]
  simp only [dotProduct_smul, dotProduct_sub, smul_eq_mul, coreLambda_totient_pair]
  change (2 / shiftedDeterminant s) *
    (inverseCharge s * mixedCharge s -
      (2 * Real.pi + mixedCharge s) * inverseCharge s) = _
  ring

theorem gram_transpose (s : Finset ℕ) : (ramanujanGramMatrix s)ᵀ = ramanujanGramMatrix s := by
  ext i j
  exact paretoInner_comm _ _

theorem gram_pair_symm (s : Finset ℕ) (u v : s → ℝ) :
    u ⬝ᵥ (ramanujanGramMatrix s *ᵥ v) = v ⬝ᵥ (ramanujanGramMatrix s *ᵥ u) := by
  simpa only [gram_transpose] using
    Matrix.dotProduct_transpose_mulVec (ramanujanGramMatrix s) u v

theorem gram_quadratic_nonneg (s : Finset ℕ) (c : s → ℝ) :
    0 ≤ c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c) := by
  rw [← synthesis_gram]
  exact paretoInner_self_nonneg _

theorem projection_error (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (projectionCoefficients s)) = 1 - sourceProjectionCharge s := by
  rw [synthesis_error, projection_normalEquation s hs ho,
    dotProduct_comm (projectionCoefficients s), projection_pairing]
  ring

/-- Complete optimal error plus the actual full Gram square of the displacement. -/
theorem projection_error_decomposition (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ) :
    paretoError (synthesis s c) = 1 - sourceProjectionCharge s +
      (c - projectionCoefficients s) ⬝ᵥ
        (ramanujanGramMatrix s *ᵥ (c - projectionCoefficients s)) := by
  rw [synthesis_error, Matrix.mulVec_sub, dotProduct_sub,
    sub_dotProduct, sub_dotProduct, projection_normalEquation s hs ho,
    gram_pair_symm s (projectionCoefficients s) c,
    projection_normalEquation s hs ho,
    dotProduct_comm (projectionCoefficients s) (ramanujanVonMangoldtVector s), projection_pairing]
  rw [dotProduct_comm c (ramanujanVonMangoldtVector s)]
  ring

theorem sourceProjectionCharge_le_one (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s ≤ 1 := by
  have he : 0 ≤ paretoError (synthesis s (projectionCoefficients s)) :=
    paretoInner_self_nonneg _
  rw [projection_error s hs ho] at he
  linarith

theorem logarithmicCharge_control (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    4 * Real.pi * (-logarithmicCharge s) ≤ shiftedDeterminant s := by
  have hq := sourceProjectionCharge_le_one s hs ho
  exact (div_le_one (shiftedDeterminant_pos s hs ho)).mp hq

theorem totient_cauchy (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) (c : s → ℝ) :
    (ramanujanTotientVector s ⬝ᵥ c) ^ 2 ≤
      (-4 * Real.pi * inverseCharge s / shiftedDeterminant s) *
        (c ⬝ᵥ (ramanujanGramMatrix s *ᵥ c)) := by
  have h := source_pair_cauchy (ramanujanGramMatrix s) c (totientDual s)
    (gram_transpose s) (gram_quadratic_nonneg s)
  rw [totientDual_normalEquation s hs ho, dotProduct_comm c,
    dotProduct_comm (totientDual s),
    totientDual_pairing] at h
  nlinarith only [h]

/-- Identification with the existing inverse obtained from actual packet independence. -/
theorem projection_eq_actual_gramSolve (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    projectionCoefficients s = ramanujanGramSolve s hs (ramanujanVonMangoldtVector s) := by
  apply sub_eq_zero.mp
  apply ramanujanGramAction_eq_zero s hs
  rw [← ramanujanGramMatrix_mulVec, Matrix.mulVec_sub,
    projection_normalEquation s hs ho, ramanujanGramMatrix_mulVec_solve, sub_self]

theorem projectionCharge_eq_actual_inverse_gram (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s = ramanujanVonMangoldtVector s ⬝ᵥ
      ramanujanGramSolve s hs (ramanujanVonMangoldtVector s) := by
  rw [← projection_eq_actual_gramSolve s hs ho]
  exact (projection_pairing s).symm

/-- Exact finite ordinary-mean penalty, including its complete source square. -/
theorem meanOne_projection_error_gap (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis s (constrainedOptimizer s)) -
      paretoError (synthesis s (projectionCoefficients s)) =
        4 * Real.pi * (2 * Real.pi + mixedCharge s) ^ 2 /
          ((-inverseCharge s) * shiftedDeterminant s) := by
  have hC := ne_of_lt (inverseCharge_neg s hs ho)
  have hT := ne_of_gt (shiftedDeterminant_pos s hs ho)
  rw [constrainedOptimizer_error s hs ho, projection_error s hs ho]
  unfold sourceProjectionCharge
  field_simp [hC, hT]
  unfold shiftedDeterminant
  ring

end RiemannResearch.RH.Pareto.PhysicalSourceProjection

/-!
# Actual projected finite errors and the normalized tail budget

The legal packet and odd-prime
hypotheses identify its explicit coefficients with the actual full Gram
optimizer through `projection_normalEquation` and
`projection_eq_actual_gramSolve`. The common-period physical site provides
the strictly positive finite error floor without a Baker hypothesis.

Source: RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 10, states the
head choice N_n + 1 ≥ 2^n [L_n(L_n + 1)]² and the resulting summable error
allowance. The head horizon is free after fixing each dictionary and its
projected error. This formalizes that dependency; it does not establish
gain divergence, compensated-source divergence, or RH. The actual tail
provider and the chosen-horizon inequality remain explicit hypotheses.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PhysicalSourceProjection

open PhysicalPacketCore PhysicalSchurCoupling
open RiemannResearch.Analysis.CompensatedSourceCertificate

/-- The literal complete projected error, with its Gram optimizer identified
by legal finite packets, supplies the paper's geometric normalization floor.
No mean nonvanishing or lower bound on an actual gain is assumed. -/
theorem projection_normalizedTailError_le_geometric
    (s : Finset ℕ) (L N n : ℕ) (τ : ℝ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (hL : 0 < L) (hperiod : ∀ q ∈ s, q ∣ L)
    (hτ : τ ≤ 1 / ((N : ℝ) + 1))
    (hN : (2 : ℝ) ^ n * ((L : ℝ) * ((L : ℝ) + 1)) ^ 2 ≤
      (N : ℝ) + 1) :
    τ / (paretoError (synthesis s (projectionCoefficients s))) ^ 2 ≤
      (1 / 2 : ℝ) ^ n := by
  have hfloor : 1 / ((L : ℝ) * ((L : ℝ) + 1)) ≤
      1 - sourceProjectionCharge s := by
    have h := synthesis_error_floor s (projectionCoefficients s) L hperiod
    simpa only [positiveWeight, projection_error s hs ho] using h
  rw [projection_error s hs ho]
  exact normalizedTailError_le_geometric_of_stage_bound
    (1 - sourceProjectionCharge s) τ L N n hL hfloor hτ hN

/-- The explicit freely chosen physical horizons discharge the normalized
error summability provider for the actual finite projected errors. The
tail errors and complete endpoint N n + 1 are retained. -/
theorem projection_normalizedTailError_summable
    (s : ℕ → Finset ℕ) (L N : ℕ → ℕ) (τ : ℕ → ℝ)
    (hs : ∀ n, ∀ q ∈ s n, 1 < q)
    (ho : ∀ n, ∃ p ∈ s n, p.Prime ∧ 2 < p)
    (hL : ∀ n, 0 < L n) (hperiod : ∀ n, ∀ q ∈ s n, q ∣ L n)
    (hτ0 : ∀ n, 0 ≤ τ n)
    (hτ : ∀ n, τ n ≤ 1 / ((N n : ℝ) + 1))
    (hN : ∀ n, (2 : ℝ) ^ n * ((L n : ℝ) * ((L n : ℝ) + 1)) ^ 2 ≤
      (N n : ℝ) + 1) :
    Summable (fun n =>
      τ n / (paretoError (synthesis (s n) (projectionCoefficients (s n)))) ^ 2) := by
  have hfloor (n : ℕ) : 1 / ((L n : ℝ) * ((L n : ℝ) + 1)) ≤
      1 - sourceProjectionCharge (s n) := by
    have h := synthesis_error_floor (s n) (projectionCoefficients (s n))
      (L n) (hperiod n)
    simpa only [positiveWeight, projection_error (s n) (hs n) (ho n)] using h
  have hsum := normalizedTailError_summable_of_stage_bound
    (fun n => 1 - sourceProjectionCharge (s n)) τ L N
    hL hfloor hτ0 hτ hN
  have herr (n : ℕ) :
      paretoError (synthesis (s n) (projectionCoefficients (s n))) =
        1 - sourceProjectionCharge (s n) := projection_error (s n) (hs n) (ho n)
  simpa only [herr] using hsum

end RiemannResearch.RH.Pareto.PhysicalSourceProjection

/- Requested future kernel axiom audit; these commands have not been run. -/

/-!
# Explicit physical horizons at the actual finite projected errors

Source: RH_Actual_Arithmetic_Advances_2026-10-07.pdf, Section 10. Its fixed
dictionary error floor and explicit head N = 2^n [L(L+1)]² give a summable
normalized source-error allowance. Here the horizon is also enlarged to meet
an arbitrary requested floor. The imported horizon cofinality theorem applies
to this same explicit sequence; no separate horizon inequality is supplied.

The first two consumers use the literal head allowance 1/(N+1), so they need
no supplied tail bound. The final consumer retains the actual tail-error
sequence and its head bound, the actual gain E_n-E_{n+1}, and the full source
comparison. It establishes an equivalence, not either divergence statement
or RH. The legal packet and odd-prime conditions identify the coefficients
as the existing actual full Gram optimizer; no Baker provider is used.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PhysicalSourceProjection

open PhysicalPacketCore PhysicalSchurCoupling
open RiemannResearch.Analysis.CompensatedSourceCertificate

/-- The fully constructed head allowance obeys the geometric normalized
budget at the actual projected error, with the complete N+1 endpoint. -/
theorem projection_normalizedHeadAllowance_le_geometric
    (s : Finset ℕ) (L F n : ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (hL : 0 < L) (hperiod : ∀ q ∈ s, q ∣ L) :
    (1 / ((normalizedTailHorizonWithFloor L F n : ℝ) + 1)) /
      (paretoError (synthesis s (projectionCoefficients s))) ^ 2 ≤
        (1 / 2 : ℝ) ^ n := by
  exact projection_normalizedTailError_le_geometric
    s L (normalizedTailHorizonWithFloor L F n) n
    (1 / ((normalizedTailHorizonWithFloor L F n : ℝ) + 1))
    hs ho hL hperiod le_rfl
    (normalizedTailHorizonWithFloor_paper_bound L F n)

/-- The explicit cofinal horizons discharge the normalized head allowance
for actual finite errors without supplying a tail or horizon inequality. -/
theorem projection_normalizedHeadAllowance_summable
    (s : ℕ → Finset ℕ) (L F : ℕ → ℕ)
    (hs : ∀ n, ∀ q ∈ s n, 1 < q)
    (ho : ∀ n, ∃ p ∈ s n, p.Prime ∧ 2 < p)
    (hL : ∀ n, 0 < L n) (hperiod : ∀ n, ∀ q ∈ s n, q ∣ L n) :
    Summable (fun n =>
      (1 / ((normalizedTailHorizonWithFloor (L n) (F n) n : ℝ) + 1)) /
        (paretoError (synthesis (s n) (projectionCoefficients (s n)))) ^ 2) := by
  exact projection_normalizedTailError_summable s L
    (fun n => normalizedTailHorizonWithFloor (L n) (F n) n)
    (fun n => 1 / ((normalizedTailHorizonWithFloor (L n) (F n) n : ℝ) + 1))
    hs ho hL hperiod
    (fun n => div_nonneg zero_le_one
      (add_nonneg (Nat.cast_nonneg _) zero_le_one))
    (fun _ => le_rfl)
    (fun n => normalizedTailHorizonWithFloor_paper_bound (L n) (F n) n)

/-- At the explicit horizons, the actual normalized gain and compensated
certificate have equivalent cumulative divergence. Gain nonnegativity and
the full source comparison remain explicit; no divergence is asserted. -/
theorem projection_normalizedCertificate_divergence_iff_explicit_horizon
    (s : ℕ → Finset ℕ) (L F : ℕ → ℕ) (A τ : ℕ → ℝ)
    (hs : ∀ n, ∀ q ∈ s n, 1 < q)
    (ho : ∀ n, ∃ p ∈ s n, p.Prime ∧ 2 < p)
    (hL : ∀ n, 0 < L n) (hperiod : ∀ n, ∀ q ∈ s n, q ∣ L n)
    (hτ0 : ∀ n, 0 ≤ τ n)
    (hτ : ∀ n, τ n ≤
      1 / ((normalizedTailHorizonWithFloor (L n) (F n) n : ℝ) + 1)) :
    let E : ℕ → ℝ := fun n =>
      paretoError (synthesis (s n) (projectionCoefficients (s n)))
    (∀ n, 0 ≤ E n - E (n + 1)) →
    (∀ n, |Real.sqrt (E n - E (n + 1)) - Real.sqrt (A n)| ≤ Real.sqrt (τ n)) →
    (Tendsto (fun J => ∑ n ∈ Finset.range J, (E n - E (n + 1)) / (E n) ^ 2)
      atTop atTop ↔
    Tendsto (fun J => ∑ n ∈ Finset.range J,
      gainCertificate (A n) (τ n) / (E n) ^ 2) atTop atTop) := by
  dsimp only
  intro hgain hsource
  let E : ℕ → ℝ := fun n =>
    paretoError (synthesis (s n) (projectionCoefficients (s n)))
  have hErrorNorm : Summable (fun n => τ n / (E n) ^ 2) := by
    exact Summable.of_nonneg_of_le
      (fun n => div_nonneg (hτ0 n) (sq_nonneg (E n)))
      (fun n => div_le_div_of_nonneg_right (hτ n) (sq_nonneg (E n)))
      (projection_normalizedHeadAllowance_summable s L F hs ho hL hperiod)
  have hError : Summable (fun n => (1 / (E n) ^ 2) * τ n) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hErrorNorm
  have hdiv := gainCertificate_weighted_divergence_iff
    (fun n => E n - E (n + 1)) A τ (fun n => 1 / (E n) ^ 2)
    hgain hτ0 (fun n => div_nonneg zero_le_one (sq_nonneg (E n))) hsource hError
  simpa only [E, div_eq_mul_inv, one_mul, mul_comm] using hdiv

end RiemannResearch.RH.Pareto.PhysicalSourceProjection

/- Root owns all future kernel checks and axiom audits. -/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Sharp structural correction transfer and finite norm consumers

These generic lemmas retain all signed pairings and correction squares.
They do not assert an analytic digamma, infinite physical norm, or RH input.
The step-space application supplies the displayed inner-product compatibility
and identifies the abstract norm constants with the literal physical ones.
-/

noncomputable section

open scoped InnerProductSpace

namespace RiemannResearch.Analysis.StepCorrectionGain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Squared real scalar action, independent of the scalar's sign. -/
theorem real_smul_norm_sq (a : ℝ) (x : H) :
    ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- Cauchy--Schwarz in the squared form used by the sharp transfer.
The proof uses a legal norm square, so no absolute values erase a sign. -/
theorem inner_sq_le_norm_sq_mul_norm_sq (h c : H) :
    ⟪h, c⟫_ℝ ^ 2 ≤ ‖h‖ ^ 2 * ‖c‖ ^ 2 := by
  by_cases hc : ‖c‖ ^ 2 = 0
  · have hcnorm : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
    have hc0 : c = 0 := norm_eq_zero.mp hcnorm
    simp [hc0]
  · have hcbase : ‖c‖ ≠ 0 := by
      intro hz
      apply hc
      rw [hz]
      ring
    have hcompletion :
        ‖h - (⟪h, c⟫_ℝ / ‖c‖ ^ 2) • c‖ ^ 2 =
          ‖h‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2 / ‖c‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq]
      field_simp [hc, hcbase]
      <;> ring
    have hnonneg : 0 ≤ ‖h‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2 / ‖c‖ ^ 2 := by
      rw [← hcompletion]
      exact sq_nonneg _
    have hmult := mul_nonneg (sq_nonneg ‖c‖) hnonneg
    have halgebra :
        ‖c‖ ^ 2 * (‖h‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2 / ‖c‖ ^ 2) =
          ‖h‖ ^ 2 * ‖c‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2 := by
      field_simp [hc, hcbase]
      <;> ring
    rw [halgebra] at hmult
    linarith

/-- Orthogonality to the removed component supplies the exact source law. -/
theorem correction_source_of_orthogonal (h c ρ : H)
    (hortho : ⟪h, ρ - c⟫_ℝ = 0) :
    ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ := by
  rw [inner_sub_right] at hortho
  linarith

/-- Exact signed correction error before estimating its cross term. -/
theorem correction_error_sq (h c ρ : H) (a : ℝ)
    (hsource : ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ) :
    ‖h - a • ρ‖ ^ 2 =
      ‖h‖ ^ 2 - 2 * a * ⟪h, c⟫_ℝ + a ^ 2 * ‖ρ‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq, hsource]
  ring

/-- The transfer gap retains a coefficient square and a Cauchy gap. -/
theorem correction_transfer_gap (h c ρ : H) (a : ℝ)
    (hsource : ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ) :
    ‖ρ‖ ^ 2 * ‖h - a • ρ‖ ^ 2 -
        (‖ρ‖ ^ 2 - ‖c‖ ^ 2) * ‖h‖ ^ 2 =
      (‖ρ‖ ^ 2 * a - ⟪h, c⟫_ℝ) ^ 2 +
        (‖h‖ ^ 2 * ‖c‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2) := by
  rw [correction_error_sq h c ρ a hsource]
  ring

/-- Denominator-cleared sharp structural transfer, without division or a
spectral-margin assumption. -/
theorem correction_transfer_mul (h c ρ : H) (a : ℝ)
    (hsource : ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ) :
    (‖ρ‖ ^ 2 - ‖c‖ ^ 2) * ‖h‖ ^ 2 ≤
      ‖ρ‖ ^ 2 * ‖h - a • ρ‖ ^ 2 := by
  have hgap := correction_transfer_gap h c ρ a hsource
  have hcauchy := inner_sq_le_norm_sq_mul_norm_sq h c
  have hsquare := sq_nonneg (‖ρ‖ ^ 2 * a - ⟪h, c⟫_ℝ)
  linarith

/-- A positive removed-component energy converts the exact transfer into
the useful quotient bound. -/
theorem correction_transfer_sq (h c ρ : H) (a : ℝ)
    (hsource : ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ)
    (hgap : 0 < ‖ρ‖ ^ 2 - ‖c‖ ^ 2) :
    ‖h‖ ^ 2 ≤
      (‖ρ‖ ^ 2 * ‖h - a • ρ‖ ^ 2) / (‖ρ‖ ^ 2 - ‖c‖ ^ 2) := by
  apply (le_div_iff₀ hgap).2
  simpa [mul_comm] using correction_transfer_mul h c ρ a hsource

/-- Divided completion retains the literal signed source. -/
theorem correction_completed_square (h c ρ : H) (a : ℝ)
    (hsource : ⟪h, ρ⟫_ℝ = ⟪h, c⟫_ℝ)
    (hρ : 0 < ‖ρ‖ ^ 2) :
    ‖h - a • ρ‖ ^ 2 =
      ‖h‖ ^ 2 - ⟪h, c⟫_ℝ ^ 2 / ‖ρ‖ ^ 2 +
        ‖ρ‖ ^ 2 * (a - ⟪h, c⟫_ℝ / ‖ρ‖ ^ 2) ^ 2 := by
  have hρbase : ‖ρ‖ ≠ 0 := by
    intro hz
    rw [hz] at hρ
    linarith
  rw [correction_error_sq h c ρ a hsource]
  field_simp [ne_of_gt hρ, hρbase]
  <;> ring

/-- The exact decomposition into projected raw error and removed energy.
The projected raw error is not asserted to be a legal finite atom trial. -/
theorem correction_orthogonal_split (h c ρ : H) (a : ℝ)
    (hh : ⟪h, ρ - c⟫_ℝ = 0)
    (hc : ⟪ρ - c, c⟫_ℝ = 0) :
    ‖h - a • ρ‖ ^ 2 =
      ‖h - a • c‖ ^ 2 + a ^ 2 * ‖ρ - c‖ ^ 2 := by
  have hsource := correction_source_of_orthogonal h c ρ hh
  have hprojection : ⟪ρ, c⟫_ℝ = ‖c‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hc
    linarith
  have hremoved : ‖ρ - c‖ ^ 2 = ‖ρ‖ ^ 2 - ‖c‖ ^ 2 := by
    rw [norm_sub_sq_real, hprojection]
    ring
  rw [correction_error_sq h c ρ a hsource, hremoved,
    norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq]
  ring

/-- An equality witness proves sharpness on the abstract structural space.
It is not an assertion about a specific damped Möbius sequence. -/
theorem correction_transfer_equality (c ρ : H)
    (hsource : ⟪c, ρ⟫_ℝ = ‖c‖ ^ 2)
    (hρ : 0 < ‖ρ‖ ^ 2) :
    ‖ρ‖ ^ 2 * ‖c - (‖c‖ ^ 2 / ‖ρ‖ ^ 2) • ρ‖ ^ 2 =
      (‖ρ‖ ^ 2 - ‖c‖ ^ 2) * ‖c‖ ^ 2 := by
  have hρbase : ‖ρ‖ ≠ 0 := by
    intro hz
    rw [hz] at hρ
    linarith
  rw [norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq, hsource]
  field_simp [ne_of_gt hρ, hρbase]
  <;> ring

/-- Exact scalar completion needed to turn a complete trapezoidal identity
and its actual harmonic lower bound into a finite two-moment norm certificate. -/
theorem trapezoid_two_moment_norm_bound (d C l harmonic a₁ a₂ tail G : ℝ)
    (hd : 0 < d) (htail : 0 ≤ tail)
    (hharmonic : 1 / (4 * d) - 1 / (48 * d ^ 2) ≤ harmonic)
    (hphysical : d * G = C - l / d - harmonic - 3 / (4 * d) -
      2 * (a₁ / (6 * d ^ 2) +
        a₂ * (1 / (3 * d ^ 2) - 1 / (30 * d ^ 4)) + tail)) :
    G ≤ C / d - (l + 1) / d ^ 2 -
      ((a₁ + 2 * a₂) / 3 - 1 / 48) / d ^ 3 + a₂ / (15 * d ^ 5) := by
  have hcompletion :
      d * (C / d - (l + 1) / d ^ 2 -
        ((a₁ + 2 * a₂) / 3 - 1 / 48) / d ^ 3 +
          a₂ / (15 * d ^ 5) - G) =
        harmonic - (1 / (4 * d) - 1 / (48 * d ^ 2)) + 2 * tail := by
    rw [mul_sub, hphysical]
    field_simp [ne_of_gt hd]
    <;> ring
  have hnonneg :
      0 ≤ d * (C / d - (l + 1) / d ^ 2 -
        ((a₁ + 2 * a₂) / 3 - 1 / 48) / d ^ 3 +
          a₂ / (15 * d ^ 5) - G) := by
    rw [hcompletion]
    linarith
  nlinarith

/-- Positive complete correction tails yield finite two-sided norm brackets.
The analytic adapter must supply the complete identity and its tail bound. -/
theorem finite_trapezoid_norm_brackets (d base finiteSum tail remainder G : ℝ)
    (hd : 0 < d) (htail : 0 ≤ tail)
    (htailbound : 2 * tail ≤ remainder / d)
    (hphysical : d * G = base - 2 * (finiteSum + tail)) :
    (base - 2 * finiteSum - remainder / d) / d ≤ G ∧
      G ≤ (base - 2 * finiteSum) / d := by
  constructor
  · apply (div_le_iff₀ hd).2
    rw [mul_comm G d, hphysical]
    linarith
  · apply (le_div_iff₀ hd).2
    rw [mul_comm G d, hphysical]
    linarith

end RiemannResearch.Analysis.StepCorrectionGain

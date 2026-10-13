import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Shift-aware core/tail certificates

Source: `RH_Early_Operator_Algebra_Program_Critical_Audit_2026-10-12`,
Sections 4 and 10. The intended RH consumer is a correctly normalized localized
Weil form: its obsolete coefficient model differs by a positive scalar shift.

The polynomial certificate below subtracts that shift from both diagonal blocks.
It distinguishes a Schur-complement margin from a lower bound in the original
Hilbert norm. The arithmetic identification, coefficient enclosures, coupling
bound and positive tail bound remain separate obligations; no Weil positivity
or RH assertion follows without them.
-/

namespace RiemannResearch.LinearAlgebra

/-- The quadratic form of the real symmetric matrix `[[a,b],[b,c]]`. -/
def blockQuadratic (a b c x y : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + c * y ^ 2

/-- A scalar Schur complement; using it as a certificate requires a positive tail. -/
noncomputable def scalarSchurMargin (a b c : ℝ) : ℝ := a - b ^ 2 / c

/-- The normalization shift acts on both diagonal blocks. -/
theorem blockQuadratic_sub_scalar (a b c δ x y : ℝ) :
    blockQuadratic (a - δ) b (c - δ) x y =
      blockQuadratic a b c x y - δ * (x ^ 2 + y ^ 2) := by
  simp only [blockQuadratic]
  ring

/-- An exact sum-of-squares identity for a proposed global lower bound `ell`. -/
theorem shifted_block_certificate_identity (a c h δ ell x y : ℝ) :
    (c - δ - ell) *
        (blockQuadratic (a - δ) (-h) (c - δ) x y -
          ell * (x ^ 2 + y ^ 2)) =
      ((c - δ - ell) * y - h * x) ^ 2 +
        ((a - δ - ell) * (c - δ - ell) - h ^ 2) * x ^ 2 := by
  simp only [blockQuadratic]
  ring

/-- A polynomial certificate for the whole quadratic form, with no square roots. -/
theorem shifted_block_lower_bound
    (a c h δ ell x y : ℝ)
    (hc : 0 < c - δ - ell)
    (hbudget : h ^ 2 ≤ (a - δ - ell) * (c - δ - ell)) :
    ell * (x ^ 2 + y ^ 2) ≤
      blockQuadratic (a - δ) (-h) (c - δ) x y := by
  have hnn :
      0 ≤ (c - δ - ell) *
        (blockQuadratic (a - δ) (-h) (c - δ) x y -
          ell * (x ^ 2 + y ^ 2)) := by
    rw [shifted_block_certificate_identity]
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (sub_nonneg.mpr hbudget) (sq_nonneg _))
  have hdiff :
      0 ≤ blockQuadratic (a - δ) (-h) (c - δ) x y -
        ell * (x ^ 2 + y ^ 2) := by
    by_contra hn
    exact (not_lt_of_ge hnn)
      (mul_neg_of_pos_of_neg hc (lt_of_not_ge hn))
  linarith

/-- Transfer a core/tail envelope for a shifted model to the actual form value.
Here `x,y` may be the norms of orthogonal core and tail components. -/
theorem lower_bound_of_shifted_envelope
    (q qTilde a c h δ ell x y : ℝ)
    (henvelope : blockQuadratic a (-h) c x y ≤ qTilde)
    (hshift : q = qTilde - δ * (x ^ 2 + y ^ 2))
    (hc : 0 < c - δ - ell)
    (hbudget : h ^ 2 ≤ (a - δ - ell) * (c - δ - ell)) :
    ell * (x ^ 2 + y ^ 2) ≤ q := by
  rw [hshift]
  calc
    ell * (x ^ 2 + y ^ 2) ≤
        blockQuadratic (a - δ) (-h) (c - δ) x y :=
      shifted_block_lower_bound a c h δ ell x y hc hbudget
    _ = blockQuadratic a (-h) c x y - δ * (x ^ 2 + y ^ 2) :=
      blockQuadratic_sub_scalar a (-h) c δ x y
    _ ≤ qTilde - δ * (x ^ 2 + y ^ 2) :=
      sub_le_sub_right henvelope _

/-- Nonnegativity follows from the zero-target version of the certificate. -/
theorem nonneg_of_shifted_envelope
    (q qTilde a c h δ x y : ℝ)
    (henvelope : blockQuadratic a (-h) c x y ≤ qTilde)
    (hshift : q = qTilde - δ * (x ^ 2 + y ^ 2))
    (hc : 0 < c - δ)
    (hbudget : h ^ 2 ≤ (a - δ) * (c - δ)) : 0 ≤ q := by
  simpa using lower_bound_of_shifted_envelope
    q qTilde a c h δ 0 x y henvelope hshift (by simpa using hc)
      (by simpa using hbudget)

/-- Subtracting a normalization shift also changes the inverse-tail term. -/
theorem scalarSchurMargin_sub_scalar
    (a b c δ : ℝ) (hc : c ≠ 0) (hcd : c - δ ≠ 0) :
    scalarSchurMargin (a - δ) b (c - δ) =
      scalarSchurMargin a b c - δ - δ * b ^ 2 / (c * (c - δ)) := by
  simp only [scalarSchurMargin]
  field_simp [hc, hcd]
  ring

/-- Schur margin `1` is not a whole-form lower bound for `[[2,1],[1,1]]`. -/
theorem schur_margin_not_global_lower_bound :
    scalarSchurMargin 2 1 1 = 1 ∧
      blockQuadratic 2 1 1 1 (-1) <
        scalarSchurMargin 2 1 1 * ((1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) := by
  norm_num [scalarSchurMargin, blockQuadratic]

/-- A naive subtraction leaves a positive margin although the corrected form
has a negative value at `(1,-2)`. All quantities are exact rational numbers. -/
theorem naive_shifted_schur_counterexample :
    0 < scalarSchurMargin 2 1 1 - (1 / 2 : ℝ) ∧
      scalarSchurMargin (2 - 1 / 2) 1 (1 - 1 / 2) = -(1 / 2 : ℝ) ∧
      blockQuadratic (2 - 1 / 2) 1 (1 - 1 / 2) 1 (-2) = -(1 / 2 : ℝ) ∧
      blockQuadratic (2 - 1 / 2) 1 (1 - 1 / 2) 1 (-2) < 0 := by
  norm_num [scalarSchurMargin, blockQuadratic]

end RiemannResearch.LinearAlgebra

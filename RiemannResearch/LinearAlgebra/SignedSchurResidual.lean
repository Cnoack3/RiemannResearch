import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair

/-!
# Coercive signed Schur certificates with a trial solve

Source: user-provided argument,
`RH_Layer_Cake_Sublevel_Program_and_Next_Attack_2026-09-16_Continued.md`,
Sections 28 and 40. This module formalizes the algebraic certificate, including
its residual correction. It does not assert an RH-specific block bound.

The real inner-product formulation also expresses the real quadratic value
of a Hermitian block after its real inner-product structure is supplied.
No finite dimensionality, completeness, or inverse is needed for the
coercive certificate. The separate exact inverse identity assumes an actual
linear equivalence, rather than interpreting an arbitrary symbol as an inverse.
-/

namespace RiemannResearch.LinearAlgebra
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The full signed quadratic value of the block with old coordinate `u`,
cross-block value `b`, and new-coordinate diagonal value `c`. -/
def signedBlockValue (A : H →ₗ[ℝ] H) (b : H) (c : ℝ) (u : H) : ℝ :=
  inner ℝ u (A u) + 2 * inner ℝ u b + c

/-- The new-coordinate Schur value associated with a trial solve `x`. -/
def signedSchurTrialValue (A : H →ₗ[ℝ] H) (b : H) (c : ℝ) (x : H) : ℝ :=
  c - 2 * inner ℝ x b + inner ℝ x (A x)

/-- The actual signed residual of the trial solve. -/
def signedSchurTrialResidual (A : H →ₗ[ℝ] H) (b x : H) : H := b - A x

/-- Completing the square about an arbitrary trial vector preserves all
signed cross terms, including the unsolved residual. -/
theorem signedBlockValue_trial_completion
    (A : H →ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (b : H) (c : ℝ) (u x : H) :
    signedBlockValue A b c u =
      inner ℝ (u + x) (A (u + x)) +
        2 * inner ℝ (u + x) (signedSchurTrialResidual A b x) +
        signedSchurTrialValue A b c x := by
  have hcross : inner ℝ x (A u) = inner ℝ u (A x) := by
    rw [hA x u, real_inner_comm]
  simp only [signedBlockValue, signedSchurTrialValue, signedSchurTrialResidual,
    map_add, inner_add_left, inner_add_right, inner_sub_right]
  rw [hcross]
  ring

/-- Coercivity controls a signed linear perturbation with its squared norm.
The proof is an exact norm square; it does not replace signed block entries
by entrywise absolute values. -/
theorem coercive_signed_linear_lower
    (A : H →ₗ[ℝ] H) (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) (v r : H) :
    -(‖r‖ ^ 2 / δ) ≤ inner ℝ v (A v) + 2 * inner ℝ v r := by
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hsquare : 0 ≤ δ * ‖v‖ ^ 2 + 2 * inner ℝ v r + ‖r‖ ^ 2 / δ := by
    calc
      0 ≤ δ * ‖v + (1 / δ) • r‖ ^ 2 :=
        mul_nonneg hδ.le (sq_nonneg _)
      _ = δ * ‖v‖ ^ 2 + 2 * inner ℝ v r + ‖r‖ ^ 2 / δ := by
        rw [norm_add_smul_sq_exact]
        field_simp [hδne]
  linarith [hcoercive v]

/-- A quantitative lower certificate valid for every old-block coordinate.
The only analytic input is the stated coercivity bound for the actual `A`. -/
theorem signedBlockValue_ge_trial_sub_residual
    (A : H →ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (b : H) (c : ℝ) (u x : H) :
    signedSchurTrialValue A b c x - ‖signedSchurTrialResidual A b x‖ ^ 2 / δ ≤
      signedBlockValue A b c u := by
  rw [signedBlockValue_trial_completion A hA b c u x]
  have h := coercive_signed_linear_lower A δ hδ hcoercive
    (u + x) (signedSchurTrialResidual A b x)
  linarith

/-- The trial Schur value dominating the squared residual is sufficient for
positivity. This is the pointwise quadratic-form version of
`S_X ≥ δ⁻¹ R*R`. The domination hypothesis remains a genuine obligation. -/
theorem signedBlockValue_nonneg_of_trial_certificate
    (A : H →ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (b : H) (c : ℝ) (x : H)
    (hcertificate : ‖signedSchurTrialResidual A b x‖ ^ 2 / δ ≤
      signedSchurTrialValue A b c x) (u : H) :
    0 ≤ signedBlockValue A b c u := by
  have h := signedBlockValue_ge_trial_sub_residual A hA δ hδ hcoercive b c u x
  linarith

/-- Exact inverse correction to an arbitrary trial value. `A` is an actual
invertible symmetric linear map, and the residual is computed from `A`. -/
theorem signedSchurTrialValue_inverse_identity
    (A : H ≃ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (b : H) (c : ℝ) (x : H) :
    c - inner ℝ b (A.symm b) =
      signedSchurTrialValue A.toLinearMap b c x -
        inner ℝ (signedSchurTrialResidual A.toLinearMap b x)
          (A.symm (signedSchurTrialResidual A.toLinearMap b x)) := by
  have hinverse : A.symm (b - A x) = A.symm b - x := by simp
  have hcross : inner ℝ (A x) (A.symm b) = inner ℝ x b := by
    rw [← hA x (A.symm b), A.apply_symm_apply]
  change c - inner ℝ b (A.symm b) =
    (c - 2 * inner ℝ x b + inner ℝ x (A x)) -
      inner ℝ (b - A x) (A.symm (b - A x))
  rw [hinverse]
  simp only [inner_sub_left, inner_sub_right]
  rw [hcross, real_inner_comm b x, real_inner_comm (A x) x]
  ring

/-- Coercivity bounds the inverse quadratic value, with the sharp reciprocal
constant used in the residual certificate. -/
theorem coercive_inverse_quadratic_le
    (A : H ≃ₗ[ℝ] H) (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v)) (r : H) :
    inner ℝ r (A.symm r) ≤ ‖r‖ ^ 2 / δ := by
  have h := coercive_signed_linear_lower A.toLinearMap δ hδ hcoercive
    (-(A.symm r)) r
  change -(‖r‖ ^ 2 / δ) ≤
    inner ℝ (-(A.symm r)) (A (-(A.symm r))) +
      2 * inner ℝ (-(A.symm r)) r at h
  simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at h
  simp only [A.apply_symm_apply] at h
  simp only [real_inner_comm r (A.symm r)] at h
  linarith

/-- The true Schur value lies between the trial value and that value minus
the certified residual error. This is the exact signed operator inequality
evaluated on one arbitrary new-block coordinate. -/
theorem signedSchurTrialValue_inverse_bounds
    (A : H ≃ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (b : H) (c : ℝ) (x : H) :
    signedSchurTrialValue A.toLinearMap b c x -
        ‖signedSchurTrialResidual A.toLinearMap b x‖ ^ 2 / δ ≤
      c - inner ℝ b (A.symm b) ∧
    c - inner ℝ b (A.symm b) ≤ signedSchurTrialValue A.toLinearMap b c x := by
  let r := signedSchurTrialResidual A.toLinearMap b x
  have hupper := coercive_inverse_quadratic_le A δ hδ hcoercive r
  have hnonneg : 0 ≤ inner ℝ r (A.symm r) := by
    have h := hcoercive (A.symm r)
    rw [A.apply_symm_apply] at h
    simp only [real_inner_comm r (A.symm r)] at h
    exact (mul_nonneg hδ.le (sq_nonneg _)).trans h
  have he := signedSchurTrialValue_inverse_identity A hA b c x
  change c - inner ℝ b (A.symm b) =
    signedSchurTrialValue A.toLinearMap b c x - inner ℝ r (A.symm r) at he
  change signedSchurTrialValue A.toLinearMap b c x - ‖r‖ ^ 2 / δ ≤
      c - inner ℝ b (A.symm b) ∧
    c - inner ℝ b (A.symm b) ≤ signedSchurTrialValue A.toLinearMap b c x
  constructor <;> linarith

/-- The full two-block certificate, uniform in both coordinates. A trial
map may be arbitrary: linearity is not required for the sufficient bound. -/
theorem signed_two_block_nonneg_of_trial_certificate
    {Y : Type*} (A : H →ₗ[ℝ] H)
    (hA : ∀ u v, inner ℝ u (A v) = inner ℝ (A u) v)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive : ∀ v, δ * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (b : Y → H) (c : Y → ℝ) (X : Y → H)
    (hcertificate : ∀ y, ‖signedSchurTrialResidual A (b y) (X y)‖ ^ 2 / δ ≤
      signedSchurTrialValue A (b y) (c y) (X y)) :
    ∀ u y, 0 ≤ signedBlockValue A (b y) (c y) u := by
  intro u y
  exact signedBlockValue_nonneg_of_trial_certificate A hA δ hδ hcoercive
    (b y) (c y) (X y) (hcertificate y) u

/-- A finite starting level and certified signed Schur steps imply positivity
at every later level. The spaces may change with the level. The coercivity
input may use positivity at the preceding level, as in the increasing
tolerance argument; the residual domination at each step remains explicit.

`hdecomposition` must identify the actual next-level form with the stated
block, including all its signed prime and pole contributions in an RH
application. This theorem does not provide that identification or its bounds. -/
theorem signed_schur_induction_from
    {V Y E : ℕ → Type*}
    [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℝ (E j)]
    (q : (j : ℕ) → V j → ℝ) (A : (j : ℕ) → E j →ₗ[ℝ] E j)
    (b : (j : ℕ) → Y j → E j) (c : (j : ℕ) → Y j → ℝ)
    (X : (j : ℕ) → Y j → E j)
    (old : (j : ℕ) → V (j + 1) → E j)
    (new : (j : ℕ) → V (j + 1) → Y j)
    (δ : ℕ → ℝ) (j₀ : ℕ)
    (hbase : ∀ v, 0 ≤ q j₀ v)
    (hsymm : ∀ j u v, inner ℝ u (A j v) = inner ℝ (A j u) v)
    (hδ : ∀ j, j₀ ≤ j → 0 < δ j)
    (hcoercive : ∀ j, j₀ ≤ j → (∀ v, 0 ≤ q j v) →
      ∀ u, δ j * ‖u‖ ^ 2 ≤ inner ℝ u (A j u))
    (hdecomposition : ∀ j v, q (j + 1) v =
      signedBlockValue (A j) (b j (new j v)) (c j (new j v)) (old j v))
    (hcertificate : ∀ j, j₀ ≤ j → ∀ y,
      ‖signedSchurTrialResidual (A j) (b j y) (X j y)‖ ^ 2 / δ j ≤
        signedSchurTrialValue (A j) (b j y) (c j y) (X j y)) :
    ∀ j, j₀ ≤ j → ∀ v, 0 ≤ q j v := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hbase
  | succ j hj ih =>
    intro v
    rw [hdecomposition]
    exact signedBlockValue_nonneg_of_trial_certificate (A j) (hsymm j)
      (δ j) (hδ j hj) (hcoercive j hj ih)
      (b j (new j v)) (c j (new j v)) (X j (new j v))
      (hcertificate j hj (new j v)) (old j v)

end
end RiemannResearch.LinearAlgebra

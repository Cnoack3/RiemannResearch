import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact elimination of the conductor-four annihilator block

Source: user-provided argument, `Exact_Optimizer_Cancellation_20261008.tex`,
rank-one annihilator screening section. The concrete RH consumer is the
inverse-square optimizer, whose conductor-four dual has squared norm `30/Z`
and reciprocal-coordinate Rayleigh quotient `1/3`.

The complete block positivity hypothesis is an explicit geometric input.
It is used to derive the coupling bound; no arithmetic cancellation estimate
or RH assumption is supplied by this module.
-/

noncomputable section
namespace RiemannResearch.LinearAlgebra.RankOneAnnihilator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact Schur operator after eliminating a unit annihilator whose
original reciprocal-coordinate Rayleigh quotient is `1/3`. -/
def screenedOperator (D : H →ₗ[ℝ] H) (b : H) : H →ₗ[ℝ] H where
  toFun x := D x - ((3 / 4 : ℝ) * inner ℝ b x) • b
  map_add' x y := by
    simp only [map_add, inner_add_right, mul_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, real_inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]
    congr 1
    congr 1
    ring

theorem screenedOperator_energy (D : H →ₗ[ℝ] H) (b x : H) :
    inner ℝ x (screenedOperator D b x) =
      inner ℝ x (D x) - (3 / 4 : ℝ) * (inner ℝ b x) ^ 2 := by
  change inner ℝ x (D x - ((3 / 4 : ℝ) * inner ℝ b x) • b) = _
  rw [inner_sub_right, real_inner_smul_right, real_inner_comm x b]
  ring

/-- Complete the square in the eliminated coordinate, retaining the signed
cross term and the entire remaining quadratic form. -/
theorem screened_block_completion (D : H →ₗ[ℝ] H) (b x : H) (t : ℝ) :
    (4 / 3 : ℝ) * t ^ 2 + 2 * t * inner ℝ b x + inner ℝ x (D x) =
      (4 / 3 : ℝ) * (t + (3 / 4 : ℝ) * inner ℝ b x) ^ 2 +
        inner ℝ x (screenedOperator D b x) := by
  rw [screenedOperator_energy]
  ring

theorem screened_block_minimizes (D : H →ₗ[ℝ] H) (b x : H) (t : ℝ) :
    inner ℝ x (screenedOperator D b x) ≤
      (4 / 3 : ℝ) * t ^ 2 + 2 * t * inner ℝ b x + inner ℝ x (D x) := by
  rw [screened_block_completion]
  exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg _))

theorem screened_block_attains (D : H →ₗ[ℝ] H) (b x : H) :
    (4 / 3 : ℝ) * (-(3 / 4 : ℝ) * inner ℝ b x) ^ 2 +
        2 * (-(3 / 4 : ℝ) * inner ℝ b x) * inner ℝ b x +
        inner ℝ x (D x) = inner ℝ x (screenedOperator D b x) := by
  rw [screened_block_completion]
  simp

/-- A positive ambient operator supplies the full block positivity once its
actual mixed pairings and compression have been identified. This records an
ordinary geometric provider for the positivity input used below. -/
theorem block_nonneg_of_positive_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →ₗ[ℝ] E) (J : H →ₗ[ℝ] E) (φ : E)
    (D : H →ₗ[ℝ] H) (b : H)
    (hG : ∀ y : E, 0 ≤ inner ℝ y (G y))
    (hφ : inner ℝ φ (G φ) = (1 / 3 : ℝ))
    (hmixed_left : ∀ x, inner ℝ φ (G (J x)) = inner ℝ b x)
    (hmixed_right : ∀ x, inner ℝ (J x) (G φ) = inner ℝ b x)
    (hcompression : ∀ x, inner ℝ (J x) (G (J x)) = inner ℝ x (D x)) :
    ∀ (t : ℝ) (x : H),
      0 ≤ (1 / 3 : ℝ) * t ^ 2 + 2 * t * inner ℝ b x + inner ℝ x (D x) := by
  intro t x
  have hp := hG (t • φ + J x)
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hφ,
    hmixed_left x, hmixed_right x, hcompression x] at hp
  convert hp using 1 <;> ring

/-- Positivity of the full original block derives the sharp coupling bound.
This is a geometric consequence, not an additional arithmetic hypothesis. -/
theorem coupling_sq_le_of_block_nonneg (D : H →ₗ[ℝ] H) (b : H)
    (hpositive : ∀ (t : ℝ) (x : H),
      0 ≤ (1 / 3 : ℝ) * t ^ 2 + 2 * t * inner ℝ b x + inner ℝ x (D x))
    (x : H) :
    3 * (inner ℝ b x) ^ 2 ≤ inner ℝ x (D x) := by
  have hp := hpositive (-3 * inner ℝ b x) x
  nlinarith

/-- The entire screened form lies between `3/4` of the original compression
and that compression. The `bb*` term is preserved in the preceding identity. -/
theorem screenedOperator_energy_bounds (D : H →ₗ[ℝ] H) (b : H)
    (hpositive : ∀ (t : ℝ) (x : H),
      0 ≤ (1 / 3 : ℝ) * t ^ 2 + 2 * t * inner ℝ b x + inner ℝ x (D x))
    (x : H) :
    (3 / 4 : ℝ) * inner ℝ x (D x) ≤ inner ℝ x (screenedOperator D b x) ∧
      inner ℝ x (screenedOperator D b x) ≤ inner ℝ x (D x) := by
  rw [screenedOperator_energy]
  have hc := coupling_sq_le_of_block_nonneg D b hpositive x
  have hs := sq_nonneg (inner ℝ b x)
  constructor <;> nlinarith

/-- Exact block normal-equation elimination. Both equations use the complete
coupling. The eliminated scalar is the actual minimizer of the full block. -/
theorem screened_resolvent_normal (D : H →ₗ[ℝ] H) (b r x : H) (t : ℝ)
    (hfirst : (4 / 3 : ℝ) * t + inner ℝ b x = 0)
    (hsecond : t • b + x + D x = r) :
    t = -(3 / 4 : ℝ) * inner ℝ b x ∧ x + screenedOperator D b x = r := by
  have ht : t = -(3 / 4 : ℝ) * inner ℝ b x := by linarith
  refine ⟨ht, ?_⟩
  change x + (D x - ((3 / 4 : ℝ) * inner ℝ b x) • b) = r
  rw [ht] at hsecond
  simpa only [neg_mul, neg_smul, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm] using hsecond

/-- An actual equivalence realizing `I + K` identifies the marked inverse
solution. Invertibility is explicit rather than attached to a formal symbol. -/
theorem screened_resolvent_solution (D : H →ₗ[ℝ] H) (b : H)
    (E : H ≃ₗ[ℝ] H)
    (hE : ∀ x, E x = x + screenedOperator D b x)
    (r x : H) (t : ℝ)
    (hfirst : (4 / 3 : ℝ) * t + inner ℝ b x = 0)
    (hsecond : t • b + x + D x = r) :
    x = E.symm r ∧ t = -(3 / 4 : ℝ) * inner ℝ b (E.symm r) := by
  obtain ⟨ht, hx⟩ := screened_resolvent_normal D b r x t hfirst hsecond
  have hsol : x = E.symm r := by
    apply E.injective
    rw [hE x, E.apply_symm_apply]
    exact hx
  exact ⟨hsol, by simpa only [hsol] using ht⟩

/-- Normalized marked first moment, retaining the complete square. -/
theorem screened_marked_moment (D : H →ₗ[ℝ] H) (b r : H) (e : ℝ) :
    inner ℝ r (screenedOperator D b r) / e =
      inner ℝ r (D r) / e - (3 / 4 : ℝ) * (inner ℝ b r) ^ 2 / e := by
  rw [screenedOperator_energy]
  ring

/-- Exact conductor-four denominator. The complete unnormalized dual pairing
is `(5-4*c₂-c₃)/(12*Z)`, and `30/Z` is its inverse-square norm. -/
theorem conductor_four_marked_moment
    (m c₂ c₃ Z e : ℝ) (hZ : Z ≠ 0) (he : e ≠ 0) :
    m - (3 / 4 : ℝ) * (((5 - 4 * c₂ - c₃) / (12 * Z)) ^ 2 / (30 / Z)) / e =
      m - (5 - 4 * c₂ - c₃) ^ 2 / (5760 * Z * e) := by
  field_simp [hZ, he]
  ring

/-- Exact higher-moment recurrence in unnormalized conductor-four dual
coordinates. `Dx` and `Df` represent the old residual-space compressions.
The correction retains both the finite dual and the compressed dual image. -/
theorem conductor_four_recurrence (Dx Df f : H) (row γ : ℝ) :
    (Dx - (row / γ) • f) -
        ((3 / 4 : ℝ) * (row / γ)) • (Df - (1 / 3 : ℝ) • f) =
      Dx - (3 * row / (4 * γ)) • (f + Df) := by
  have hc : 3 * row / (4 * γ) = (3 / 4 : ℝ) * (row / γ) := by ring
  have hc2 : ((3 / 4 : ℝ) * (row / γ)) * (1 / 3 : ℝ) =
      (1 / 4 : ℝ) * (row / γ) := by ring
  have hc3 : row / γ - (1 / 4 : ℝ) * (row / γ) =
      (3 / 4 : ℝ) * (row / γ) := by ring
  rw [hc, smul_add, smul_sub, smul_smul, hc2]
  calc
    _ = Dx - (row / γ - (1 / 4 : ℝ) * (row / γ)) • f -
        ((3 / 4 : ℝ) * (row / γ)) • Df := by
      rw [sub_smul]
      abel
    _ = _ := by
      rw [hc3]
      abel

end RiemannResearch.LinearAlgebra.RankOneAnnihilator

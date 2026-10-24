import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual finite Gram optimization with soft observation constraints

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The full objective is realized in the Hilbert product of the original space
and the finite Euclidean observation space. Independence of the original
dictionary proves invertibility for every real penalty parameter, including
zero; observation rows may be dependent and requested values inconsistent.
Both complete norm-square remainders precede every comparison estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteRegularizedConstraints
open FiniteHilbertGram

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

abbrev Augmented (H : Type*) (κ : Type*) [Fintype κ] :=
  WithLp 2 (H × EuclideanSpace ℝ κ)

def pair (f : H) (x : κ → ℝ) : Augmented H κ :=
  WithLp.toLp 2 (f, WithLp.toLp 2 x)

def first : Augmented H κ →ₗ[ℝ] H where
  toFun x := x.ofLp.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinate (j : κ) : Augmented H κ →ₗ[ℝ] ℝ where
  toFun x := x.ofLp.2.ofLp j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem augmented_ext {x y : Augmented H κ}
    (hfirst : first x = first y) (hcoord : ∀ j, coordinate j x = coordinate j y) : x = y := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext hfirst
  apply WithLp.ofLp_injective 2
  exact funext hcoord

theorem pair_inner (f g : H) (x y : κ → ℝ) :
    inner ℝ (pair f x) (pair g y) = inner ℝ f g + ∑ j, x j * y j := by
  simp only [pair, WithLp.prod_inner_apply, WithLp.ofLp_toLp, PiLp.inner_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [RCLike.inner_apply', mul_comm]

theorem pair_norm_sq (f : H) (x : κ → ℝ) :
    ‖pair f x‖ ^ 2 = ‖f‖ ^ 2 + ∑ j, (x j) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, pair_inner, real_inner_self_eq_norm_sq]
  simp only [pow_two]

theorem pair_sub (f g : H) (x y : κ → ℝ) :
    pair f x - pair g y = pair (f - g) (x - y) := rfl

def observe (B : Matrix κ ι ℝ) (a : ι → ℝ) (j : κ) : ℝ :=
  ∑ i, a i * B j i

theorem observe_sub (B : Matrix κ ι ℝ) (a c : ι → ℝ) (j : κ) :
    observe B (a - c) j = observe B a j - observe B c j := by
  simp only [observe, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

def observationEnergy (B : Matrix κ ι ℝ) (a : ι → ℝ) : ℝ :=
  ∑ j, (observe B a j) ^ 2

theorem observationEnergy_nonneg (B : Matrix κ ι ℝ) (a : ι → ℝ) :
    0 ≤ observationEnergy B a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem observationEnergy_sub_rev (B : Matrix κ ι ℝ) (a c : ι → ℝ) :
    observationEnergy B (a - c) = observationEnergy B (c - a) := by
  unfold observationEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [observe_sub, observe_sub]
  ring

def rows (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (i : ι) : Augmented H κ :=
  pair (v i) (fun j => ρ * B j i)

def target (f : H) (t : κ → ℝ) (ρ : ℝ) : Augmented H κ :=
  pair f (fun j => ρ * t j)

theorem first_row (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (i : ι) :
    first (rows v B ρ i) = v i := rfl

theorem coordinate_row (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (i : ι) (j : κ) :
    coordinate j (rows v B ρ i) = ρ * B j i := rfl

/-- No rank, feasibility, or positivity condition is required of the soft rows. -/
theorem rows_independent {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (ρ : ℝ) : LinearIndependent ℝ (rows v B ρ) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have h := congrArg (first (H := H) (κ := κ)) ha
  simp only [map_sum, map_smul, first_row, map_zero] at h
  exact Fintype.linearIndependent_iff.mp hv a h

theorem synthesis_rows (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (a : ι → ℝ) :
    Fintype.linearCombination ℝ (rows v B ρ) a =
      pair (Fintype.linearCombination ℝ v a) (fun j => ρ * observe B a j) := by
  apply augmented_ext
  · change first (Fintype.linearCombination ℝ (rows v B ρ) a) =
      Fintype.linearCombination ℝ v a
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, first_row]
  · intro j
    change coordinate j (Fintype.linearCombination ℝ (rows v B ρ) a) = ρ * observe B a j
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, coordinate_row,
      smul_eq_mul, observe, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem synthesis_rows_norm_sq (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (a : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (rows v B ρ) a‖ ^ 2 =
      ‖Fintype.linearCombination ℝ v a‖ ^ 2 + ρ ^ 2 * observationEnergy B a := by
  rw [synthesis_rows, pair_norm_sq]
  simp only [mul_pow, observationEnergy, Finset.mul_sum]

def mismatchEnergy (B : Matrix κ ι ℝ) (t : κ → ℝ) (a : ι → ℝ) : ℝ :=
  ∑ j, (observe B a j - t j) ^ 2

theorem mismatchEnergy_nonneg (B : Matrix κ ι ℝ) (t : κ → ℝ) (a : ι → ℝ) :
    0 ≤ mismatchEnergy B t a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

def objective (v : ι → H) (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ)
    (ρ : ℝ) (a : ι → ℝ) : ℝ :=
  ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 + ρ ^ 2 * mismatchEnergy B t a

theorem objective_eq_augmented (v : ι → H) (B : Matrix κ ι ℝ)
    (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ) :
    objective v B f t ρ a =
      ‖target f t ρ - Fintype.linearCombination ℝ (rows v B ρ) a‖ ^ 2 := by
  rw [synthesis_rows, target, pair_sub, pair_norm_sq]
  unfold objective mismatchEnergy
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

def regularizedGram (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) : Matrix ι ι ℝ :=
  gramMatrix (rows v B ρ)

theorem regularizedGram_entry (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) (i k : ι) :
    regularizedGram v B ρ i k = inner ℝ (v i) (v k) + ρ ^ 2 * ∑ j, B j i * B j k := by
  change inner ℝ (pair (v i) (fun j => ρ * B j i)) (pair (v k) (fun j => ρ * B j k)) = _
  rw [pair_inner, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem regularizedGram_matrix (v : ι → H) (B : Matrix κ ι ℝ) (ρ : ℝ) :
    regularizedGram v B ρ = gramMatrix v + ρ ^ 2 • (B.transpose * B) := by
  ext i k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]
  exact regularizedGram_entry v B ρ i k

theorem regularizedGram_posDef {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (ρ : ℝ) : (regularizedGram v B ρ).PosDef :=
  gramMatrix_posDef (rows_independent hv B ρ)

def source (v : ι → H) (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (i : ι) : ℝ :=
  inner ℝ (v i) f + ρ ^ 2 * ∑ j, B j i * t j

theorem cross_rows_target (v : ι → H) (B : Matrix κ ι ℝ)
    (f : H) (t : κ → ℝ) (ρ : ℝ) : cross (rows v B ρ) (target f t ρ) = source v B f t ρ := by
  funext i
  change inner ℝ (pair (v i) (fun j => ρ * B j i)) (pair f (fun j => ρ * t j)) = _
  rw [pair_inner]
  unfold source
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

def coefficients {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) : ι → ℝ :=
  inverseCoeff (rows_independent hv B ρ) (target f t ρ)

theorem coefficients_inverseGram [DecidableEq ι] {v : ι → H}
    (hv : LinearIndependent ℝ v) (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    coefficients hv B f t ρ = (regularizedGram v B ρ)⁻¹.mulVec (source v B f t ρ) := by
  rw [regularizedGram, gramMatrix_inverseSource (rows_independent hv B ρ)]
  unfold coefficients inverseCoeff
  rw [cross_rows_target]
  rfl

/-- Full normal equation in the original dictionary coordinates. -/
theorem coefficients_normal {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (i : ι) :
    inner ℝ (v i) (Fintype.linearCombination ℝ v (coefficients hv B f t ρ)) +
      ρ ^ 2 * ∑ j, B j i * observe B (coefficients hv B f t ρ) j = source v B f t ρ i := by
  have h := inverseCoeff_normal (rows_independent hv B ρ) (target f t ρ) i
  rw [cross_rows_target] at h
  change inner ℝ (rows v B ρ i)
    (Fintype.linearCombination ℝ (rows v B ρ) (coefficients hv B f t ρ)) = _ at h
  rw [synthesis_rows] at h
  change inner ℝ (pair (v i) (fun j => ρ * B j i))
    (pair (Fintype.linearCombination ℝ v (coefficients hv B f t ρ))
      (fun j => ρ * observe B (coefficients hv B f t ρ) j)) = _ at h
  rw [pair_inner] at h
  convert h using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact minimum value of the actual positive regularized Gram system. -/
theorem coefficients_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) :
    objective v B f t ρ (coefficients hv B f t ρ) =
      ‖f‖ ^ 2 + ρ ^ 2 * ∑ j, (t j) ^ 2 -
        ∑ i, coefficients hv B f t ρ i * source v B f t ρ i := by
  rw [objective_eq_augmented]
  have h := residual_schur_value (rows_independent hv B ρ) (target f t ρ)
  have ht : ‖target f t ρ‖ ^ 2 = ‖f‖ ^ 2 + ρ ^ 2 * ∑ j, (t j) ^ 2 := by
    rw [target, pair_norm_sq]
    simp only [mul_pow, Finset.mul_sum]
  rw [cross_rows_target, ht] at h
  exact h

/-- Both exact remainders survive: physical displacement and observation displacement. -/
theorem coefficients_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ) :
    objective v B f t ρ a = objective v B f t ρ (coefficients hv B f t ρ) +
      ‖Fintype.linearCombination ℝ v (a - coefficients hv B f t ρ)‖ ^ 2 +
        ρ ^ 2 * observationEnergy B (a - coefficients hv B f t ρ) := by
  have h := residual_completion (rows_independent hv B ρ) (target f t ρ) a
  change ‖target f t ρ - Fintype.linearCombination ℝ (rows v B ρ) a‖ ^ 2 =
    ‖target f t ρ - Fintype.linearCombination ℝ (rows v B ρ) (coefficients hv B f t ρ)‖ ^ 2 +
    ‖Fintype.linearCombination ℝ (rows v B ρ) (a - coefficients hv B f t ρ)‖ ^ 2 at h
  rw [← objective_eq_augmented, ← objective_eq_augmented, synthesis_rows_norm_sq] at h
  linarith

theorem coefficients_minimizes {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ) :
    objective v B f t ρ (coefficients hv B f t ρ) ≤ objective v B f t ρ a := by
  rw [coefficients_completion hv B f t ρ a]
  have hp := mul_nonneg (sq_nonneg ρ)
    (observationEnergy_nonneg B (a - coefficients hv B f t ρ))
  linarith [sq_nonneg ‖Fintype.linearCombination ℝ v (a - coefficients hv B f t ρ)‖]

theorem coefficients_optimal_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ) :
    objective v B f t ρ a = objective v B f t ρ (coefficients hv B f t ρ) ↔
      a = coefficients hv B f t ρ := by
  constructor
  · intro he
    have ht := coefficients_completion hv B f t ρ a
    have hp := mul_nonneg (sq_nonneg ρ)
      (observationEnergy_nonneg B (a - coefficients hv B f t ρ))
    have hz : ‖Fintype.linearCombination ℝ v (a - coefficients hv B f t ρ)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ v (a - coefficients hv B f t ρ)‖]
    have hs := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    apply sub_eq_zero.mp
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hs
  · rintro rfl
    rfl

/-- Every exactly feasible trial gives a simultaneous fit/mismatch bound. -/
theorem feasible_comparator {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (a : ι → ℝ)
    (ha : ∀ j, observe B a j = t j) :
    objective v B f t ρ (coefficients hv B f t ρ) ≤
      ‖f - Fintype.linearCombination ℝ v a‖ ^ 2 := by
  have h := coefficients_minimizes hv B f t ρ a
  simpa only [objective, mismatchEnergy, ha, sub_self, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero, add_zero] using h

/-- A feasible trial controls the coordinate mismatch by its excess over the unconstrained minimum. -/
theorem mismatch_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) (a : ι → ℝ)
    (ha : ∀ j, observe B a j = t j) :
    mismatchEnergy B t (coefficients hv B f t ρ) ≤
      (‖f - Fintype.linearCombination ℝ v a‖ ^ 2 -
        ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2) / ρ ^ 2 := by
  have h := feasible_comparator hv B f t ρ a ha
  unfold objective at h
  rw [residual_completion hv f (coefficients hv B f t ρ)] at h
  apply (le_div_iff₀ (sq_pos_iff.mpr hρ)).mpr
  have hn := sq_nonneg
    ‖Fintype.linearCombination ℝ v (coefficients hv B f t ρ - inverseCoeff hv f)‖
  nlinarith

/-- Exact two-penalty tradeoff, including both complete displacement energies. -/
theorem penalty_difference_exact {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) :
    (σ ^ 2 - ρ ^ 2) *
      (mismatchEnergy B t (coefficients hv B f t ρ) -
        mismatchEnergy B t (coefficients hv B f t σ)) =
      2 * ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖ ^ 2 +
      (ρ ^ 2 + σ ^ 2) * observationEnergy B
        (coefficients hv B f t ρ - coefficients hv B f t σ) := by
  have hρ := coefficients_completion hv B f t ρ (coefficients hv B f t σ)
  have hσ := coefficients_completion hv B f t σ (coefficients hv B f t ρ)
  have he : ‖Fintype.linearCombination ℝ v
      (coefficients hv B f t σ - coefficients hv B f t ρ)‖ ^ 2 =
      ‖Fintype.linearCombination ℝ v
        (coefficients hv B f t ρ - coefficients hv B f t σ)‖ ^ 2 := by
    rw [map_sub, map_sub, norm_sub_rev]
  rw [he, observationEnergy_sub_rev B (coefficients hv B f t σ)
    (coefficients hv B f t ρ)] at hρ
  unfold objective at hρ hσ
  nlinarith

theorem mismatch_antitone_of_sq_lt {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 < σ ^ 2) :
    mismatchEnergy B t (coefficients hv B f t σ) ≤
      mismatchEnergy B t (coefficients hv B f t ρ) := by
  have h := penalty_difference_exact hv B f t ρ σ
  have hp := mul_nonneg (add_nonneg (sq_nonneg ρ) (sq_nonneg σ))
    (observationEnergy_nonneg B (coefficients hv B f t ρ - coefficients hv B f t σ))
  nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ v
    (coefficients hv B f t ρ - coefficients hv B f t σ)‖]

theorem fit_error_monotone_of_sq_lt {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 < σ ^ 2) :
    ‖f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ)‖ ^ 2 ≤
      ‖f - Fintype.linearCombination ℝ v (coefficients hv B f t σ)‖ ^ 2 := by
  have h := coefficients_minimizes hv B f t ρ (coefficients hv B f t σ)
  have hm := mismatch_antitone_of_sq_lt hv B f t ρ σ hρσ
  have hp := mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hm)
  unfold objective at h
  nlinarith

/-- The optimizer depends on the square of the penalty, including its zero value. -/
theorem coefficients_eq_of_sq_eq {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 = σ ^ 2) :
    coefficients hv B f t ρ = coefficients hv B f t σ := by
  have he (a : ι → ℝ) : objective v B f t ρ a = objective v B f t σ a := by
    simp only [objective, hρσ]
  have hρ := coefficients_minimizes hv B f t ρ (coefficients hv B f t σ)
  have hσ := coefficients_minimizes hv B f t σ (coefficients hv B f t ρ)
  rw [he, he] at hρ
  exact (coefficients_optimal_iff hv B f t σ (coefficients hv B f t ρ)).mp
    (le_antisymm hρ hσ)

theorem coefficients_zero {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) :
    coefficients hv B f t 0 = inverseCoeff hv f := by
  have h := coefficients_minimizes hv B f t 0 (inverseCoeff hv f)
  simp only [objective, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h
  have he := le_antisymm h (residual_minimizes hv f (coefficients hv B f t 0))
  apply residual_minimizer_unique hv f (coefficients hv B f t 0)
  exact he.trans (residual_schur_value hv f)

theorem mismatch_antitone_of_sq_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 ≤ σ ^ 2) :
    mismatchEnergy B t (coefficients hv B f t σ) ≤
      mismatchEnergy B t (coefficients hv B f t ρ) := by
  rcases lt_or_eq_of_le hρσ with hlt | heq
  · exact mismatch_antitone_of_sq_lt hv B f t ρ σ hlt
  · rw [coefficients_eq_of_sq_eq hv B f t ρ σ heq]

theorem fit_error_monotone_of_sq_le {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (f : H) (t : κ → ℝ) (ρ σ : ℝ) (hρσ : ρ ^ 2 ≤ σ ^ 2) :
    ‖f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ)‖ ^ 2 ≤
      ‖f - Fintype.linearCombination ℝ v (coefficients hv B f t σ)‖ ^ 2 := by
  rcases lt_or_eq_of_le hρσ with hlt | heq
  · exact fit_error_monotone_of_sq_lt hv B f t ρ σ hlt
  · rw [coefficients_eq_of_sq_eq hv B f t ρ σ heq]

end RiemannResearch.Analysis.FiniteRegularizedConstraints

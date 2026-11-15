import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-coordinate detection and surjectivity

Source: Christian Noack's density-coupling discussion, 14 November 2026.
The proof uses the Banach open mapping theorem and a quantitative adjoint tail
bound. The existence of a finite detecting head is characterized, not assumed
to hold. The concrete consumer is QDensityCouplingSurjectivity.
-/

noncomputable section
namespace RiemannResearch.Analysis.FiniteHeadSurjectivity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-- A single finite head distinguishes zero from every nonzero vector. -/
def HeadUnique (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ) : Prop :=
  ∀ w : F, (∀ n : ℕ, n < N → coordinates w n = 0) → w = 0

def headMap (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ) :
    F →ₗ[ℝ] (Fin N → ℝ) where
  toFun w i := coordinates w i
  map_add' x y := by funext i; exact congrFun (coordinates.map_add x y) i
  map_smul' a x := by funext i; exact congrFun (coordinates.map_smul a x) i

theorem headMap_injective (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ)
    (h : HeadUnique coordinates N) : Function.Injective (headMap coordinates N) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply h
  intro n hn
  have he := congrFun hxy (⟨n, hn⟩ : Fin N)
  change coordinates x n = coordinates y n at he
  simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using he

theorem finiteDimensional_of_headUnique
    (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ) (h : HeadUnique coordinates N) :
    FiniteDimensional ℝ F :=
  FiniteDimensional.of_injective (headMap coordinates N) (headMap_injective coordinates N h)

/-- Surjectivity supplies a uniform estimate, not merely adjoint injectivity. -/
theorem adjoint_norm_bound_of_surjective (T : E →L[ℝ] F)
    (hT : Function.Surjective T) :
    ∃ K > 0, ∀ w : F, ‖w‖ ≤ K * ‖T.adjoint w‖ := by
  obtain ⟨K, hK, hlift⟩ := T.exists_preimage_norm_le hT
  refine ⟨K, hK, ?_⟩
  intro w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨v, hv, hnorm⟩ := hlift w
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hh : ‖w‖ * ‖w‖ ≤ ‖w‖ * (K * ‖T.adjoint w‖) := by
    calc
      ‖w‖ * ‖w‖ = inner ℝ (T v) w := by rw [hv, real_inner_self_eq_norm_sq]; ring
      _ = inner ℝ v (T.adjoint w) := (T.adjoint_inner_right v w).symm
      _ ≤ ‖v‖ * ‖T.adjoint w‖ := real_inner_le_norm _ _
      _ ≤ (K * ‖w‖) * ‖T.adjoint w‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖w‖ * (K * ‖T.adjoint w‖) := by ring
  exact le_of_mul_le_mul_left hh hpos

/-- An adjoint tail bound turns surjectivity into detection by one finite head. -/
theorem exists_headUnique_of_surjective
    (T : E →L[ℝ] F) (coordinates : F →ₗ[ℝ] (ℕ → ℝ))
    (a : ℝ)
    (htail : ∀ (N : ℕ) (w : F),
      (∀ n : ℕ, n < N → coordinates w n = 0) →
      ‖T.adjoint w‖ ≤ (a / ((N : ℝ) + 1)) * ‖w‖)
    (hT : Function.Surjective T) :
    ∃ N : ℕ, HeadUnique coordinates N := by
  obtain ⟨K, hK, hbound⟩ := adjoint_norm_bound_of_surjective T hT
  obtain ⟨N, hN⟩ := exists_nat_gt (K * a)
  have hf : K * (a / ((N : ℝ) + 1)) < 1 := by
    rw [← mul_div_assoc]
    apply (div_lt_one (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr
    linarith
  refine ⟨N, ?_⟩
  intro w hw
  by_contra hne
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have hle := (hbound w).trans
    (mul_le_mul_of_nonneg_left (htail N w hw) hK.le)
  have hlt := mul_lt_mul_of_pos_right hf hp
  nlinarith

/-- Dense range is exact range when the target is finite-dimensional. -/
theorem surjective_of_finiteDimensional (T : E →L[ℝ] F)
    (hdense : T.range.topologicalClosure = ⊤) [FiniteDimensional ℝ F] :
    Function.Surjective T := by
  exact LinearMap.range_eq_top.mp (T.range.topologicalClosure_eq_self ▸ hdense)

/-- Finite head uniqueness and dense range suffice for exact solvability. -/
theorem surjective_of_headUnique
    (T : E →L[ℝ] F)
    (hdense : T.range.topologicalClosure = ⊤)
    (coordinates : F →ₗ[ℝ] (ℕ → ℝ))
    (N : ℕ) (hN : HeadUnique coordinates N) :
    Function.Surjective T := by
  let _ := finiteDimensional_of_headUnique coordinates N hN
  exact surjective_of_finiteDimensional T hdense

/-- Exact equivalence; no finite-head provider is supplied by this theorem. -/
theorem surjective_iff_exists_headUnique
    (T : E →L[ℝ] F)
    (hdense : T.range.topologicalClosure = ⊤)
    (coordinates : F →ₗ[ℝ] (ℕ → ℝ))
    (a : ℝ)
    (htail : ∀ (N : ℕ) (w : F),
      (∀ n : ℕ, n < N → coordinates w n = 0) →
      ‖T.adjoint w‖ ≤ (a / ((N : ℝ) + 1)) * ‖w‖) :
    Function.Surjective T ↔ ∃ N : ℕ, HeadUnique coordinates N := by
  constructor
  · exact exists_headUnique_of_surjective T coordinates a htail
  · rintro ⟨N, hN⟩
    exact surjective_of_headUnique T hdense coordinates N hN

/-- A detecting head gives an explicit upper bound, not only finite dimension. -/
theorem finrank_le_of_headUnique
    (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ) (h : HeadUnique coordinates N) :
    Module.finrank ℝ F ≤ N := by
  let _ := finiteDimensional_of_headUnique coordinates N h
  have hli := (Module.finBasis ℝ F).linearIndependent.map'
    (headMap coordinates N) (LinearMap.ker_eq_bot.mpr (headMap_injective coordinates N h))
  simpa using hli.fintype_card_le_finrank

/-- A uniform lower bound beats the reciprocal tail beyond an explicit cutoff. -/
theorem headUnique_of_adjoint_lower_bound
    (T : E →L[ℝ] F) (coordinates : F →ₗ[ℝ] (ℕ → ℝ))
    (a δ : ℝ)
    (htail : ∀ (N : ℕ) (w : F),
      (∀ n : ℕ, n < N → coordinates w n = 0) →
      ‖T.adjoint w‖ ≤ (a / ((N : ℝ) + 1)) * ‖w‖)
    (hlower : ∀ w : F, δ * ‖w‖ ≤ ‖T.adjoint w‖)
    (N : ℕ) (hN : a / ((N : ℝ) + 1) < δ) :
    HeadUnique coordinates N := by
  intro w hw
  by_contra hne
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have hle := (hlower w).trans (htail N w hw)
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hN hp)) hle

/-- Failure of finite-head detection has a normalized witness. -/
theorem exists_unit_head_zero_of_not_headUnique
    (coordinates : F →ₗ[ℝ] (ℕ → ℝ)) (N : ℕ) (h : ¬ HeadUnique coordinates N) :
    ∃ w : F, ‖w‖ = 1 ∧ ∀ n : ℕ, n < N → coordinates w n = 0 := by
  obtain ⟨w, hw, hne⟩ :
      ∃ w : F, (∀ n : ℕ, n < N → coordinates w n = 0) ∧ w ≠ 0 := by
    by_contra hh
    apply h
    intro w hw
    by_contra hne
    exact hh ⟨w, hw, hne⟩
  have hp : 0 < ‖w‖ := norm_pos_iff.mpr hne
  refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  · intro n hn
    rw [map_smul]
    change ‖w‖⁻¹ * coordinates w n = 0
    rw [hw n hn, mul_zero]

#print axioms surjective_iff_exists_headUnique
#print axioms adjoint_norm_bound_of_surjective

end RiemannResearch.Analysis.FiniteHeadSurjectivity

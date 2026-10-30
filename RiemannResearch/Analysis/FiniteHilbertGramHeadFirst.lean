/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.OrthogonalObservationHeadFirst
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The full head-first inverse-Gram transition

Source: user-provided innovation-space research agenda, 29 October 2026.
An injective rank-one shear identifies the adjusted full basis. The exact
projection formula retains the gain with its favorable minus sign.
-/
namespace RiemannResearch.Analysis.OrthogonalObservationHeadFirst
noncomputable section
open scoped BigOperators
open RiemannResearch.Analysis.FiniteHilbertGram
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def headShear (k ell : H) (K : ℝ) : H →ₗ[ℝ] H where
  toFun x := x - (inner ℝ ell x / K) • k
  map_add' x y := by
    simp only [inner_add_right, add_div, add_smul]
    abel
  map_smul' a x := by
    simp only [inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]
    congr 1
    congr 1
    ring

theorem headShear_injective (k ell : H) (K : ℝ)
    (hellk : inner ℝ ell k = 0) : Function.Injective (headShear k ell K) := by
  intro x y hxy
  have he := congrArg (fun z => inner ℝ ell z) hxy
  change inner ℝ ell (x - (inner ℝ ell x / K) • k) =
    inner ℝ ell (y - (inner ℝ ell y / K) • k) at he
  simp only [inner_sub_right, inner_smul_right, hellk, mul_zero, sub_zero] at he
  change x - (inner ℝ ell x / K) • k = y - (inner ℝ ell y / K) • k at hxy
  simpa only [he, sub_left_inj] using hxy

variable [Fintype ι]

theorem headShear_independent (v : ι → H) (hv : LinearIndependent ℝ v)
    (k ell : H) (K : ℝ) (hellk : inner ℝ ell k = 0) :
    LinearIndependent ℝ (fun i => headShear k ell K (v i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have he : headShear k ell K (∑ j, c j • v j) = 0 := by
    simpa only [map_sum, map_smul] using hc
  have hz : (∑ j, c j • v j) = 0 :=
    headShear_injective k ell K hellk (by simpa only [map_zero] using he)
  exact Fintype.linearIndependent_iff.mp hv c hz i

theorem headShear_mem (v : ι → H) (k ell : H) (K : ℝ) (x : H)
    (hx : x ∈ synthesisSpan v) :
    headShear k ell K x ∈ synthesisSpan (fun j => headShear k ell K (v j)) := by
  change x ∈ Submodule.span ℝ (Set.range v) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

theorem headShear_gain (D k ell : H) (a b K cap : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hell : ‖ell‖ ^ 2 = cap - K)
    (hDell : inner ℝ D ell = b - a) :
    headShear k ell K (D - (b / cap) • ell) = headFirstGain D k ell a b K cap := by
  have he : -(inner ℝ ell (D - (b / cap) • ell) / K) = a / K - b / cap := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm D ell, hDell, hell]
    field_simp
    <;> ring
  change D - (b / cap) • ell - (inner ℝ ell (D - (b / cap) • ell) / K) • k = _
  rw [sub_eq_add_neg, ← neg_smul, he]
  rfl

theorem adjusted_source (v k F : H) (c a K : ℝ) (hK : K ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hvk : inner ℝ v k = 0) (hFk : inner ℝ k F = 0) :
    inner ℝ (adjustedColumn v k c K) (F + (a / K) • k) =
      inner ℝ v F - a * c / K := by
  simp only [adjustedColumn, inner_sub_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, hvk, hFk, hk]
  field_simp
  <;> ring

/-- The head-first gain is the actual projection onto the adjusted basis. -/
theorem headFirstGain_projection (v : ι → H) (D F k ell : H) (a b K cap : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hell : ‖ell‖ ^ 2 = cap - K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hDell : inner ℝ D ell = b - a)
    (hFk : inner ℝ k F = 0) (hvk : ∀ j, inner ℝ (v j) k = 0)
    (hD : D ∈ synthesisSpan v) (he : ell ∈ synthesisSpan v)
    (hDF : ∀ j, inner ℝ D (v j) = inner ℝ F (v j)) :
    (synthesisSpan (fun j => headShear k ell K (v j))).starProjection
      (F + (a / K) • k) = headFirstGain D k ell a b K cap := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [← headShear_gain D k ell a b K cap hK hcap hell hDell]
    exact headShear_mem v k ell K _ ((synthesisSpan v).sub_mem hD
      ((synthesisSpan v).smul_mem _ he))
  · intro w hw
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
    change Fintype.linearCombination ℝ (fun j => headShear k ell K (v j)) z = w at hz
    rw [← hz, real_inner_comm, inner_synthesis_left]
    apply Finset.sum_eq_zero
    intro j _
    have hp := gain_pairing D k ell (v j) a b K cap (inner ℝ ell (v j))
      hK hk hDk hellk (by simpa only [real_inner_comm] using hvk j) rfl
    have hs := adjusted_source (v j) k F (inner ℝ ell (v j)) a K hK hk (hvk j) hFk
    change z j * inner ℝ (adjustedColumn (v j) k (inner ℝ ell (v j)) K)
      (F + (a / K) • k - headFirstGain D k ell a b K cap) = 0
    have hc : inner ℝ (adjustedColumn (v j) k (inner ℝ ell (v j)) K)
        (headFirstGain D k ell a b K cap) =
        inner ℝ (v j) F - a * inner ℝ ell (v j) / K := by
      rw [real_inner_comm, hp, hDF j, real_inner_comm]
    rw [inner_sub_right, hs, hc, sub_self, mul_zero]

variable [DecidableEq ι]

/-- Literal inverse-Gram head-first transition. All hypotheses concern
the actual old normal, innovation, displacement, and their exact sources. -/
theorem headFirst_inverseGram (v : ι → H) (hv : LinearIndependent ℝ v)
    (D F k ell : H) (a b K cap : ℝ)
    (hK : K ≠ 0) (hcap : cap ≠ 0)
    (hk : ‖k‖ ^ 2 = K) (hell : ‖ell‖ ^ 2 = cap - K)
    (hDk : inner ℝ D k = 0) (hellk : inner ℝ ell k = 0)
    (hDell : inner ℝ D ell = b - a)
    (hFk : inner ℝ k F = 0) (hvk : ∀ j, inner ℝ (v j) k = 0)
    (hD : D ∈ synthesisSpan v) (he : ell ∈ synthesisSpan v)
    (hDF : ∀ j, inner ℝ D (v j) = inner ℝ F (v j)) :
    let c := fun j => inner ℝ ell (v j)
    let r := fun j => inner ℝ (v j) F - a * c j / K
    let B' : Matrix ι ι ℝ := fun j l => inner ℝ (v j) (v l) + c j * c l / K
    b ^ 2 / cap - ‖D‖ ^ 2 = a ^ 2 / K - dotProduct r (B'⁻¹.mulVec r) := by
  dsimp only
  let v' := fun j => headShear k ell K (v j)
  let Y := F + (a / K) • k
  have hi : LinearIndependent ℝ v' := headShear_independent v hv k ell K hellk
  have hp := projection_inner_eq_inverseGram hi Y Y
  rw [headFirstGain_projection v D F k ell a b K cap hK hcap hk hell
    hDk hellk hDell hFk hvk hD he hDF, real_inner_self_eq_norm_sq,
    gain_norm D k ell a b K cap hK hcap hk hell hDk hellk hDell] at hp
  have hcross : cross v' Y = fun j => inner ℝ (v j) F - a * inner ℝ ell (v j) / K := by
    funext j
    exact adjusted_source (v j) k F (inner ℝ ell (v j)) a K hK hk (hvk j) hFk
  have hgram : gramMatrix v' =
      (fun j l => inner ℝ (v j) (v l) + inner ℝ ell (v j) * inner ℝ ell (v l) / K) := by
    funext j l
    exact adjusted_inner (v j) (v l) k (inner ℝ ell (v j)) (inner ℝ ell (v l)) K
      hK hk (hvk j) (by simpa only [real_inner_comm] using hvk l)
  rw [hcross, hgram] at hp
  linarith

end
end RiemannResearch.Analysis.OrthogonalObservationHeadFirst

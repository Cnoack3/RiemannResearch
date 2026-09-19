import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact additive capacity after screening a finite block

Source: user-provided argument,
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Section 14. The old Gram inverse is the actual Hilbert Gram inverse;
the new block is residualized against the full old span. The inverse-Gram
gain retains every mixed entry. No assertion of cumulative divergence
is contained in this module.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
noncomputable section

open FiniteHilbertGram FiniteHilbertConstraints

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The genuine new direction after orthogonal screening against the old span. -/
def screened {u : ι → H} (hu : LinearIndependent ℝ u) (w : κ → H) (j : κ) : H :=
  w j - Fintype.linearCombination ℝ u (inverseCoeff hu (w j))

/-- The prescribed source after the same screening of the old representer. -/
def screenedSource {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (b : ι → ℝ) (d : κ → ℝ) (j : κ) : ℝ :=
  d j - inner ℝ (w j) (minimumVector hu b)

omit [Fintype κ] in
theorem inner_old_screened {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (i : ι) (j : κ) : inner ℝ (u i) (screened hu w j) = 0 := by
  unfold screened
  rw [inner_sub_right, inverseCoeff_normal]
  simp only [cross, sub_self]

omit [Fintype κ] in
/-- This is the entrywise identity `Σ = T_A - Bᵀ T_O⁻¹ B`. -/
theorem screened_gram_entry {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (i j : κ) :
    inner ℝ (screened hu w i) (screened hu w j) =
      inner ℝ (w i) (w j) - ∑ k, inverseCoeff hu (w i) k * cross u (w j) k := by
  exact residual_bilinear_schur hu (w i) (w j)

omit [Fintype κ] in
/-- This is the full screened source `s = v_A - Bᵀ T_O⁻¹ v_O`. -/
theorem screenedSource_eq {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (b : ι → ℝ) (d : κ → ℝ) (j : κ) :
    screenedSource hu w b d j =
      d j - ∑ i, inverseSource hu b i * cross u (w j) i := by
  unfold screenedSource
  rw [real_inner_comm]
  change d j - inner ℝ
    (Fintype.linearCombination ℝ u (inverseSource hu b)) (w j) = _
  rw [inner_synthesis_left]
  rfl

private theorem synthesis_sum (u : ι → H) (w : κ → H)
    (a : ι → ℝ) (c : κ → ℝ) :
    Fintype.linearCombination ℝ (Sum.elim u w) (Sum.elim a c) =
      Fintype.linearCombination ℝ u a + Fintype.linearCombination ℝ w c := by
  simp only [Fintype.linearCombination_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]

private theorem synthesis_screened {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (c : κ → ℝ) :
    Fintype.linearCombination ℝ (screened hu w) c =
      Fintype.linearCombination ℝ w c -
        Fintype.linearCombination ℝ u (∑ j, c j • inverseCoeff hu (w j)) := by
  change (∑ j, c j • (w j - Fintype.linearCombination ℝ u (inverseCoeff hu (w j)))) = _
  rw [map_sum]
  simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
  rfl

/-- Screening preserves independence when the combined old/new family is independent.
Thus invertibility of the Schur Gram matrix is a theorem, not a new assumption. -/
theorem screened_linearIndependent {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hall : LinearIndependent ℝ (Sum.elim u w)) :
    LinearIndependent ℝ (screened hu w) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hsc : Fintype.linearCombination ℝ (screened hu w) c = 0 := hc
  have hsyn : Fintype.linearCombination ℝ (Sum.elim u w)
      (Sum.elim (-(∑ k, c k • inverseCoeff hu (w k))) c) = 0 := by
    rw [synthesis_sum, map_neg]
    have hs := synthesis_screened hu w c
    rw [hsc] at hs
    simpa only [sub_eq_add_neg, add_comm] using hs.symm
  have hz : Sum.elim (-(∑ k, c k • inverseCoeff hu (w k))) c = 0 := by
    apply hall.fintypeLinearCombination_injective
    simpa only [map_zero] using hsyn
  exact congrFun hz (Sum.inr j)

/-- The genuine screened quadratic form is strictly positive off zero. -/
theorem screened_gram_positive {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hall : LinearIndependent ℝ (Sum.elim u w))
    (c : κ → ℝ) (hc : c ≠ 0) :
    0 < ∑ i, c i * gram (screened hu w) c i := by
  rw [← gram_quadratic]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hc
  apply (screened_linearIndependent hu w hall).fintypeLinearCombination_injective
  simpa only [map_zero] using hz

theorem inner_old_screened_minimumVector {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hs : LinearIndependent ℝ (screened hu w))
    (s : κ → ℝ) (i : ι) : inner ℝ (u i) (minimumVector hs s) = 0 := by
  unfold minimumVector
  rw [Fintype.linearCombination_apply, inner_sum]
  simp only [inner_smul_right, inner_old_screened, mul_zero, Finset.sum_const_zero]

/-- The enlarged representer splits into old and screened orthogonal components. -/
theorem minimumVector_screened_sum {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hs : LinearIndependent ℝ (screened hu w))
    (hall : LinearIndependent ℝ (Sum.elim u w)) (b : ι → ℝ) (d : κ → ℝ) :
    minimumVector hall (Sum.elim b d) =
      minimumVector hu b + minimumVector hs (screenedSource hu w b d) := by
  let s := screenedSource hu w b d
  let y := inverseSource hs s
  let a := inverseSource hu b - ∑ j, y j • inverseCoeff hu (w j)
  let c := Sum.elim a y
  have hsyn : Fintype.linearCombination ℝ (Sum.elim u w) c =
      minimumVector hu b + minimumVector hs s := by
    change Fintype.linearCombination ℝ (Sum.elim u w) (Sum.elim a y) = _
    rw [synthesis_sum]
    have hz : minimumVector hs s = Fintype.linearCombination ℝ (screened hu w) y := rfl
    rw [hz, synthesis_screened]
    change Fintype.linearCombination ℝ u
      (inverseSource hu b - ∑ j, y j • inverseCoeff hu (w j)) +
      Fintype.linearCombination ℝ w y = _
    rw [map_sub]
    change Fintype.linearCombination ℝ u (inverseSource hu b) -
      Fintype.linearCombination ℝ u (∑ j, y j • inverseCoeff hu (w j)) +
      Fintype.linearCombination ℝ w y =
      Fintype.linearCombination ℝ u (inverseSource hu b) +
        (Fintype.linearCombination ℝ w y -
          Fintype.linearCombination ℝ u (∑ j, y j • inverseCoeff hu (w j)))
    abel
  have hnew (j : κ) : inner ℝ (w j) (minimumVector hs s) = s j := by
    have h := minimumVector_observation hs s j
    change inner ℝ (w j - Fintype.linearCombination ℝ u (inverseCoeff hu (w j)))
      (minimumVector hs s) = s j at h
    rw [inner_sub_left, inner_synthesis_left] at h
    simp only [inner_old_screened_minimumVector, mul_zero, Finset.sum_const_zero,
      sub_zero] at h
    exact h
  have hn (k : ι ⊕ κ) : gram (Sum.elim u w) c k = Sum.elim b d k := by
    change inner ℝ (Sum.elim u w k)
      (Fintype.linearCombination ℝ (Sum.elim u w) c) = _
    rw [hsyn, inner_add_right]
    cases k with
    | inl i =>
      simp only [Sum.elim_inl, minimumVector_observation,
        inner_old_screened_minimumVector, add_zero]
    | inr j =>
      simp only [Sum.elim_inr, hnew]
      dsimp [s, screenedSource]
      ring
  have hc : c = inverseSource hall (Sum.elim b d) := by
    apply gram_injective hall
    funext k
    rw [hn, inverseSource_normal]
  change Fintype.linearCombination ℝ (Sum.elim u w)
    (inverseSource hall (Sum.elim b d)) = _
  rw [← hc, hsyn]

/-- The exact additive inverse-Gram formula. The new capacity is formed
from the actual Schur Gram matrix and actual screened source. -/
theorem capacity_screened_add {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hs : LinearIndependent ℝ (screened hu w))
    (hall : LinearIndependent ℝ (Sum.elim u w)) (b : ι → ℝ) (d : κ → ℝ) :
    capacity hall (Sum.elim b d) =
      capacity hu b + capacity hs (screenedSource hu w b d) := by
  have ho : inner ℝ (minimumVector hu b)
      (minimumVector hs (screenedSource hu w b d)) = 0 := by
    unfold minimumVector
    rw [inner_synthesis_left]
    change (∑ i, (gramEquiv hu).symm b i *
      inner ℝ (u i) (minimumVector hs (screenedSource hu w b d))) = 0
    simp only [inner_old_screened_minimumVector, mul_zero, Finset.sum_const_zero]
  rw [capacity_eq_norm_sq, minimumVector_screened_sum hu w hs hall b d,
    norm_add_sq_real, ho, ← capacity_eq_norm_sq, ← capacity_eq_norm_sq]
  ring

theorem capacity_le_enlarged {u : ι → H} (hu : LinearIndependent ℝ u)
    (w : κ → H) (hs : LinearIndependent ℝ (screened hu w))
    (hall : LinearIndependent ℝ (Sum.elim u w)) (b : ι → ℝ) (d : κ → ℝ) :
    capacity hu b ≤ capacity hall (Sum.elim b d) := by
  rw [capacity_screened_add hu w hs hall b d]
  exact le_add_of_nonneg_right (capacity_nonneg hs _)

/-- Exact change of full-Gram capacity from an additive tail gain. -/
theorem saturated_capacity_gain (τ Γ : ℝ) (hτ : 0 ≤ τ) (hΓ : 0 ≤ Γ) :
    2 * (τ + Γ) / (τ + Γ + 2) - 2 * τ / (τ + 2) =
      4 * Γ / ((τ + 2) * (τ + Γ + 2)) := by
  have h₀ : τ + 2 ≠ 0 := by linarith
  have h₁ : τ + Γ + 2 ≠ 0 := by linarith
  field_simp [h₀, h₁]
  ring

/-- Exact decrease of the head-normalized tail minimum. -/
theorem inverse_capacity_drop (τ Γ : ℝ) (hτ : 0 < τ) (hΓ : 0 ≤ Γ) :
    1 / τ - 1 / (τ + Γ) = Γ / (τ * (τ + Γ)) := by
  have h₁ : τ + Γ ≠ 0 := by linarith
  field_simp [ne_of_gt hτ, h₁]
  ring

/-- Once actual block gains have been supplied, their finite sum is exact. -/
theorem capacity_telescope (τ Γ : ℕ → ℝ)
    (hstep : ∀ j, τ (j + 1) = τ j + Γ j) (J : ℕ) :
    τ J = τ 0 + ∑ j ∈ Finset.range J, Γ j := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [hstep, ih, Finset.sum_range_succ]
    ring

end
end RiemannResearch.Analysis.FiniteGramCapacity

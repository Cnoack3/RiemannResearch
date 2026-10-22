import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.ParetoResidueGramStrict
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Strict positivity of the complete integrated Ramanujan Gram form

Source: user-provided September 11, 2026 conversation, linear independence
and inverse Gram discussion. All inner products use the full Pareto law.
Finite positive definiteness does not assert a uniform inverse bound.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every mixed covariance is retained in the actual full Gram quadratic form. -/
def ramanujanGramQuadratic (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    c i * c j * paretoInner (ramanujanPacket i) (ramanujanPacket j)

theorem ramanujanGramQuadratic_eq_inner (s : Finset ℕ) (c : ℕ → ℝ) :
    ramanujanGramQuadratic s c =
      paretoInner (fun k => ∑ i ∈ s, c i * ramanujanPacket i k)
        (fun k => ∑ i ∈ s, c i * ramanujanPacket i k) := by
  symm
  exact paretoInner_finsetCombination s c ramanujanPacket_abs_le

/-- Algebraic independence implies strict positivity of each finite actual
Pareto Gram form. This includes the infinite tails and all signed mixed terms. -/
theorem ramanujanGramQuadratic_pos (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q) (hc : ∃ q ∈ s, c q ≠ 0) :
    0 < ramanujanGramQuadratic s c := by
  rw [ramanujanGramQuadratic_eq_inner]
  let f : ℕ → ℝ := fun k => ∑ q ∈ s, c q * ramanujanPacket q k
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  have hnonneg := paretoInner_self_nonneg f
  by_contra hpos
  have hzero : paretoInner f f = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hvalues := (paretoInner_self_zero_iff_positive hC).mp hzero
  have hall : ∀ k, ∑ q ∈ s, c q * ramanujanPacket q k = 0 := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [ramanujanPacket, residue]
    · exact hvalues k (Nat.pos_of_ne_zero hk)
  obtain ⟨q, hqs, hcq⟩ := hc
  exact hcq (ramanujanPacket_finite_independent s c hs hall q hqs)

theorem ramanujanGramQuadratic_eq_zero_iff (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q) :
    ramanujanGramQuadratic s c = 0 ↔ ∀ q ∈ s, c q = 0 := by
  classical
  constructor
  · intro hz
    by_contra h
    push_neg at h
    have hp := ramanujanGramQuadratic_pos s c hs h
    linarith
  · intro hc
    unfold ramanujanGramQuadratic
    apply Finset.sum_eq_zero
    intro i hi
    simp [hc i hi]

/-- The actual finite Pareto Gram matrix acting on its conductor coordinates. -/
def ramanujanGramAction (s : Finset ℕ) : (s → ℝ) →ₗ[ℝ] (s → ℝ) where
  toFun v i := ∑ j : s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * v j
  map_add' v w := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    ext i
    simp [Finset.mul_sum, mul_left_comm]

/-- A vector in the actual Gram kernel is zero; positive definiteness is
proved above from the genuine packet independence and full Pareto atoms. -/
theorem ramanujanGramAction_eq_zero (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (v : s → ℝ)
    (hv : ramanujanGramAction s v = 0) : v = 0 := by
  classical
  let c : ℕ → ℝ := fun q => if hq : q ∈ s then v ⟨q, hq⟩ else 0
  have hrow (i : s) :
      (∑ j ∈ s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * c j) = 0 := by
    have he :
        (∑ j : s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * v j) =
          ∑ j ∈ s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * c j := by
      apply Finset.sum_bij (fun j _ => j.val)
      · intro j _
        exact j.property
      · intro j _ k _ hjk
        exact Subtype.ext hjk
      · intro j hj
        exact ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
      · intro j _
        simp [c, j.property]
    have hval := congrFun hv i
    change (∑ j : s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * v j) = 0
      at hval
    exact he.symm.trans hval
  have hquad : ramanujanGramQuadratic s c = 0 := by
    unfold ramanujanGramQuadratic
    apply Finset.sum_eq_zero
    intro i hi
    calc
      (∑ j ∈ s, c i * c j * paretoInner (ramanujanPacket i) (ramanujanPacket j)) =
          c i * ∑ j ∈ s, paretoInner (ramanujanPacket i) (ramanujanPacket j) * c j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hrow ⟨i, hi⟩, mul_zero]
  have hc := (ramanujanGramQuadratic_eq_zero_iff s c hs).mp hquad
  ext i
  simpa [c, i.property] using hc i i.property

theorem ramanujanGramAction_injective (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) : Function.Injective (ramanujanGramAction s) := by
  intro v w hvw
  have hz : ramanujanGramAction s (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  exact sub_eq_zero.mp (ramanujanGramAction_eq_zero s hs (v - w) hz)

/-- The inverse exists at every finite conductor set, without assuming an
inverse, a matrix nondegeneracy hypothesis, or any uniform condition number. -/
def ramanujanGramEquiv (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) :
    (s → ℝ) ≃ₗ[ℝ] (s → ℝ) :=
  LinearEquiv.ofBijective (ramanujanGramAction s)
    ⟨ramanujanGramAction_injective s hs,
      (LinearMap.injective_iff_surjective).mp (ramanujanGramAction_injective s hs)⟩

/-- Actual coefficients solving any prescribed finite normal equations. -/
def ramanujanGramSolve (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q) (y : s → ℝ) : s → ℝ :=
  (ramanujanGramEquiv s hs).symm y

theorem ramanujanGramSolve_normal_equations (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (y : s → ℝ) :
    ramanujanGramAction s (ramanujanGramSolve s hs y) = y := by
  exact (ramanujanGramEquiv s hs).apply_symm_apply y

end
end RiemannResearch.RH.Pareto

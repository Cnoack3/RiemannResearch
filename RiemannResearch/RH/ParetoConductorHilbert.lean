import RiemannResearch.RH.ParetoConductorFibers
import RiemannResearch.LinearAlgebra.WeightedQuotientHilbert

/-!
# Concrete finite Hilbert realization of the full Pareto conductor step

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §§2--3.
Coordinates are the positive representatives 1,...,N*b, with actual
periodized Pareto masses. Inner products agree with the complete infinite
Pareto inner products for bounded periodic inputs.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.LinearAlgebra.WeightedFiniteQuotient
open RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
noncomputable section

def conductorQuotient (N b : ℕ) (hN : 0 < N) (i : Fin (N*b)) : Fin N :=
  ⟨i.val % N, Nat.mod_lt _ hN⟩

def conductorFineWeight (N b : ℕ) (i : Fin (N*b)) : ℝ :=
  progressionWeight (N*b) (i.val+1)

def conductorSample (N b : ℕ) (f : ℕ → ℝ) (i : Fin (N*b)) : ℝ := f (i.val+1)

def conductorQuotientMean (N b : ℕ) (hN : 0 < N) (f : ℕ → ℝ) : Fin N → ℝ :=
  average (conductorQuotient N b hN) (conductorFineWeight N b) (conductorSample N b f)

/-- A concrete packet/function vector in the finite weighted Hilbert model. -/
def conductorHilbert (N b : ℕ) (f : ℕ → ℝ) : EuclideanSpace ℝ (Fin (N*b)) :=
  coordinates (conductorFineWeight N b) (conductorSample N b f)

theorem conductorFineWeight_pos (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (i : Fin (N*b)) : 0 < conductorFineWeight N b i :=
  progressionWeight_pos (N*b) (i.val+1) (Nat.mul_pos hN hb) (by omega)

theorem conductorQuotient_surjective (N b : ℕ) (hN : 0 < N) (hb : 0 < b) :
    Function.Surjective (conductorQuotient N b hN) := by
  intro r
  have hNb : N ≤ N*b := Nat.le_mul_of_pos_right N hb
  refine ⟨⟨r.val, lt_of_lt_of_le r.isLt hNb⟩, ?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt r.isLt

theorem conductor_pushforward_pos (N b : ℕ) (hN : 0 < N) (hb : 0 < b) (r : Fin N) :
    0 < pushforward (conductorQuotient N b hN) (conductorFineWeight N b) r := by
  obtain ⟨i,hi⟩ := conductorQuotient_surjective N b hN hb r
  unfold pushforward
  apply Finset.sum_pos'
  · intro j _
    split_ifs
    · exact (conductorFineWeight_pos N b hN hb j).le
    · exact le_rfl
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [if_pos hi]
    exact conductorFineWeight_pos N b hN hb i

/-- Every full Pareto Gram entry equals the finite Euclidean Gram entry exactly. -/
theorem conductorHilbert_inner (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (f g : ℕ → ℝ) {C D : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hg : ∀ k, |g k| ≤ D)
    (hpf : ∀ k, f (k+N*b) = f k) (hpg : ∀ k, g (k+N*b) = g k) :
    inner ℝ (conductorHilbert N b f) (conductorHilbert N b g) = paretoInner f g := by
  rw [conductorHilbert, conductorHilbert,
    coordinates_inner _ _ _ (fun i => (conductorFineWeight_pos N b hN hb i).le),
    periodic_paretoInner_mixed (N*b) (Nat.mul_pos hN hb) f g hf hg hpf hpg]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [conductorFineWeight, conductorSample]
  ring

/-- The actual finite arithmetic average has no unresolved orthogonality provider. -/
theorem conductorHilbert_conditional_orthogonal (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (f : ℕ → ℝ) (v : EuclideanSpace ℝ (Fin (N*b)))
    (hv : v ∈ coarseSpace (conductorQuotient N b hN) (conductorFineWeight N b)) :
    inner ℝ (conductorHilbert N b f - coordinates (conductorFineWeight N b)
      ((conductorQuotientMean N b hN f) ∘ conductorQuotient N b hN)) v = 0 := by
  exact conditional_residual_orthogonal _ _ _
    (fun i => (conductorFineWeight_pos N b hN hb i).le)
    (fun r => ne_of_gt (conductor_pushforward_pos N b hN hb r)) v hv

/-- Full-weight conductor averaging equals the genuine finite Hilbert projection. -/
theorem conductorHilbert_mean_eq_projection (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (f : ℕ → ℝ) :
    coordinates (conductorFineWeight N b)
      ((conductorQuotientMean N b hN f) ∘ conductorQuotient N b hN) =
      (coarseSpace (conductorQuotient N b hN) (conductorFineWeight N b)).starProjection
        (conductorHilbert N b f) := by
  exact conditional_vector_eq_projection _ _ _
    (fun i => (conductorFineWeight_pos N b hN hb i).le)
    (fun r => ne_of_gt (conductor_pushforward_pos N b hN hb r))

end
end RiemannResearch.RH.Pareto

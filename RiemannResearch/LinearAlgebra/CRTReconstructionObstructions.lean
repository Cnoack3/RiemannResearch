import Mathlib.Data.Setoid.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Obstructions to unrestricted CRT and bounded-energy reconstruction

Source: the user-provided categorical CRT research note of 2026-11-14.
These counterexamples identify which hypotheses are needed by the finite
gluing and analytic reconstruction theorems used in the Pareto RH program.
-/

namespace CRTReconstruction

def leftPartition : Setoid (Fin 3) := Setoid.ker (fun n : Fin 3 => n == 2)
def rightPartition : Setoid (Fin 3) := Setoid.ker (fun n : Fin 3 => n == 0)

theorem join_compatible_not_pair_solvable :
    (leftPartition ⊔ rightPartition) 2 0 ∧
      ¬ ∃ z : Fin 3, leftPartition z 2 ∧ rightPartition z 0 := by
  constructor
  · apply (leftPartition ⊔ rightPartition).iseqv.trans (y := 1)
    · exact (show rightPartition ≤ leftPartition ⊔ rightPartition from le_sup_right)
        (by change ((2 : Fin 3) == 0) = ((1 : Fin 3) == 0); decide)
    · exact (show leftPartition ≤ leftPartition ⊔ rightPartition from le_sup_left)
        (by change ((1 : Fin 3) == 2) = ((0 : Fin 3) == 2); decide)
  · rintro ⟨z, hz, hz'⟩
    change (z == 2) = true at hz
    change (z == 0) = true at hz'
    have hz2 : z = 2 := by simpa using hz
    have hz0 : z = 0 := by simpa using hz'
    exact (by decide : (2 : Fin 3) ≠ 0) (hz2.symm.trans hz0)

/-- Three linear quotient maps have all binary images full, but their triple
image is proper. Thus permuting kernels alone do not suffice. -/
theorem three_linear_constraints_obstruction :
    Function.Surjective (fun p : ℝ × ℝ => (p.1, p.2)) ∧
    Function.Surjective (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) ∧
    Function.Surjective (fun p : ℝ × ℝ => (p.2, p.1 + p.2)) ∧
    ¬ ∃ p : ℝ × ℝ, p.1 = 0 ∧ p.2 = 0 ∧ p.1 + p.2 = 1 := by
  refine ⟨fun p => ⟨p, rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩
    exact ⟨(a, b - a), Prod.ext rfl (by dsimp; ring)⟩
  · rintro ⟨a, b⟩
    exact ⟨(b - a, a), Prod.ext rfl (by dsimp; ring)⟩
  · rintro ⟨p, h₁, h₂, h₃⟩
    rw [h₁, h₂] at h₃
    norm_num at h₃

def firstKernel : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)
def secondKernel : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.snd ℝ ℝ ℝ)
def sumKernel : Submodule ℝ (ℝ × ℝ) :=
  LinearMap.ker (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ)

theorem kernel_meet_eq_bot : firstKernel ⊓ secondKernel = ⊥ := by
  ext p
  simp only [Submodule.mem_inf, firstKernel, secondKernel, LinearMap.mem_ker,
    LinearMap.fst_apply, LinearMap.snd_apply, Submodule.mem_bot]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h => by subst p; exact ⟨rfl, rfl⟩⟩

theorem kernel_binary_sums_top : firstKernel ⊔ sumKernel = ⊤ ∧
    secondKernel ⊔ sumKernel = ⊤ := by
  constructor
  · apply top_unique
    intro p _
    apply Submodule.mem_sup.mpr
    refine ⟨(0, p.2 + p.1), ?_, (p.1, -p.1), ?_, ?_⟩
    · simp [firstKernel, LinearMap.mem_ker]
    · simp [sumKernel, LinearMap.mem_ker]
    · apply Prod.ext <;> dsimp <;> ring
  · apply top_unique
    intro p _
    apply Submodule.mem_sup.mpr
    refine ⟨(p.1 + p.2, 0), ?_, (-p.2, p.2), ?_, ?_⟩
    · simp [secondKernel, LinearMap.mem_ker]
    · simp [sumKernel, LinearMap.mem_ker]
    · apply Prod.ext <;> dsimp <;> ring

/-- The precise distributivity failure behind the three-constraint obstruction. -/
theorem kernel_distributivity_failure :
    (firstKernel ⊓ secondKernel) ⊔ sumKernel ≠
      (firstKernel ⊔ sumKernel) ⊓ (secondKernel ⊔ sumKernel) := by
  rw [kernel_meet_eq_bot, bot_sup_eq, kernel_binary_sums_top.1,
    kernel_binary_sums_top.2, inf_top_eq]
  intro h
  have hp : ((1, 0) : ℝ × ℝ) ∈ sumKernel := by rw [h]; trivial
  norm_num [sumKernel, LinearMap.mem_ker] at hp

noncomputable def nearSingularEquiv (ε : ℝ) (hε : ε ≠ 0) :
    (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1, p.1 + ε * p.2)
  invFun p := (p.1, (p.2 - p.1) / ε)
  left_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hε]
      ring
  right_inv p := by
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [hε]
      ring
  map_add' p q := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  map_smul' c p := by
    apply Prod.ext
    · rfl
    · dsimp
      ring

theorem nearSingular_target_inverse (ε : ℝ) (hε : ε ≠ 0) :
    (nearSingularEquiv ε hε).symm (0, 1) = (0, ε⁻¹) := by
  simp [nearSingularEquiv]

def euclideanEnergy (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

theorem nearSingular_target_energy (ε : ℝ) (hε : ε ≠ 0) :
    euclideanEnergy ((nearSingularEquiv ε hε).symm (0, 1)) = (ε⁻¹) ^ 2 := by
  rw [nearSingular_target_inverse]
  simp [euclideanEnergy]

theorem isomorphism_reconstruction_cost_unbounded (C : ℝ) (hC : 0 ≤ C) :
    ∃ (ε : ℝ) (hε : ε ≠ 0),
      C < euclideanEnergy ((nearSingularEquiv ε hε).symm (0, 1)) := by
  have h : C + 1 ≠ 0 := by linarith
  refine ⟨(C + 1)⁻¹, inv_ne_zero h, ?_⟩
  rw [nearSingular_target_energy, inv_inv]
  nlinarith [sq_nonneg C]

/-- Every finite collection of unit target coordinates has a square-summable
realization with exact squared energy equal to the number of constraints. -/
theorem finite_unit_data_energy (F : Finset ℕ) :
    ∃ v : ℕ → ℝ, Summable (fun n => v n ^ 2) ∧
      (∀ n ∈ F, v n = 1) ∧ (∑' n, v n ^ 2) = (F.card : ℝ) := by
  classical
  refine ⟨fun n => if n ∈ F then 1 else 0, ?_, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := F)
    intro n hn
    simp [hn]
  · intro n hn
    simp [hn]
  · rw [tsum_eq_sum (s := F)]
    · simp
    · intro n hn
      simp [hn]

theorem infinite_unit_data_not_square_summable :
    ¬ ∃ v : ℕ → ℝ, Summable (fun n => v n ^ 2) ∧ ∀ n, v n = 1 := by
  rintro ⟨v, hv, heq⟩
  simp_rw [heq, one_pow] at hv
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hv.tendsto_atTop_zero
  exact one_ne_zero h10

theorem finite_unit_data_minimal_energy (F : Finset ℕ) (v : ℕ → ℝ)
    (hv : Summable (fun n => v n ^ 2)) (hcoords : ∀ n ∈ F, v n = 1) :
    (F.card : ℝ) ≤ ∑' n, v n ^ 2 := by
  calc
    (F.card : ℝ) = ∑ n ∈ F, v n ^ 2 := by
      symm
      calc
        ∑ n ∈ F, v n ^ 2 = ∑ n ∈ F, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hcoords n hn, one_pow]
        _ = (F.card : ℝ) := by simp
    _ ≤ ∑' n, v n ^ 2 := Summable.sum_le_tsum F (fun n _ => sq_nonneg (v n)) hv

end CRTReconstruction

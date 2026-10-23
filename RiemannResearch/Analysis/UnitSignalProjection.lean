import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unit-signal projection normalization

Source: `Final_Limit_Unit_Signal_Residues_2026-10-11 (1).md`,
Proposition 2.1 and the minimum-distance argument in Section 3.

This module gives the abstract inner-product-space calculation, with a concrete
constructor using Mathlib's `Submodule.starProjection`. The actual inverse-square
residue-space application is in `RH/ZetaTwoUnitSignal.lean`.
Completeness is unnecessary for the algebraic portion once a projection vector
has been supplied. No hypothesis here asserts vanishing of the limiting defect.
-/

noncomputable section

open scoped Topology

namespace RiemannResearch.Analysis.UnitSignalProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Data satisfied by a nonzero orthogonal projection of the signal target.
For the attached note, `mass = 1/4`, `target = Y`, `complement = O`, and
`projection = Π_M Y` (or `Π Y`). -/
structure ProjectionSignalModel (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  space : Submodule ℝ E
  target : E
  complement : E
  projection : E
  mass : ℝ
  target_energy : inner ℝ target target = mass
  projection_mem : projection ∈ space
  complement_mem : complement ∈ space
  targets_orthogonal : inner ℝ target complement = 0
  projection_pairing : ∀ f ∈ space,
    inner ℝ f projection = inner ℝ f target
  projection_energy_pos : 0 < inner ℝ projection projection

namespace ProjectionSignalModel

variable (M : ProjectionSignalModel E)

/-- Concrete constructor from Mathlib's orthogonal projection. The nonzero
projection hypothesis supplies the strict positivity needed to normalize it.
No minimum-distance or projection-pairing identity is assumed here. -/
def ofStarProjection (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (y o : E) (ho : o ∈ S) (hyo : ⟪y, o⟫ = 0)
    (hs : S.starProjection y ≠ 0) : ProjectionSignalModel E where
  space := S
  target := y
  complement := o
  projection := S.starProjection y
  mass := ⟪y, y⟫
  target_energy := rfl
  projection_mem := S.starProjection_apply_mem y
  complement_mem := ho
  targets_orthogonal := hyo
  projection_pairing := by
    intro f hf
    have hz : ⟪f, y - S.starProjection y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hf
        (Submodule.sub_starProjection_mem_orthogonal (K := S) y)
    rw [inner_sub_right] at hz
    linarith
  projection_energy_pos := real_inner_self_pos.mpr hs

def energy : ℝ := ⟪M.projection, M.projection⟫

def defect : ℝ := ‖M.target - M.projection‖ ^ 2

def optimizer : E := (M.mass / M.energy) • M.projection

/-- The two scalar moment constraints replacing conditional expectation. -/
def Admissible (f : E) : Prop :=
  f ∈ M.space ∧ ⟪f, M.target⟫ = M.mass ∧ ⟪f, M.complement⟫ = 0

theorem energy_pos : 0 < M.energy := M.projection_energy_pos

theorem energy_ne_zero : M.energy ≠ 0 := ne_of_gt M.energy_pos

theorem projection_inner_target :
    ⟪M.projection, M.target⟫ = M.energy :=
  (M.projection_pairing M.projection M.projection_mem).symm

theorem projection_inner_complement :
    ⟪M.projection, M.complement⟫ = 0 := by
  calc
    ⟪M.projection, M.complement⟫ = ⟪M.complement, M.projection⟫ :=
      real_inner_comm _ _
    _ = ⟪M.complement, M.target⟫ :=
      M.projection_pairing M.complement M.complement_mem
    _ = ⟪M.target, M.complement⟫ := real_inner_comm _ _
    _ = 0 := M.targets_orthogonal

theorem optimizer_inner_target : ⟪M.optimizer, M.target⟫ = M.mass := by
  rw [optimizer, real_inner_smul_left, M.projection_inner_target]
  field_simp [M.energy_ne_zero]

theorem optimizer_inner_complement : ⟪M.optimizer, M.complement⟫ = 0 := by
  rw [optimizer, real_inner_smul_left, M.projection_inner_complement, mul_zero]

theorem optimizer_admissible : M.Admissible M.optimizer := by
  refine ⟨?_, M.optimizer_inner_target, M.optimizer_inner_complement⟩
  exact M.space.smul_mem (M.mass / M.energy) M.projection_mem

theorem optimizer_energy : ⟪M.optimizer, M.optimizer⟫ = M.mass ^ 2 / M.energy := by
  simp only [optimizer, real_inner_smul_left, real_inner_smul_right]
  change (M.mass / M.energy) * ((M.mass / M.energy) * M.energy) =
    M.mass ^ 2 / M.energy
  field_simp [M.energy_ne_zero]

theorem optimizer_norm_sq : ‖M.optimizer‖ ^ 2 = M.mass ^ 2 / M.energy := by
  rw [← real_inner_self_eq_norm_sq]
  exact M.optimizer_energy

theorem admissible_inner_optimizer {f : E} (hf : M.Admissible f) :
    ⟪f, M.optimizer⟫ = M.mass ^ 2 / M.energy := by
  have hfs : ⟪f, M.projection⟫ = M.mass :=
    (M.projection_pairing f hf.1).trans hf.2.1
  rw [optimizer, real_inner_smul_right, hfs]
  ring

/-- Exact Pythagorean remainder, stronger than a minimum-value inequality. -/
theorem admissible_pythagorean {f : E} (hf : M.Admissible f) :
    ‖f - M.target‖ ^ 2 =
      ‖M.optimizer - M.target‖ ^ 2 + ‖f - M.optimizer‖ ^ 2 := by
  simp only [norm_sub_sq_real, hf.2.1, M.optimizer_inner_target,
    M.admissible_inner_optimizer hf, M.optimizer_norm_sq]
  ring

theorem optimizer_minimizes {f : E} (hf : M.Admissible f) :
    ‖M.optimizer - M.target‖ ^ 2 ≤ ‖f - M.target‖ ^ 2 := by
  have hp := M.admissible_pythagorean hf
  nlinarith [sq_nonneg ‖f - M.optimizer‖]

/-- Equality in the minimum-value inequality uniquely identifies the optimizer. -/
theorem error_eq_minimum_iff {f : E} (hf : M.Admissible f) :
    ‖f - M.target‖ ^ 2 = ‖M.optimizer - M.target‖ ^ 2 ↔
      f = M.optimizer := by
  constructor
  · intro he
    have hp := M.admissible_pythagorean hf
    have hn : ‖f - M.optimizer‖ = 0 := by
      nlinarith [norm_nonneg (f - M.optimizer)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · rintro rfl
    rfl

theorem optimizer_error :
    ‖M.optimizer - M.target‖ ^ 2 = M.mass ^ 2 / M.energy - M.mass := by
  have hy : ‖M.target‖ ^ 2 = M.mass := by
    rw [← real_inner_self_eq_norm_sq]
    exact M.target_energy
  rw [norm_sub_sq_real, M.optimizer_norm_sq, M.optimizer_inner_target, hy]
  ring

theorem defect_eq : M.defect = M.mass - M.energy := by
  have hy : ‖M.target‖ ^ 2 = M.mass := by
    rw [← real_inner_self_eq_norm_sq]
    exact M.target_energy
  have hs : ‖M.projection‖ ^ 2 = M.energy := by
    exact (real_inner_self_eq_norm_sq M.projection).symm
  have hys : ⟪M.target, M.projection⟫ = M.energy := by
    rw [real_inner_comm]
    exact M.projection_inner_target
  rw [defect, norm_sub_sq_real, hy, hs, hys]
  ring

theorem defect_nonneg : 0 ≤ M.defect := sq_nonneg _

theorem defect_lt_mass : M.defect < M.mass := by
  rw [M.defect_eq]
  linarith [M.energy_pos]

/-- General signal-mass formula; specializes to δ / (1 - 4δ). -/
theorem optimizer_error_as_defect :
    ‖M.optimizer - M.target‖ ^ 2 =
      M.mass * M.defect / (M.mass - M.defect) := by
  rw [M.optimizer_error, M.defect_eq]
  have hd : M.mass - (M.mass - M.energy) = M.energy := by ring
  rw [hd]
  field_simp [M.energy_ne_zero]

theorem quarter_denominator_pos (hq : M.mass = (1 : ℝ) / 4) :
    0 < 1 - 4 * M.defect := by
  have h := M.defect_lt_mass
  rw [hq] at h
  linarith

/-- Exact error formula from Proposition 2.1 of the supplied note. -/
theorem quarter_optimizer_error (hq : M.mass = (1 : ℝ) / 4) :
    ‖M.optimizer - M.target‖ ^ 2 = M.defect / (1 - 4 * M.defect) := by
  rw [M.optimizer_error_as_defect, hq]
  have hd := M.quarter_denominator_pos hq
  have hd' : (1 : ℝ) / 4 - M.defect ≠ 0 := by linarith
  field_simp [ne_of_gt hd, hd']

/-- Exact two-stage identity from Proposition 2.2. The two models may arise
from finite-dimensional or arbitrary orthogonally complemented subspaces. -/
theorem nested_optimizer_difference (N : ProjectionSignalModel E)
    (hspace : M.space ≤ N.space) (hy : M.target = N.target)
    (ho : M.complement = N.complement) (hq : M.mass = N.mass) :
    ‖M.optimizer - N.optimizer‖ ^ 2 =
      ‖M.optimizer - M.target‖ ^ 2 - ‖N.optimizer - N.target‖ ^ 2 := by
  have hM := M.optimizer_admissible
  have hN : N.Admissible M.optimizer := by
    refine ⟨hspace hM.1, ?_, ?_⟩
    · rw [← hy, ← hq]
      exact hM.2.1
    · rw [← ho]
      exact hM.2.2
  have hp := N.admissible_pythagorean hN
  rw [← hy] at hp
  rw [← hy]
  linarith

/-- Normalization preserves convergence when the signal mass is fixed and the
limiting projection is nonzero. Together with Mathlib's monotone-subspace
projection convergence theorem, this supplies the limit passage in Section 3
of the attached note. It imposes no conjectural vanishing of the defect. -/
theorem optimizer_tendsto {ι : Type*} {l : Filter ι}
    (Ms : ι → ProjectionSignalModel E)
    (hmass : ∀ i, (Ms i).mass = M.mass)
    (hprojection : Filter.Tendsto (fun i => (Ms i).projection) l
      (𝓝 M.projection)) :
    Filter.Tendsto (fun i => (Ms i).optimizer) l (𝓝 M.optimizer) := by
  have he : Filter.Tendsto (fun i => (Ms i).energy) l (𝓝 M.energy) := by
    simpa only [energy, real_inner_self_eq_norm_sq] using hprojection.norm.pow 2
  have hm : Filter.Tendsto (fun i => (Ms i).mass) l (𝓝 M.mass) := by
    have hmfun : (fun i => (Ms i).mass) = (fun _ : ι => M.mass) :=
      funext hmass
    rw [hmfun]
    exact tendsto_const_nhds
  have hc := hm.div he M.energy_ne_zero
  simpa only [optimizer, Pi.div_apply] using hc.smul hprojection

/-- Exact norm/error identity for unit-signal admissibility.
Source: user-provided boundedness-to-RH argument, 22 October 2026. -/
theorem admissible_norm_sq {f : E} (hf : M.Admissible f) :
    ‖f‖ ^ 2 = M.mass + ‖f - M.target‖ ^ 2 := by
  have hy : ‖M.target‖ ^ 2 = M.mass := by
    rw [← real_inner_self_eq_norm_sq]
    exact M.target_energy
  rw [norm_sub_sq_real, hf.2.1, hy]
  ring

/-- A fixed admissible competitor bounds every optimizer that admits it.
This does not assert target membership in the trial-space closure. -/
theorem optimizer_norm_sq_le_admissible {f : E} (hf : M.Admissible f) :
    ‖M.optimizer‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [M.admissible_norm_sq M.optimizer_admissible,
    M.admissible_norm_sq hf]
  linarith [M.optimizer_minimizes hf]

/-- Target identification requires saturation of the projection energy.
A positive lower bound only bounds the normalized optimizer. -/
theorem optimizer_eq_target_iff_energy_eq_mass :
    M.optimizer = M.target ↔ M.energy = M.mass := by
  constructor
  · intro h
    have hm : M.target ∈ M.space := h ▸ M.optimizer_admissible.1
    have hp := M.projection_pairing M.target hm
    calc
      M.energy = inner ℝ M.projection M.target := M.projection_inner_target.symm
      _ = inner ℝ M.target M.projection := real_inner_comm _ _
      _ = M.mass := hp.trans M.target_energy
  · intro h
    have hn : ‖M.optimizer - M.target‖ ^ 2 = 0 := by
      rw [M.optimizer_error, ← h]
      field_simp [M.energy_ne_zero]
      ring
    have hz : ‖M.optimizer - M.target‖ = 0 := by
      nlinarith [norm_nonneg (M.optimizer - M.target)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The normalized residual is generally not orthogonal to the trial space.
This keeps the signed term absent from the unnormalized projection residual. -/
theorem normalized_residual_pairing {f : E} (hf : f ∈ M.space) :
    inner ℝ (M.target - M.optimizer) f =
      (1 - M.mass / M.energy) * inner ℝ M.target f := by
  have hp : inner ℝ M.projection f = inner ℝ M.target f := by
    calc
      inner ℝ M.projection f = inner ℝ f M.projection := real_inner_comm _ _
      _ = inner ℝ f M.target := M.projection_pairing f hf
      _ = inner ℝ M.target f := real_inner_comm _ _
  rw [inner_sub_left, optimizer, real_inner_smul_left, hp]
  ring

end ProjectionSignalModel

end RiemannResearch.Analysis.UnitSignalProjection

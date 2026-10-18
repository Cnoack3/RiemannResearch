import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.Analysis.UnitSignalProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Actual inverse-square unit-signal optimizer

Application of the abstract normalization theorem to the actual `QHilbert`,
`qEven`, and `qOdd` from the full inverse-square law. Source: Sections 1--3 of
`Final_Limit_Unit_Signal_Residues_2026-10-11 (1).md`.

The only subspace inputs are an orthogonal projection and inclusion of the
legal atoms of conductors 2 and 3. Nonvanishing of the projected signal is
proved from the positive conductor-3 pairing; it is not assumed.

The limiting defect is not asserted to vanish. The convergence theorem uses
no conjectural arithmetic assumption and does not prove RH.
-/

noncomputable section

open Filter
open scoped Topology

namespace RiemannResearch.RH.ZetaTwoUnitSignal

open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoParitySignal
open RiemannResearch.Analysis.UnitSignalProjection
open RiemannResearch.Analysis.ExhaustiveWalk

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

omit [S.HasOrthogonalProjection] in
theorem qOdd_mem (h2 : qResidue 2 ∈ S) : qOdd ∈ S :=
  S.smul_mem (2 : ℝ) h2

/-- The actual projected signal is nonzero because conductor 3 sees it. -/
theorem projected_qEven_ne_zero (h3 : qResidue 3 ∈ S) :
    S.starProjection qEven ≠ 0 := by
  intro hz
  have hinner : ⟪qResidue 3, qEven - S.starProjection qEven⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal h3
      (Submodule.sub_starProjection_mem_orthogonal (K := S) qEven)
  rw [hz, sub_zero, real_inner_comm] at hinner
  exact (ne_of_gt qEven_inner_qResidue_three_pos) hinner

/-- The generic model instantiated with the actual full-law parity indicators. -/
def unitSignalModel (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    ProjectionSignalModel QHilbert :=
  ProjectionSignalModel.ofStarProjection S qEven qOdd (qOdd_mem S h2)
    qEven_inner_qOdd (projected_qEven_ne_zero S h3)

@[simp] theorem unitSignalModel_mass (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) : (unitSignalModel S h2 h3).mass = (1 / 4 : ℝ) :=
  qEven_inner_self

/-- Squared approximation error of the constant in the actual Q norm. -/
def qUnitSignalDefect : ℝ := ‖qOne - S.starProjection qOne‖ ^ 2

/-- The unit-signal optimizer in the given subspace. -/
def qUnitSignalOptimizer (h2 : qResidue 2 ∈ S) (h3 : qResidue 3 ∈ S) :
    QHilbert := (unitSignalModel S h2 h3).optimizer

/-- The constant and parity target have exactly the same projection residual. -/
theorem qOne_residual_eq_qEven_residual (h2 : qResidue 2 ∈ S) :
    qOne - S.starProjection qOne = qEven - S.starProjection qEven := by
  have ho : S.starProjection qOdd = qOdd :=
    Submodule.starProjection_eq_self_iff.mpr (qOdd_mem S h2)
  rw [← qEven_add_qOdd, map_add, ho]
  abel

@[simp] theorem unitSignalModel_defect (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) :
    (unitSignalModel S h2 h3).defect = qUnitSignalDefect S := by
  change ‖qEven - S.starProjection qEven‖ ^ 2 =
    ‖qOne - S.starProjection qOne‖ ^ 2
  rw [qOne_residual_eq_qEven_residual S h2]

theorem qUnitSignalDefect_nonneg : 0 ≤ qUnitSignalDefect S := sq_nonneg _

theorem qUnitSignalDefect_lt_quarter (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) : qUnitSignalDefect S < (1 / 4 : ℝ) := by
  have h := (unitSignalModel S h2 h3).defect_lt_mass
  simpa only [unitSignalModel_defect, unitSignalModel_mass] using h

theorem qUnitSignal_denominator_pos (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) : 0 < 1 - 4 * qUnitSignalDefect S := by
  linarith [qUnitSignalDefect_lt_quarter S h2 h3]

theorem qUnitSignalOptimizer_eq_projection (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) :
    qUnitSignalOptimizer S h2 h3 =
      ((1 / 4 : ℝ) / ⟪S.starProjection qEven, S.starProjection qEven⟫) •
        S.starProjection qEven := by
  change (⟪qEven, qEven⟫ / ⟪S.starProjection qEven, S.starProjection qEven⟫) •
    S.starProjection qEven = _
  rw [qEven_inner_self]

/-- Both unit-signal moments and legality are actual QHilbert conclusions. -/
theorem qUnitSignalOptimizer_admissible (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) :
    qUnitSignalOptimizer S h2 h3 ∈ S ∧
      ⟪qUnitSignalOptimizer S h2 h3, qEven⟫ = (1 / 4 : ℝ) ∧
      ⟪qUnitSignalOptimizer S h2 h3, qOdd⟫ = 0 := by
  have h := (unitSignalModel S h2 h3).optimizer_admissible
  change qUnitSignalOptimizer S h2 h3 ∈ S ∧
    ⟪qUnitSignalOptimizer S h2 h3, qEven⟫ = ⟪qEven, qEven⟫ ∧
    ⟪qUnitSignalOptimizer S h2 h3, qOdd⟫ = 0 at h
  simpa only [qEven_inner_self] using h

/-- Proposition 2.1 specialized to the actual inverse-square law. -/
theorem qUnitSignalOptimizer_error (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) :
    ‖qUnitSignalOptimizer S h2 h3 - qEven‖ ^ 2 =
      qUnitSignalDefect S / (1 - 4 * qUnitSignalDefect S) := by
  have h := (unitSignalModel S h2 h3).quarter_optimizer_error
    (unitSignalModel_mass S h2 h3)
  change ‖qUnitSignalOptimizer S h2 h3 - qEven‖ ^ 2 =
    (unitSignalModel S h2 h3).defect / (1 - 4 * (unitSignalModel S h2 h3).defect) at h
  simpa only [unitSignalModel_defect] using h

/-- Exact error decomposition for every legal competitor with unit parity signal. -/
theorem qUnitSignalOptimizer_pythagorean (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) (f : QHilbert) (hf : f ∈ S)
    (hfe : ⟪f, qEven⟫ = (1 / 4 : ℝ)) (hfo : ⟪f, qOdd⟫ = 0) :
    ‖f - qEven‖ ^ 2 = ‖qUnitSignalOptimizer S h2 h3 - qEven‖ ^ 2 +
      ‖f - qUnitSignalOptimizer S h2 h3‖ ^ 2 := by
  have hadmissible : (unitSignalModel S h2 h3).Admissible f := by
    refine ⟨hf, ?_, hfo⟩
    change ⟪f, qEven⟫ = ⟪qEven, qEven⟫
    rw [qEven_inner_self]
    exact hfe
  exact (unitSignalModel S h2 h3).admissible_pythagorean hadmissible

/-- The optimizer attains the minimum; equality is possible for it alone. -/
theorem qUnitSignalOptimizer_unique (h2 : qResidue 2 ∈ S)
    (h3 : qResidue 3 ∈ S) (f : QHilbert) (hf : f ∈ S)
    (hfe : ⟪f, qEven⟫ = (1 / 4 : ℝ)) (hfo : ⟪f, qOdd⟫ = 0) :
    ‖f - qEven‖ ^ 2 = ‖qUnitSignalOptimizer S h2 h3 - qEven‖ ^ 2 ↔
      f = qUnitSignalOptimizer S h2 h3 := by
  have hadmissible : (unitSignalModel S h2 h3).Admissible f := by
    refine ⟨hf, ?_, hfo⟩
    change ⟪f, qEven⟫ = ⟪qEven, qEven⟫
    rw [qEven_inner_self]
    exact hfe
  exact (unitSignalModel S h2 h3).error_eq_minimum_iff hadmissible

/-! ## The actual exhaustive all-conductor sequence

`allConductorStage n` includes conductors 2 through n+3. Thus its optimizer is
the note's `U_(n+3)`. The shift ensures that both conductors 2 and 3 occur from
the first stage onward.
-/

def allConductorDictionary (i : ℕ) : QHilbert := qResidue (i + 2)

def allConductorStage (n : ℕ) : Submodule ℝ QHilbert :=
  walkSpan allConductorDictionary id (n + 2)

def allConductorSpace : Submodule ℝ QHilbert :=
  dictionaryClosure allConductorDictionary

instance allConductorStage_hasOrthogonalProjection (n : ℕ) :
    (allConductorStage n).HasOrthogonalProjection := by
  unfold allConductorStage
  infer_instance

instance allConductorSpace_hasOrthogonalProjection :
    allConductorSpace.HasOrthogonalProjection := by
  unfold allConductorSpace dictionaryClosure
  infer_instance

theorem allConductorStage_mem_two (n : ℕ) : qResidue 2 ∈ allConductorStage n := by
  change qResidue 2 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin (n + 2) => allConductorDictionary (i : ℕ)))
  apply Submodule.subset_span
  exact ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩

theorem allConductorStage_mem_three (n : ℕ) : qResidue 3 ∈ allConductorStage n := by
  change qResidue 3 ∈ Submodule.span ℝ
    (Set.range (fun i : Fin (n + 2) => allConductorDictionary (i : ℕ)))
  apply Submodule.subset_span
  exact ⟨⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ n)⟩, rfl⟩

theorem allConductorSpace_mem_two : qResidue 2 ∈ allConductorSpace := by
  apply (Submodule.span ℝ (Set.range allConductorDictionary)).le_topologicalClosure
  exact Submodule.subset_span ⟨0, rfl⟩

theorem allConductorSpace_mem_three : qResidue 3 ∈ allConductorSpace := by
  apply (Submodule.span ℝ (Set.range allConductorDictionary)).le_topologicalClosure
  exact Submodule.subset_span ⟨1, rfl⟩

def allConductorModel (n : ℕ) : ProjectionSignalModel QHilbert :=
  unitSignalModel (allConductorStage n)
    (allConductorStage_mem_two n) (allConductorStage_mem_three n)

def allConductorLimitModel : ProjectionSignalModel QHilbert :=
  unitSignalModel allConductorSpace allConductorSpace_mem_two allConductorSpace_mem_three

def allConductorOptimizer (n : ℕ) : QHilbert := (allConductorModel n).optimizer

def allConductorLimit : QHilbert := allConductorLimitModel.optimizer

theorem allConductorProjection_tendsto :
    Tendsto (fun n => (allConductorStage n).starProjection qEven) atTop
      (𝓝 (allConductorSpace.starProjection qEven)) := by
  have h := walkProjection_tendsto allConductorDictionary id Function.surjective_id qEven
  simpa only [Function.comp_def, allConductorStage, allConductorSpace] using
    h.comp (tendsto_add_atTop_nat 2)

/-- Unconditional norm convergence of the actual unit-signal optimizers.
This identifies their projection-based limit without asserting it is `qEven`. -/
theorem allConductorOptimizer_tendsto :
    Tendsto allConductorOptimizer atTop (𝓝 allConductorLimit) := by
  exact allConductorLimitModel.optimizer_tendsto allConductorModel
    (by intro n; rfl) allConductorProjection_tendsto

theorem allConductorLimit_error :
    ‖allConductorLimit - qEven‖ ^ 2 =
      qUnitSignalDefect allConductorSpace /
        (1 - 4 * qUnitSignalDefect allConductorSpace) :=
  qUnitSignalOptimizer_error allConductorSpace
    allConductorSpace_mem_two allConductorSpace_mem_three

theorem allConductorError_tendsto :
    Tendsto (fun n => ‖allConductorOptimizer n - qEven‖ ^ 2) atTop
      (𝓝 (‖allConductorLimit - qEven‖ ^ 2)) := by
  exact (allConductorOptimizer_tendsto.sub tendsto_const_nhds).norm.pow 2

end RiemannResearch.RH.ZetaTwoUnitSignal

import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.Analysis.CompressedMomentZeroCriterion
import RiemannResearch.RH.ZetaTwoMobiusQuarticFloorDecay
import RiemannResearch.RH.ZetaTwoWeightedFloorNormalization
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Actual inverse-square squarefree optimizer stages

Source: user-provided `Exact_Optimizer_Cancellation_20261008.tex` and the
exact signed optimizer moment argument. Every object here is in the actual
inverse-square Hilbert realization. The signed correction retains the
complete weighted optimizer mismatch and the ordinary screening norm.

No RH-strength closure statement or cancellation provider is assumed as an
established fact. The cofinal result concludes literal squarefree closure;
the RH identification and the positive signed-cancellation provider remain
separate arithmetic assembly obligations.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ZetaTwoOptimizerStage
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.LinearAlgebra

/-- A redundant but exhaustive dictionary of exactly the legal squarefree
residue atoms. Nonsquarefree coordinates are the zero vector. -/
def squarefreeAtom (i : ℕ) : QHilbert :=
  if Squarefree (i + 2) then qResidue (i + 2) else 0

def stage (n : ℕ) : Submodule ℝ QHilbert := walkSpan squarefreeAtom id n

instance stage_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (stage n) := by
  unfold stage
  infer_instance

def closure : Submodule ℝ QHilbert := dictionaryClosure squarefreeAtom

instance closure_hasOrthogonalProjection : closure.HasOrthogonalProjection := by
  unfold closure
  infer_instance

def optimizer (n : ℕ) : QHilbert := (stage n).starProjection qOne

def residual (n : ℕ) : QHilbert := qOne - optimizer n

def limitingResidual : QHilbert := qOne - closure.starProjection qOne

def error (n : ℕ) : ℝ := ‖residual n‖ ^ 2

def weightedAtom (i : ℕ) : QHilbert := reciprocalD (squarefreeAtom i)

def weightedStage (n : ℕ) : Submodule ℝ QHilbert := walkSpan weightedAtom id n

instance weightedStage_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (weightedStage n) := by
  unfold weightedStage
  infer_instance

def weightedOptimizer (n : ℕ) : QHilbert :=
  (weightedStage n).starProjection (reciprocalD qOne)

/-- The actual optimum with complete `k^-4` weights. -/
def quarticFloor (n : ℕ) : ℝ := ‖reciprocalD qOne - weightedOptimizer n‖ ^ 2

def weightedMismatch (n : ℕ) : ℝ :=
  ‖reciprocalD (optimizer n) - weightedOptimizer n‖ ^ 2

def screening (n : ℕ) : ℝ :=
  ‖(stage n).starProjection (reciprocalD (residual n))‖ ^ 2

/-- Both positive squares are retained in this signed quantity. -/
def signedCorrection (n : ℕ) : ℝ := weightedMismatch n - screening n

def screenedResidual (n : ℕ) : QHilbert :=
  reciprocalD (residual n) - (stage n).starProjection (reciprocalD (residual n))

def secondMoment (n : ℕ) : ℝ := ‖screenedResidual n‖ ^ 2 / error n

/-- The actual legal Möbius trial in the stage's squarefree dictionary. -/
def mobiusTrial (n : ℕ) : QHilbert :=
  finiteSchurCombination (fun i : Fin n => squarefreeAtom i)
    (fun i => -(ArithmeticFunction.moebius (i.val + 2) : ℝ))

theorem residual_mem_orthogonal (n : ℕ) : residual n ∈ (stage n)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal qOne

theorem optimizer_tendsto :
    Tendsto optimizer atTop (𝓝 (closure.starProjection qOne)) := by
  change Tendsto (fun n => (walkSpan squarefreeAtom id n).starProjection qOne)
    atTop (𝓝 ((dictionaryClosure squarefreeAtom).starProjection qOne))
  exact walkProjection_tendsto squarefreeAtom id Function.surjective_id qOne

theorem residual_tendsto : Tendsto residual atTop (𝓝 limitingResidual) := by
  exact tendsto_const_nhds.sub optimizer_tendsto

theorem error_tendsto_zero_iff_mem_closure :
    Tendsto error atTop (𝓝 0) ↔ qOne ∈ closure := by
  change Tendsto (fun n => ‖qOne -
    (walkSpan squarefreeAtom id n).starProjection qOne‖ ^ 2) atTop (𝓝 0) ↔
      qOne ∈ dictionaryClosure squarefreeAtom
  exact walkError_tendsto_zero_iff squarefreeAtom id Function.surjective_id qOne

theorem stage_coordinate_zero (n : ℕ) (v : QHilbert) (hv : v ∈ stage n) :
    qSequence v ((n + 2).factorial) = 0 := by
  unfold stage walkSpan at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      change qSequence (squarefreeAtom i.val) ((n + 2).factorial) = 0
      by_cases hs : Squarefree (i.val + 2)
      · rw [squarefreeAtom, if_pos hs, qSequence_qResidue]
        have hdvd : i.val + 2 ∣ (n + 2).factorial :=
          Nat.dvd_factorial (by omega) (by omega)
        simp [residueFraction, Nat.mod_eq_zero_of_dvd hdvd]
      · rw [squarefreeAtom, if_neg hs]
        change qSequenceLinear 0 _ = 0
        rw [map_zero]
        rfl
  | zero =>
      change qSequenceLinear 0 _ = 0
      rw [map_zero]
      rfl
  | add x y hx hy ihx ihy =>
      change qSequenceLinear (x + y) _ = 0
      rw [map_add]
      change qSequence x _ + qSequence y _ = 0
      rw [ihx, ihy, add_zero]
  | smul c x hx ih =>
      change qSequenceLinear (c • x) _ = 0
      rw [map_smul]
      change c * qSequence x _ = 0
      rw [ih, mul_zero]

/-- Every finite-stage error is strictly positive. A common factorial
multiple makes every finite legal atom zero while the target equals one. -/
theorem error_pos (n : ℕ) : 0 < error n := by
  have hpzero := stage_coordinate_zero n (optimizer n)
    ((stage n).starProjection_apply_mem qOne)
  have hone : qSequence qOne ((n + 2).factorial) = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt (Nat.factorial_pos (n + 2))]
  have hrone : qSequenceLinear (residual n) ((n + 2).factorial) = 1 := by
    change qSequenceLinear (qOne - optimizer n) _ = 1
    rw [map_sub]
    change qSequence qOne _ - qSequence (optimizer n) _ = 1
    rw [hone, hpzero, sub_zero]
  have hrne : residual n ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hrone
    norm_num at hrone
  exact sq_pos_of_pos (norm_pos_iff.mpr hrne)

/-- The actual unweighted optimizer has finite normal-equation coefficients,
even though the squarefree dictionary includes redundant zero atoms. -/
theorem exists_optimizer_coefficients (n : ℕ) :
    ∃ c : Fin n → ℝ,
      finiteSchurCombination (fun i : Fin n => squarefreeAtom i) c = optimizer n ∧
      ∀ i : Fin n, inner ℝ (squarefreeAtom i)
        (finiteSchurCombination (fun j : Fin n => squarefreeAtom j) c) =
          inner ℝ (squarefreeAtom i) qOne := by
  have hp : optimizer n ∈ stage n := (stage n).starProjection_apply_mem qOne
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have hcombo : finiteSchurCombination (fun i : Fin n => squarefreeAtom i) c =
      optimizer n := hc
  refine ⟨c, hcombo, ?_⟩
  intro i
  have hi : squarefreeAtom i ∈ stage n := Submodule.subset_span ⟨i, rfl⟩
  have ho := ((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _ hi
  change inner ℝ (squarefreeAtom i) (qOne - optimizer n) = 0 at ho
  rw [inner_sub_right] at ho
  rw [hcombo]
  exact (sub_eq_zero.mp ho).symm

theorem exists_weighted_optimizer_coefficients (n : ℕ) :
    ∃ cD : Fin n → ℝ,
      finiteSchurCombination (fun i : Fin n => reciprocalD (squarefreeAtom i)) cD =
        weightedOptimizer n ∧
      ∀ i : Fin n, inner ℝ (reciprocalD (squarefreeAtom i))
        (finiteSchurCombination (fun j : Fin n => reciprocalD (squarefreeAtom j)) cD) =
          inner ℝ (reciprocalD (squarefreeAtom i)) (reciprocalD qOne) := by
  have hp : weightedOptimizer n ∈ weightedStage n :=
    (weightedStage n).starProjection_apply_mem (reciprocalD qOne)
  obtain ⟨cD, hcD⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have hcombo : finiteSchurCombination
      (fun i : Fin n => reciprocalD (squarefreeAtom i)) cD = weightedOptimizer n := hcD
  refine ⟨cD, hcombo, ?_⟩
  intro i
  have hi : reciprocalD (squarefreeAtom i) ∈ weightedStage n :=
    Submodule.subset_span ⟨i, rfl⟩
  have ho := ((weightedStage n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal (reciprocalD qOne)) _ hi
  change inner ℝ (reciprocalD (squarefreeAtom i))
    (reciprocalD qOne - weightedOptimizer n) = 0 at ho
  rw [inner_sub_right] at ho
  rw [hcombo]
  exact (sub_eq_zero.mp ho).symm

theorem exists_screening_coefficients (n : ℕ) :
    ∃ b : Fin n → ℝ,
      finiteSchurCombination (fun i : Fin n => squarefreeAtom i) b =
        (stage n).starProjection (reciprocalD (residual n)) ∧
      ∀ i : Fin n, inner ℝ (squarefreeAtom i)
        (finiteSchurCombination (fun j : Fin n => squarefreeAtom j) b) =
          inner ℝ (squarefreeAtom i) (reciprocalD (residual n)) := by
  have hp : (stage n).starProjection (reciprocalD (residual n)) ∈ stage n :=
    (stage n).starProjection_apply_mem _
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have hcombo : finiteSchurCombination (fun i : Fin n => squarefreeAtom i) b =
      (stage n).starProjection (reciprocalD (residual n)) := hb
  refine ⟨b, hcombo, ?_⟩
  intro i
  have hi : squarefreeAtom i ∈ stage n := Submodule.subset_span ⟨i, rfl⟩
  have ho := ((stage n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal (reciprocalD (residual n))) _ hi
  rw [inner_sub_right] at ho
  rw [hcombo]
  exact (sub_eq_zero.mp ho).symm

theorem reciprocal_optimizer_mem_weightedStage (n : ℕ) :
    reciprocalD (optimizer n) ∈ weightedStage n := by
  have hp : optimizer n ∈ stage n := (stage n).starProjection_apply_mem qOne
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hp
  have hcombo : finiteSchurCombination (fun i : Fin n => squarefreeAtom i) c =
      optimizer n := hc
  rw [← hcombo]
  unfold finiteSchurCombination
  rw [map_sum]
  apply (weightedStage n).sum_mem
  intro i hi
  rw [map_smul]
  apply (weightedStage n).smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

theorem reciprocal_mobiusTrial_mem_weightedStage (n : ℕ) :
    reciprocalD (mobiusTrial n) ∈ weightedStage n := by
  unfold mobiusTrial finiteSchurCombination
  rw [map_sum]
  apply (weightedStage n).sum_mem
  intro i hi
  rw [map_smul]
  apply (weightedStage n).smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem mobius_sum_reindex (n k : ℕ) :
    (∑ i : Fin n, (ArithmeticFunction.moebius (i.val + 2) : ℝ) *
      residueFraction (i.val + 2) k) =
      ∑ d ∈ Finset.Icc 1 (n + 1),
        (ArithmeticFunction.moebius d : ℝ) * residueFraction d k := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (ArithmeticFunction.moebius (i + 2) : ℝ) *
      residueFraction (i + 2) k) n]
  induction n with
  | zero => simp [residueFraction, Nat.mod_one]
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

theorem qSequence_mobiusResidual (n k : ℕ) (hk : 0 < k) :
    qSequence (qOne - mobiusTrial n) k =
      RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual (n + 1) k := by
  have hone : qSequence qOne k = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hk]
  have hmu : ∀ i : Fin n,
      -(ArithmeticFunction.moebius (i.val + 2) : ℝ) *
        qSequence (squarefreeAtom i) k =
      -(ArithmeticFunction.moebius (i.val + 2) : ℝ) * residueFraction (i.val + 2) k := by
    intro i
    unfold squarefreeAtom
    split_ifs with hs
    · rw [qSequence_qResidue]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  change qSequenceLinear (qOne - mobiusTrial n) k = _
  rw [map_sub]
  change qSequence qOne k - qSequenceLinear (mobiusTrial n) k = _
  rw [hone]
  unfold mobiusTrial finiteSchurCombination
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change 1 - (∑ i : Fin n, -(ArithmeticFunction.moebius (i.val + 2) : ℝ) *
    qSequence (squarefreeAtom i) k) = _
  simp_rw [hmu]
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, mobius_sum_reindex]
  rfl

/-- Exact equality of the actual reciprocal norm and the complete physical
quartic energy, including the zero-weight coordinate. -/
theorem reciprocal_norm_eq_quarticEnergy (v : QHilbert) :
    ‖reciprocalD v‖ ^ 2 =
      RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy (qSequence v) := by
  rw [qNorm_weighted_sq]
  simp_rw [qSequence_reciprocalD]
  unfold RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
    RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergyTerm
  congr 1
  funext k
  by_cases hk : k = 0
  · simp [hk, positiveQWeight]
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    unfold positiveQWeight
    field_simp [hkR, ne_of_gt RiemannResearch.RH.ZetaTwoProbability.zetaTwo_pos]

theorem mobiusTrial_quartic_energy (n : ℕ) :
    ‖reciprocalD (qOne - mobiusTrial n)‖ ^ 2 =
      RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
        (RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual (n + 1)) := by
  rw [reciprocal_norm_eq_quarticEnergy]
  unfold RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
  congr 1
  funext k
  by_cases hk : k = 0
  · simp [hk, RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergyTerm]
  · rw [RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergyTerm,
      qSequence_mobiusResidual n k (Nat.pos_of_ne_zero hk)]
    rfl

/-- Exact complete Möbius trial error, retaining the weighted optimizer
displacement square before estimating it. -/
theorem mobiusTrial_energy_exact (n : ℕ) :
      RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
        (RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual (n + 1)) =
      quarticFloor n + ‖reciprocalD (mobiusTrial n) - weightedOptimizer n‖ ^ 2 := by
  have horth : inner ℝ (reciprocalD qOne - weightedOptimizer n)
      (weightedOptimizer n - reciprocalD (mobiusTrial n)) = 0 := by
    rw [real_inner_comm]
    exact ((weightedStage n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (reciprocalD qOne)) _
      ((weightedStage n).sub_mem
        ((weightedStage n).starProjection_apply_mem (reciprocalD qOne))
        (reciprocal_mobiusTrial_mem_weightedStage n))
  have he : reciprocalD (qOne - mobiusTrial n) =
      (reciprocalD qOne - weightedOptimizer n) +
        (weightedOptimizer n - reciprocalD (mobiusTrial n)) := by
    rw [map_sub]
    abel
  rw [← mobiusTrial_quartic_energy, he, norm_add_sq_real, horth]
  unfold quarticFloor
  rw [norm_sub_rev (weightedOptimizer n) (reciprocalD (mobiusTrial n))]
  ring

/-- The actual weighted optimum is dominated by the actual admissible
Möbius trial; no variational infimum is assumed to be a projection. -/
theorem quarticFloor_le_mobiusTrial (n : ℕ) :
    quarticFloor n ≤
      RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
        (RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual (n + 1)) := by
  rw [mobiusTrial_energy_exact]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The actual stage's complete quartic optimum tends to zero
unconditionally, supplied by the established Möbius trial arithmetic. -/
theorem quarticFloor_tendsto_zero : Tendsto quarticFloor atTop (𝓝 0) := by
  have htrial := RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual_quarticEnergy_mul_shiftedLogPow_tendsto_zero 0
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hlim : Tendsto
      (fun n => RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.quarticEnergy
        (RiemannResearch.RH.Pareto.ZetaTwoMobiusFloor.residual (n + 1)))
      atTop (𝓝 0) := by
        simpa only [Function.comp_def, pow_zero, mul_one] using htrial.comp hshift
  exact squeeze_zero (fun n => sq_nonneg _) quarticFloor_le_mobiusTrial hlim

/-- Actual `h₂=ε₂+δ₂`, with complete weighted norms. -/
theorem weightedResidual_eq_floor_add_mismatch (n : ℕ) :
    ‖reciprocalD (residual n)‖ ^ 2 = quarticFloor n + weightedMismatch n := by
  have horth : inner ℝ
      (reciprocalD qOne - weightedOptimizer n)
      (weightedOptimizer n - reciprocalD (optimizer n)) = 0 := by
    rw [real_inner_comm]
    exact ((weightedStage n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal (reciprocalD qOne)) _
      ((weightedStage n).sub_mem
        ((weightedStage n).starProjection_apply_mem (reciprocalD qOne))
        (reciprocal_optimizer_mem_weightedStage n))
  have he : reciprocalD (residual n) =
      (reciprocalD qOne - weightedOptimizer n) +
        (weightedOptimizer n - reciprocalD (optimizer n)) := by
    change reciprocalD (qOne - optimizer n) = _
    rw [map_sub]
    abel
  rw [he, norm_add_sq_real, horth]
  unfold quarticFloor weightedMismatch
  rw [norm_sub_rev (weightedOptimizer n) (reciprocalD (optimizer n))]
  ring

theorem quarticFloor_le_weightedResidual (n : ℕ) :
    quarticFloor n ≤ ‖reciprocalD (residual n)‖ ^ 2 := by
  rw [weightedResidual_eq_floor_add_mismatch]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem residual_ne_zero (n : ℕ) : residual n ≠ 0 := by
  intro hzero
  have hp := error_pos n
  simp [error, hzero] at hp

/-- The actual quartic optimum is small relative to the actual moving
unweighted optimum, unconditionally. Absolute arithmetic decay and canonical
normalized compact geometry supply both cases of the proof. -/
theorem quarticFloor_normalized_tendsto_zero :
    Tendsto (fun n => quarticFloor n / error n) atTop (𝓝 0) := by
  simpa only [error, residual, optimizer, stage] using
    reciprocalWeightedFloor_ratio_tendsto_zero squarefreeAtom qOne quarticFloor
      residual_ne_zero (fun n => sq_nonneg _)
      quarticFloor_le_weightedResidual quarticFloor_tendsto_zero

/-- Actual `e*m₂=ε₂+Γ`, with both positive squares in `Γ`. -/
theorem screenedResidual_energy_exact (n : ℕ) :
    ‖screenedResidual n‖ ^ 2 = quarticFloor n + signedCorrection n := by
  have hproj := RiemannResearch.LinearAlgebra.inner_residualized_eq_schur
    (stage n) (reciprocalD (residual n)) (reciprocalD (residual n))
  simp only [real_inner_self_eq_norm_sq] at hproj
  change ‖reciprocalD (residual n) -
    (stage n).starProjection (reciprocalD (residual n))‖ ^ 2 = _
  rw [hproj, weightedResidual_eq_floor_add_mismatch]
  unfold signedCorrection screening
  ring

theorem signedCorrection_ge_neg_floor (n : ℕ) :
    -quarticFloor n ≤ signedCorrection n := by
  have he := screenedResidual_energy_exact n
  have hn := sq_nonneg ‖screenedResidual n‖
  linarith

theorem residual_inner_screened (n : ℕ) :
    inner ℝ (residual n) (screenedResidual n) =
      inner ℝ (residual n) (reciprocalD (residual n)) := by
  have ho : inner ℝ (residual n)
      ((stage n).starProjection (reciprocalD (residual n))) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (residual_mem_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  simp only [screenedResidual, inner_sub_right, ho, sub_zero]

/-- A literal actual-Q cofinal compressed-moment consumer, using the proved
faithfulness of the physical reciprocal multiplier. -/
theorem mem_closure_of_cofinal_secondMoment
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hmoment : Tendsto (fun j => secondMoment (κ j)) atTop (𝓝 0)) :
    qOne ∈ closure := by
  have hzero := RiemannResearch.Analysis.CompressedMomentZeroCriterion.limit_eq_zero_of_cofinal_normalizedScreenedMoment reciprocalD reciprocalD_faithful
      residual screenedResidual limitingResidual residual_tendsto error_pos
      residual_inner_screened κ hκ hmoment
  have herror : Tendsto error atTop (𝓝 0) := by
    change Tendsto (fun n => ‖residual n‖ ^ 2) atTop (𝓝 0)
    simpa only [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      residual_tendsto.norm.pow 2
  exact error_tendsto_zero_iff_mem_closure.mp herror

/-- The literal signed-cancellation consumer. Its only decay inputs are the
actual normalized quartic floor and the positive part of the actual signed
correction. Faithfulness, strong convergence, positivity of finite errors,
and the screening identity have already been proved above. -/
theorem mem_closure_of_cofinal_positiveCorrection
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hfloor : Tendsto (fun j => quarticFloor (κ j) / error (κ j)) atTop (𝓝 0))
    (hcorrection : Tendsto
      (fun j => max (signedCorrection (κ j)) 0 / error (κ j)) atTop (𝓝 0)) :
    qOne ∈ closure := by
  have hmoment := (RiemannResearch.Analysis.SignedOptimizerMoment.normalizedMoment_tendsto_zero_iff_positiveCorrection
      (e := fun j => error (κ j)) (ε := fun j => quarticFloor (κ j))
      (Γ := fun j => signedCorrection (κ j))
      (M := fun j => ‖screenedResidual (κ j)‖ ^ 2)
      (fun j => error_pos (κ j)) (fun j => sq_nonneg _)
      (fun j => sq_nonneg _) (fun j => screenedResidual_energy_exact (κ j))
      hfloor).mpr hcorrection
  exact mem_closure_of_cofinal_secondMoment κ hκ hmoment

/-- Actual-Q one-provider cofinal criterion: the normalized weighted floor
has already been discharged unconditionally. -/
theorem mem_closure_of_cofinal_positiveCorrection_decay
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hcorrection : Tendsto
      (fun j => max (signedCorrection (κ j)) 0 / error (κ j)) atTop (𝓝 0)) :
    qOne ∈ closure :=
  mem_closure_of_cofinal_positiveCorrection κ hκ
    (quarticFloor_normalized_tendsto_zero.comp hκ) hcorrection

/-- The negative part is already solved unconditionally after the complete
moving normalization. The positive signed part is the remaining provider. -/
theorem negativeCorrection_normalized_tendsto_zero :
    Tendsto (fun n => max (-signedCorrection n) 0 / error n) atTop (𝓝 0) := by
  exact RiemannResearch.Analysis.SignedOptimizerMoment.normalizedNegativeCorrection_tendsto_zero error_pos (fun n => sq_nonneg _)
      (fun n => sq_nonneg _) screenedResidual_energy_exact
      quarticFloor_normalized_tendsto_zero

theorem secondMoment_tendsto_zero_of_mem_closure (hclosure : qOne ∈ closure) :
    Tendsto secondMoment atTop (𝓝 0) := by
  have hlimit : limitingResidual = 0 := by
    unfold limitingResidual
    rw [Submodule.starProjection_eq_self_iff.mpr hclosure, sub_self]
  have hrzero : Tendsto residual atTop (𝓝 0) := by
    simpa only [hlimit] using residual_tendsto
  have hDzero : Tendsto
      (fun n => ‖reciprocalD (residual n)‖ ^ 2 / error n) atTop (𝓝 0) := by
    simpa only [error, residual, optimizer, stage] using
      normalizedWalkResidual_reciprocalEnergy_tendsto_zero
        squarefreeAtom qOne hrzero residual_ne_zero
  have hscreen_le : ∀ n, ‖screenedResidual n‖ ^ 2 ≤
      ‖reciprocalD (residual n)‖ ^ 2 := by
    intro n
    have hproj := inner_residualized_eq_schur (stage n)
      (reciprocalD (residual n)) (reciprocalD (residual n))
    simp only [real_inner_self_eq_norm_sq] at hproj
    change ‖reciprocalD (residual n) -
      (stage n).starProjection (reciprocalD (residual n))‖ ^ 2 ≤ _
    rw [hproj]
    exact sub_le_self _ (sq_nonneg _)
  apply squeeze_zero
    (fun n => div_nonneg (sq_nonneg _) (error_pos n).le)
    (fun n => div_le_div_of_nonneg_right (hscreen_le n) (error_pos n).le)
    hDzero

/-- Exact actual-Q squarefree closure criterion. Both arithmetic floor decay
and reciprocal compact geometry have been discharged; the displayed positive
signed-cancellation limit is the sole remaining input. -/
theorem mem_closure_iff_positiveCorrection :
    qOne ∈ closure ↔
      Tendsto (fun n => max (signedCorrection n) 0 / error n) atTop (𝓝 0) := by
  constructor
  · intro hclosure
    apply (RiemannResearch.Analysis.SignedOptimizerMoment.normalizedMoment_tendsto_zero_iff_positiveCorrection
        error_pos (fun n => sq_nonneg _) (fun n => sq_nonneg _)
        screenedResidual_energy_exact quarticFloor_normalized_tendsto_zero).mp
    exact secondMoment_tendsto_zero_of_mem_closure hclosure
  · intro hcorrection
    exact mem_closure_of_cofinal_positiveCorrection_decay id tendsto_id hcorrection

/-- Cofinal signed-cancellation is equivalent to the same actual closure;
neither the moments nor the signed correction are assumed monotone. -/
theorem mem_closure_iff_cofinal_positiveCorrection :
    qOne ∈ closure ↔ ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧
      Tendsto (fun j => max (signedCorrection (κ j)) 0 / error (κ j))
        atTop (𝓝 0) := by
  constructor
  · intro hclosure
    exact ⟨id, tendsto_id, mem_closure_iff_positiveCorrection.mp hclosure⟩
  · rintro ⟨κ, hκ, hcorrection⟩
    exact mem_closure_of_cofinal_positiveCorrection_decay κ hκ hcorrection

end RiemannResearch.RH.ZetaTwoOptimizerStage

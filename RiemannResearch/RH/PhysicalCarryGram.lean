import RiemannResearch.Analysis.FiniteSingularGramReconstruction
import RiemannResearch.LinearAlgebra.CarryGramCongruence
import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.ParetoExactHeadCRT
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ResidueGramDigamma
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.QResidueMoments

/-!
# Physical Gram and target transport at a finite conductor

Source: the user's atom/carry CRT agenda, §§14.5 and 14.6. Columns of the
finite change matrix are synthesized in the given physical space. We prove
the exact Gram and observation laws, including the least-energy law at
singular Gram matrices. The Pareto weight defect and Green boundary and tail
are explicit. The Q packet pairing uses the Q weight.
-/

noncomputable section
open scoped BigOperators Matrix
namespace RiemannResearch.RH.PhysicalCarryGram
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.LinearAlgebra.CarryGramCongruence
open FiniteAtomCarryCRT

section Families

variable {I H : Type*} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def columns (v : I → H) (T : Matrix I I ℝ) (j : I) : H :=
  ∑ i, T i j • v i

def gramMatrix (v : I → H) : Matrix I I ℝ := fun i j => inner ℝ (v i) (v j)

def observations (v : I → H) (x : H) : Matrix I Unit ℝ := fun i _ => inner ℝ (v i) x

theorem observations_columns (v : I → H) (T : Matrix I I ℝ) (x : H) :
    observations (columns v T) x = Tᵀ * observations v x := by
  ext i u
  simp only [observations, columns, sum_inner, real_inner_smul_left,
    Matrix.mul_apply, Matrix.transpose_apply]

theorem gramMatrix_columns (v : I → H) (T : Matrix I I ℝ) :
    gramMatrix (columns v T) = Tᵀ * gramMatrix v * T := by
  ext i j
  simp only [gramMatrix, columns, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Every single feasible vector is preserved by an involutory change. -/
theorem observed_iff [DecidableEq I] (v : I → H) (T : Matrix I I ℝ)
    (hT : T * T = 1) (b : Matrix I Unit ℝ) (x : H) :
    (∀ i, inner ℝ (columns v T i) x = (Tᵀ * b) i ()) ↔
      ∀ i, inner ℝ (v i) x = b i () := by
  have ht : Tᵀ * Tᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hT
  have he (a : I → H) (m : Matrix I Unit ℝ) :
      (∀ i, inner ℝ (a i) x = m i ()) ↔ observations a x = m := by
    constructor
    · intro h
      ext i u
      cases u
      exact h i
    · intro h i
      exact congrFun (congrFun h i) ()
  rw [he, he, observations_columns]
  constructor
  · intro h
    have hh := congrArg (fun A : Matrix I Unit ℝ => Tᵀ * A) h
    simpa only [← Matrix.mul_assoc, ht, Matrix.one_mul] using hh
  · intro h
    rw [h]

theorem gram_feasible_columns_iff [DecidableEq I] (v : I → H) (T : Matrix I I ℝ)
    (hT : T * T = 1) (b : Matrix I Unit ℝ) :
    (∃ c, gram (columns v T) c = fun i => (Tᵀ * b) i ()) ↔
      ∃ c, gram v c = fun i => b i () := by
  rw [← finite_feasible_iff_gram_range, ← finite_feasible_iff_gram_range]
  exact exists_congr (observed_iff v T hT b)

/-- Extended minimum energy, including the value at every infeasible datum. -/
theorem minimum_energy_columns [DecidableEq I] (v : I → H) (T : Matrix I I ℝ)
    (hT : T * T = 1) (b : Matrix I Unit ℝ) :
    finiteConstraintEnergy (columns v T) (fun i => (Tᵀ * b) i ()) =
      finiteConstraintEnergy v (fun i => b i ()) := by
  unfold finiteConstraintEnergy
  apply iInf_congr
  intro x
  rw [propext (observed_iff v T hT b x)]

/-- The Hilbert-space minimizer itself survives an oblique coefficient
change, including when the coefficient Gram is singular. -/
theorem minimum_vector_columns [DecidableEq I] (v : I → H) (T : Matrix I I ℝ)
    (hT : T * T = 1) (b : Matrix I Unit ℝ) (hb : ∃ c, gram v c = fun i => b i ()) :
    gramMinimumVector (columns v T) (fun i => (Tᵀ * b) i ()) =
      gramMinimumVector v (fun i => b i ()) := by
  let a := columns v T
  let s := fun i => (Tᵀ * b) i ()
  let t := fun i => b i ()
  have hs : ∃ c, gram a c = s := (gram_feasible_columns_iff v T hT b).2 hb
  have hx := (observed_iff v T hT b _).1 (gramMinimumVector_observation a s hs)
  have hy := (observed_iff v T hT b _).2 (gramMinimumVector_observation v t hb)
  apply (gramMinimumVector_unique v t hb _ hx).1
  have h₁ := gramMinimumVector_completion v t hb _ hx
  have h₂ := gramMinimumVector_completion a s hs _ hy
  change ‖gramMinimumVector a s‖ ^ 2 = ‖gramMinimumVector v t‖ ^ 2
  nlinarith [sq_nonneg ‖gramMinimumVector a s - gramMinimumVector v t‖,
    sq_nonneg ‖gramMinimumVector v t - gramMinimumVector a s‖]

end Families

abbrev StageIndex (L : ℕ) := PrimeIndex L ⊕ MixedIndex L

def conductor {L : ℕ} : StageIndex L → ℕ := Sum.elim Subtype.val Subtype.val

theorem conductor_pos {L : ℕ} (i : StageIndex L) : 0 < conductor i := by
  cases i with
  | inl p => exact lt_trans Nat.zero_lt_one (Finset.mem_filter.mp p.property).2.1
  | inr d => exact lt_trans Nat.zero_lt_one (Finset.mem_filter.mp d.property).2.1

def stageChange (L : ℕ) : Matrix (StageIndex L) (StageIndex L) ℝ :=
  change (fun i j => rowCoefficients L j i)

theorem stageChange_involution (L : ℕ) : stageChange L * stageChange L = 1 :=
  change_mul_self _

def pAtoms (L : ℕ) (i : StageIndex L) : Pareto.ThresholdHilbert :=
  Pareto.normalizedResidueHilbert (conductor i) (conductor_pos i)

def qAtoms (L : ℕ) (i : StageIndex L) : ZetaTwoHilbert.QHilbert :=
  ZetaTwoHilbert.qResidue (conductor i)

/-- Acting on physical vectors, an old prime-power column is fixed. -/
theorem stage_columns_prime {L : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : StageIndex L → H) (i : PrimeIndex L) :
    columns v (stageChange L) (.inl i) = v (.inl i) := by
  classical
  rw [columns, Fintype.sum_sum_type]
  change (∑ p : PrimeIndex L, (1 : Matrix (PrimeIndex L) (PrimeIndex L) ℝ) p i •
    v (.inl p)) + (∑ d : MixedIndex L, (0 : ℝ) • v (.inr d)) = _
  simp [Matrix.one_apply, ite_smul]

/-- On a mixed column, the same arithmetic row subtracts the old mixed atom. -/
theorem stage_columns_mixed {L : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : StageIndex L → H) (j : MixedIndex L) :
    columns v (stageChange L) (.inr j) =
      (∑ i, rowCoefficients L j i • v (.inl i)) - v (.inr j) := by
  classical
  rw [columns, Fintype.sum_sum_type]
  change (∑ i : PrimeIndex L, rowCoefficients L j i • v (.inl i)) +
    (∑ d : MixedIndex L, -((1 : Matrix (MixedIndex L) (MixedIndex L) ℝ) d j) •
      v (.inr d)) = _
  simp [Matrix.one_apply, ite_smul, sub_eq_add_neg]

private theorem mixed_column_sequence {L : ℕ} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : StageIndex L → H) (seq : H →ₗ[ℝ] (ℕ → ℝ))
    (hv : ∀ i, seq (v i) = ArithmeticCumulative.residueFraction (conductor i))
    (j : MixedIndex L) :
    seq (columns v (stageChange L) (.inr j)) = carryVector L j := by
  rw [stage_columns_mixed, map_sub, map_sum, carry_eq_row_sub_atom,
    Fintype.linearCombination_apply]
  simp only [map_smul, hv]
  rfl

theorem p_mixed_column_sequence (L : ℕ) (j : MixedIndex L) :
    Pareto.hilbertSequence (columns (pAtoms L) (stageChange L) (.inr j)) =
      carryVector L j :=
  mixed_column_sequence (pAtoms L) Pareto.hilbertSequenceLinear
    (fun i => Pareto.normalizedResidueHilbert_sequence (conductor i) (conductor_pos i)) j

theorem q_mixed_column_sequence (L : ℕ) (j : MixedIndex L) :
    ZetaTwoHilbert.qSequence (columns (qAtoms L) (stageChange L) (.inr j)) =
      carryVector L j :=
  mixed_column_sequence (qAtoms L) ZetaTwoHilbert.qSequenceLinear
    (fun i => ZetaTwoHilbert.qSequence_qResidue (conductor i)) j

/-- The two Gram matrices and target columns are transported separately in
their physical inner products, with the same arithmetic coordinate matrix. -/
theorem physical_gram_and_targets (L : ℕ) (x : Pareto.ThresholdHilbert)
    (y : ZetaTwoHilbert.QHilbert) :
    let T := stageChange L
    gramMatrix (columns (pAtoms L) T) = Tᵀ * gramMatrix (pAtoms L) * T ∧
    observations (columns (pAtoms L) T) x = Tᵀ * observations (pAtoms L) x ∧
    gramMatrix (columns (qAtoms L) T) = Tᵀ * gramMatrix (qAtoms L) * T ∧
    observations (columns (qAtoms L) T) y = Tᵀ * observations (qAtoms L) y :=
  ⟨gramMatrix_columns _ _, observations_columns _ _ _, gramMatrix_columns _ _,
    observations_columns _ _ _⟩

theorem stage_inverse_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : ℕ) (v : StageIndex L → H) (hg : IsUnit (gramMatrix v).det)
    (b : Matrix (StageIndex L) Unit ℝ) :
    let T := stageChange L
    (Tᵀ * b)ᵀ * (gramMatrix (columns v T))⁻¹ * (Tᵀ * b) =
      bᵀ * (gramMatrix v)⁻¹ * b := by
  dsimp only
  rw [gramMatrix_columns]
  exact target_energy_invariant _ _ hg _

open Pareto ZetaTwoHilbert ArithmeticCumulative QRamanujanPackets

/-- Splitting the P measure into uniform counting and its actual weight
defect gives the complete normalized residue Gram entry. -/
theorem p_atom_gram_uniform_defect (a b L : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (haL : a ∣ L) (hbL : b ∣ L) :
    inner ℝ (normalizedResidueHilbert a ha) (normalizedResidueHilbert b hb) =
      ((1 / (L : ℝ)) * (∑ r : Fin L, Pareto.residue a (r.val+1) * Pareto.residue b (r.val+1)) +
        ∑ r : Fin L, ExactHeadCRT.uniformDefect L (r.val+1) *
          (Pareto.residue a (r.val+1) * Pareto.residue b (r.val+1))) / ((a : ℝ) * (b : ℝ)) := by
  rw [normalizedResidueHilbert_inner, ExactHeadCRT.mixed_uniform_defect L hL _ _
    (fun k => residue_abs_le a k ha) (fun k => residue_abs_le b k hb)
    (residue_period_of_dvd haL) (residue_period_of_dvd hbL)]

/-- The exact P packet entry in unanchored Green coordinates, displaying
both the finite-end boundary product and the infinite physical tail. -/
theorem p_packet_gram_green_boundary_tail (N q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert r) =
      (∑ m ∈ Finset.Ico 1 (N+1), ∑ n ∈ Finset.Ico 1 (N+1),
        ramanujanSum q m * ramanujanSum r n * (1 / (max m n : ℕ))) -
      ramanujanPacket q N * ramanujanPacket r N / ((N : ℝ)+1) +
      ∑' k, positiveWeight (k+(N+1)) *
        (ramanujanPacket q (k+(N+1)) * ramanujanPacket r (k+(N+1))) := by
  rw [hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert,
    hilbertSequence_ramanujanPacketHilbert, ramanujanPacket_green_gram_with_tail N q r hq hr,
    green_gram_boundary_of_prefix N _ _ _ _ (ramanujanPacket_prefix q N hq)
      (ramanujanPacket_prefix r N hr)]

theorem q_packet_gram_weighted (q r : ℕ) :
    inner ℝ (qRamanujanPacket q) (qRamanujanPacket r) =
      ∑' k, positiveQWeight k * ramanujanPacket q k * ramanujanPacket r k := by
  rw [qInner_weighted, qSequence_qRamanujanPacket, qSequence_qRamanujanPacket]

/-- Complete finite evaluation of the Q packet Gram at any common period. -/
theorem q_packet_gram_trigamma (q r L : ℕ) (hL : 0 < L) (hq : q ∣ L) (hr : r ∣ L) :
    inner ℝ (qRamanujanPacket q) (qRamanujanPacket r) =
      ∑ a : Fin L, CRTBlock.trigamma (((a.val+1 : ℕ) : ℝ) / L) /
        (ZetaTwoProbability.zetaTwo * (L : ℝ)^2) *
        (ramanujanPacket q (a.val+1) * ramanujanPacket r (a.val+1)) := by
  rw [qInner_eq_inversePowerMean, qSequence_qRamanujanPacket, qSequence_qRamanujanPacket]
  apply inversePowerMean_zero_eq_trigamma L hL
  · exact bounded_product (ramanujanPacket_abs_le q) (ramanujanPacket_abs_le r)
  · intro k
    rw [ramanujanPacket_period_of_dvd q L hq, ramanujanPacket_period_of_dvd r L hr]

theorem q_atom_gram_weighted (L : ℕ) (i j : StageIndex L) :
    gramMatrix (qAtoms L) i j = ∑' k, positiveQWeight k *
      residueFraction (conductor i) k * residueFraction (conductor j) k := by
  simp only [gramMatrix, qAtoms, qInner_weighted, qSequence_qResidue]

end RiemannResearch.RH.PhysicalCarryGram

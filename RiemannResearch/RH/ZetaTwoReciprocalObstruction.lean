import RiemannResearch.RH.ZetaTwoConductorFour
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.Linarith

/-!
# Permanent reciprocal compression obstruction for squarefree stages

Source: independently developed paper continuation of the user-directed exact
optimizer program, 9 October 2026. The four-site arithmetic comes from
ZetaTwoConductorFour; every application here uses the actual QHilbert and
actual stage definitions. The signed pairing and complete projection remain
in the statements. A universal cap cannot vanish; target-specific arithmetic
cancellation is still needed for RH.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ZetaTwoReciprocalObstruction
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open RiemannResearch.Analysis.ExhaustiveWalk

private theorem witness_square_summable :
    Summable (fun k => positiveQWeight k *
      (ZetaTwoConductorFour.natWitness k)^2) := by
  apply (ZetaTwoConductorFour.fullPair_summable 0 zetaTwo
    ZetaTwoConductorFour.natWitness).congr
  intro k
  simp only [Nat.zero_add]
  unfold positiveQWeight
  ring

/-- Literal four-site dual in the actual inverse-square Hilbert space. -/
def fourWitness : QHilbert :=
  encodeQ ZetaTwoConductorFour.natWitness witness_square_summable

theorem fourWitness_sequence :
    qSequence fourWitness = ZetaTwoConductorFour.natWitness := by
  exact qSequence_encodeQ _ _ (by norm_num [ZetaTwoConductorFour.natWitness])

theorem inner_fourWitness (x : QHilbert) :
    inner ℝ fourWitness x =
      ZetaTwoConductorFour.fullPair 0 zetaTwo (qSequence x) := by
  rw [qInner_weighted, fourWitness_sequence]
  unfold ZetaTwoConductorFour.fullPair
  congr 1
  funext k
  unfold positiveQWeight
  ring

theorem fourWitness_norm_sq : ‖fourWitness‖^2 = 30 / zetaTwo := by
  rw [← real_inner_self_eq_norm_sq, inner_fourWitness, fourWitness_sequence]
  exact ZetaTwoConductorFour.fullPair_norm zetaTwo

theorem fourWitness_reciprocal_energy :
    inner ℝ fourWitness (reciprocalD fourWitness) = 10 / zetaTwo := by
  rw [inner_fourWitness]
  have he : ZetaTwoConductorFour.fullPair 0 zetaTwo
      (qSequence (reciprocalD fourWitness)) =
      ZetaTwoConductorFour.fullPair 1 zetaTwo ZetaTwoConductorFour.natWitness := by
    unfold ZetaTwoConductorFour.fullPair
    congr 1
    funext k
    rw [qSequence_reciprocalD, fourWitness_sequence]
    by_cases hk : k = 0
    · simp [hk]
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp [hkR, ne_of_gt zetaTwo_pos]
      ring
  rw [he]
  exact ZetaTwoConductorFour.fullPair_reciprocal_energy zetaTwo

theorem fourWitness_inner_qOne : inner ℝ fourWitness qOne = 0 := by
  rw [inner_fourWitness, qSequence_qOne,
    ZetaTwoConductorFour.fullPair_eq_rawInner]
  norm_num [ZetaTwoConductorFour.rawInner, ZetaTwoConductorFour.witness,
    qOneSequence, Fin.sum_univ_succ]

theorem fourWitness_inner_squarefreeAtom (i : ℕ) :
    inner ℝ fourWitness (squarefreeAtom i) = 0 := by
  unfold squarefreeAtom
  split_ifs with hs
  · rw [inner_fourWitness, qSequence_qResidue]
    apply ZetaTwoConductorFour.fullPair_atom_annihilates
      (i + 2) (by omega) _ zetaTwo
    intro h
    rw [h] at hs
    exact (by decide : ¬ Squarefree 4) hs
  · simp

theorem fourWitness_mem_stage_orthogonal (n : ℕ) :
    fourWitness ∈ (stage n)ᗮ := by
  apply ((stage n).mem_orthogonal _).mpr
  intro x hx
  rw [real_inner_comm]
  change x ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => squarefreeAtom (id i))) at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact fourWitness_inner_squarefreeAtom i
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul c x hx ih => simp [inner_smul_right, ih]

/-- Every all-direction first-moment cap is bounded away from zero.
The witness is legal in the orthogonal complement at every integer stage. -/
theorem universal_firstMoment_cap_ge_third (n : ℕ) (τ : ℝ)
    (hcap : ∀ x : QHilbert, x ∈ (stage n)ᗮ →
      inner ℝ x (reciprocalD x) ≤ τ * ‖x‖ ^ 2) :
    (1 / 3 : ℝ) ≤ τ := by
  have h := hcap fourWitness (fourWitness_mem_stage_orthogonal n)
  rw [fourWitness_reciprocal_energy, fourWitness_norm_sq,
    ← mul_div_assoc] at h
  have hs := (div_le_div_iff_of_pos_right zetaTwo_pos).mp h
  linarith

theorem no_vanishing_universal_firstMoment_caps (τ : ℕ → ℝ)
    (hcap : ∀ n x, x ∈ (stage n)ᗮ →
      inner ℝ x (reciprocalD x) ≤ τ n * ‖x‖ ^ 2) :
    ¬ Tendsto τ atTop (𝓝 0) := by
  intro ht
  have hle : (1 / 3 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall
      (fun n => universal_firstMoment_cap_ge_third n (τ n) (hcap n)))
  norm_num at hle

/-- The full reciprocal projection retains the witness's exact signed pairing. -/
theorem fourWitness_inner_compressed (n : ℕ) (x : QHilbert) :
    inner ℝ fourWitness
      (reciprocalD x - (stage n).starProjection (reciprocalD x)) =
      inner ℝ fourWitness (reciprocalD x) := by
  have hp : inner ℝ fourWitness
      ((stage n).starProjection (reciprocalD x)) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp
      (fourWitness_mem_stage_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  rw [inner_sub_right, hp, sub_zero]

theorem fourWitness_inner_residual (n : ℕ) :
    inner ℝ fourWitness (residual n) = 0 := by
  have hp : inner ℝ fourWitness (optimizer n) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp
      (fourWitness_mem_stage_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  rw [ZetaTwoOptimizerStage.residual, inner_sub_right, fourWitness_inner_qOne, hp, sub_zero]

theorem compressed_fourWitness_norm_sq_ge (n : ℕ) :
    ‖fourWitness‖^2 / 9 ≤
      ‖reciprocalD fourWitness -
        (stage n).starProjection (reciprocalD fourWitness)‖ ^ 2 := by
  let s := reciprocalD fourWitness -
    (stage n).starProjection (reciprocalD fourWitness)
  have hi : inner ℝ fourWitness s = ‖fourWitness‖^2 / 3 := by
    rw [fourWitness_inner_compressed, fourWitness_reciprocal_energy,
      fourWitness_norm_sq]
    ring
  have hc := abs_real_inner_le_norm fourWitness s
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg fourWitness) (norm_nonneg s))).mpr hc
  rw [sq_abs, mul_pow, hi] at hsq
  have hpos : 0 < ‖fourWitness‖^2 := by
    rw [fourWitness_norm_sq]
    exact div_pos (by norm_num) zetaTwo_pos
  have hmul : ‖fourWitness‖^2 * (‖fourWitness‖^2 / 9) ≤
      ‖fourWitness‖^2 * ‖s‖^2 := by nlinarith [hsq]
  by_contra hn
  have hlt : ‖s‖^2 < ‖fourWitness‖^2 / 9 := lt_of_not_ge hn
  have hproduct := mul_pos hpos (sub_pos.mpr hlt)
  nlinarith [hproduct]

/-- No all-direction compressed-square certificate can tend to zero. -/
theorem universal_secondMoment_cap_ge_ninth (n : ℕ) (τ : ℝ)
    (hcap : ∀ x : QHilbert, x ∈ (stage n)ᗮ →
      ‖reciprocalD x - (stage n).starProjection (reciprocalD x)‖ ^ 2 ≤
        τ * ‖x‖ ^ 2) : (1 / 9 : ℝ) ≤ τ := by
  have h := (compressed_fourWitness_norm_sq_ge n).trans
    (hcap fourWitness (fourWitness_mem_stage_orthogonal n))
  have hp : 0 < ‖fourWitness‖^2 := by
    rw [fourWitness_norm_sq]
    exact div_pos (by norm_num) zetaTwo_pos
  have hm : (1 / 9 : ℝ) * ‖fourWitness‖^2 ≤ τ * ‖fourWitness‖^2 := by
    nlinarith [h]
  by_contra hn
  have hlt : τ < (1 / 9 : ℝ) := lt_of_not_ge hn
  have hproduct := mul_pos hp (sub_pos.mpr hlt)
  nlinarith [hproduct]

theorem no_vanishing_universal_secondMoment_caps (τ : ℕ → ℝ)
    (hcap : ∀ n x, x ∈ (stage n)ᗮ →
      ‖reciprocalD x - (stage n).starProjection (reciprocalD x)‖ ^ 2 ≤
        τ n * ‖x‖ ^ 2) : ¬ Tendsto τ atTop (𝓝 0) := by
  intro ht
  have hle : (1 / 9 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall
      (fun n => universal_secondMoment_cap_ge_ninth n (τ n) (hcap n)))
  norm_num at hle

/-- The actual residual is orthogonal to the dual, but its reciprocal image
has a complete signed row that the screened second moment must control. -/
theorem residual_reciprocal_row_sq_le (n : ℕ) :
    (inner ℝ fourWitness (reciprocalD (residual n)))^2 ≤
      (30 / zetaTwo) * ‖screenedResidual n‖^2 := by
  have hi : inner ℝ fourWitness (screenedResidual n) =
      inner ℝ fourWitness (reciprocalD (residual n)) :=
    fourWitness_inner_compressed n (residual n)
  have hc := abs_real_inner_le_norm fourWitness (screenedResidual n)
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg fourWitness) (norm_nonneg (screenedResidual n)))).mpr hc
  simpa only [sq_abs, mul_pow, hi, fourWitness_norm_sq] using hsq

end RiemannResearch.RH.ZetaTwoReciprocalObstruction

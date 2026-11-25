import RiemannResearch.RH.DyadicParityGramRow
import RiemannResearch.RH.RamanujanMultipleCapacityLimits

/-! # A finite inverse Gram certificate for the centered parity source

The energy defect of the unit target is controlled at every stage by the
uncaptured squared norm of an explicit different source. Its norm is known
exactly. Each certificate is the difference between this constant and one
positive quadratic form in the ordinary inverse packet Gram matrix.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization PacketGramBoundary MixedConductorBasis RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open scoped LegalMeanAlgebra

/-- The correction adds one fifteenth of the first physical site. -/
def centeredParitySource : ThresholdHilbert := parityAdjointPacket + (1/15 : ℝ) • paretoPointHilbert 0

theorem centeredParitySource_norm_sq :
    ‖centeredParitySource‖^2 = 2*Real.log 2-Real.pi^2/8+11/450 := by
  have h1 : inner ℝ parityAdjointPacket (paretoPointHilbert 0) = 1/6 := by
    rw [paretoPoint_zero_inner,parityAdjointPacket_coordinate]
    norm_num
  rw [centeredParitySource,norm_add_sq_real,parityAdjointPacket_norm_sq,
    real_inner_smul_right,h1,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/15),
    mul_pow,paretoPoint_zero_norm_sq]
  ring

/-- Cross-Gram source for the finite least squares approximation to centered parity. -/
def centeredParityGramRow (n : ℕ) (i : Fin n) : ℝ :=
  adjointParityGramRow n i-finiteMoebiusSource n i/30

theorem centeredParityGramRow_eq (n : ℕ) :
    centeredParityGramRow n = cross (fun i : Fin n => ramanujanPacketHilbert (i.val+2)) centeredParitySource := by
  funext i
  rw [centeredParityGramRow,adjointParityGramRow_eq,cross,centeredParitySource,inner_add_right,
    real_inner_smul_right,paretoPoint_zero_inner,hilbertSequence_ramanujanPacketHilbert,
    ramanujanPacket_at_one_moebius _ (by omega),finiteMoebiusSource]
  ring

/-- Complete source capture with all off-diagonal signs retained. -/
def centeredParityGramCapacity (n : ℕ) : ℝ :=
  dotProduct (centeredParityGramRow n) ((finitePacketGram n)⁻¹.mulVec (centeredParityGramRow n))

private theorem projection_eq_of_eq_space {S T : Submodule ℝ ThresholdHilbert}
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] (h : S = T) (y : ThresholdHilbert) :
    S.starProjection y = T.starProjection y := by subst T; rfl

theorem centeredParityGramCapacity_eq (n : ℕ) :
    centeredParityGramCapacity n = ‖(finiteSpace n).starProjection centeredParitySource‖^2 := by
  have h := projection_inner_eq_inverseGram (finitePacket_independent n) centeredParitySource centeredParitySource
  have hs : synthesisSpan (fun i : Fin n => ramanujanPacketHilbert (i.val+2)) = finiteSpace n :=
    finitePacket_span_eq n
  rw [projection_eq_of_eq_space hs,real_inner_self_eq_norm_sq,← centeredParityGramRow_eq] at h
  exact h.symm

theorem centeredParityGram_error (n : ℕ) :
    ‖centeredParitySource-(finiteSpace n).starProjection centeredParitySource‖^2 =
      2*Real.log 2-Real.pi^2/8+11/450 - centeredParityGramCapacity n := by
  let S := finiteSpace n
  let y := centeredParitySource
  have ho := Submodule.inner_right_of_mem_orthogonal (S.starProjection_apply_mem y)
    (Submodule.sub_starProjection_mem_orthogonal (K:=S) y)
  rw [inner_sub_right,real_inner_self_eq_norm_sq,sub_eq_zero] at ho
  have hp : inner ℝ y (S.starProjection y) = ‖S.starProjection y‖^2 := (real_inner_comm ..).trans ho
  change ‖y-S.starProjection y‖^2 = _
  rw [norm_sub_sq_real,hp,← centeredParityGramCapacity_eq,centeredParitySource_norm_sq]
  ring

/-- The centered arithmetic row is the actual residual pairing at stage n. -/
theorem centeredAdjointParityResidual_eq_pair (n : ℕ) :
    centeredAdjointParityResidual n = inner ℝ (hilbertOne-projection n) centeredParitySource := by
  rw [centeredAdjointParityResidual,finiteAdjointParityResidual_eq,firstSiteGramCoordinates_eq,
    centeredParitySource,inner_add_right,real_inner_smul_right,paretoPoint_zero_inner,
    hilbertSequence_sub,hilbertOne_sequence]
  simp only [Pi.sub_apply,zeroAnchor,ite_false,one_ne_zero]
  ring

/-- The finite two-source Schur determinant is an exact squared norm.
All three scalar entries come from the same ordinary packet Gram section. -/
theorem centeredParityGram_finite_remainder (n : ℕ) :
    let e := energy n
    let R := centeredAdjointParityResidual n
    let u := hilbertOne-projection n
    let v := centeredParitySource-(finiteSpace n).starProjection centeredParitySource
    ‖e • v-R • u‖^2 =
      e*(e*(2*Real.log 2-Real.pi^2/8+11/450-centeredParityGramCapacity n)-R^2) := by
  let e := energy n
  let R := centeredAdjointParityResidual n
  let u := hilbertOne-projection n
  let p := (finiteSpace n).starProjection centeredParitySource
  let v := centeredParitySource-p
  have hu : ‖u‖^2 = e := rfl
  have hv : ‖v‖^2 = 2*Real.log 2-Real.pi^2/8+11/450-centeredParityGramCapacity n :=
    centeredParityGram_error n
  have hpu : inner ℝ p u = 0 := Submodule.inner_right_of_mem_orthogonal
    ((finiteSpace n).starProjection_apply_mem centeredParitySource)
    (Submodule.sub_starProjection_mem_orthogonal (K:=finiteSpace n) hilbertOne)
  have hvu : inner ℝ v u = R := by
    dsimp only [v]
    rw [inner_sub_left,hpu,sub_zero,real_inner_comm,← centeredAdjointParityResidual_eq_pair]
  change ‖e • v-R • u‖^2 = _
  rw [norm_sub_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,
    sq_abs,sq_abs,hv,hu,real_inner_smul_left,real_inner_smul_right,hvu]
  change _ = e*(e*(2*Real.log 2-Real.pi^2/8+11/450-centeredParityGramCapacity n)-R^2)
  ring

/-- An individual finite capture bounds the limiting RH defect. -/
theorem limitEnergy_le_centeredParityGram_error (n : ℕ) :
    (2/5-1/(10*Real.sqrt 3))^2*limitEnergy ≤
      2*Real.log 2-Real.pi^2/8+11/450 - centeredParityGramCapacity n := by
  let E := limitEnergy
  let K : ℝ := 2/5-1/(10*Real.sqrt 3)
  let y := centeredParitySource
  let v := (finiteSpace n).starProjection y
  let R := inner ℝ limitResidual (y-v)
  have hK : 0 < K :=
    (by norm_num : (0:ℝ) < 1/3).trans one_third_lt_centeredParityLowerCoefficient
  have hE : 0 ≤ E := sq_nonneg _
  have hv := Submodule.inner_right_of_mem_orthogonal
    (RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace n ((finiteSpace n).starProjection_apply_mem y))
    limitResidual_mem_orthogonal
  have hp : inner ℝ limitResidual v = 0 := (real_inner_comm ..).trans hv
  have hr : R = inner ℝ limitResidual parityAdjointPacket + hilbertSequence limitResidual 1/30 := by
    change inner ℝ limitResidual (centeredParitySource-v) = _
    rw [inner_sub_right,hp,sub_zero,centeredParitySource,inner_add_right,real_inner_smul_right,paretoPoint_zero_inner]
    ring
  have hlo : K*E ≤ R := by
    rw [hr]
    exact centeredAdjointParity_limit_lower
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le limitResidual (y-v)
  change R^2 ≤ E*‖y-v‖^2 at hcs
  have hs := ((sq_le_sq₀ (mul_nonneg hK.le hE) ((mul_nonneg hK.le hE).trans hlo)).mpr hlo).trans hcs
  rw [← centeredParityGram_error]
  change K^2*E ≤ ‖y-v‖^2
  by_cases hz : E = 0
  · rw [hz,mul_zero]; exact sq_nonneg _
  apply le_of_mul_le_mul_left _ (lt_of_le_of_ne hE (Ne.symm hz))
  calc
    E*(K^2*E) = (K*E)^2 := by ring
    _ ≤ _ := hs

/-- The centered unit vanishes exactly when the finite capacities approach
the known full source norm arbitrarily closely. -/
theorem stageUnit_zero_iff_centeredParityGram_capacity (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      2*Real.log 2-Real.pi^2/8+11/450 ≤ centeredParityGramCapacity n+ε := by
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_one_mem, ← limitEnergy_zero_iff_mem]
  constructor
  · intro h ε hε
    have hy : centeredParitySource ∈ closedSpace := by
      rw [closedSpace_eq_top_iff_one_mem.mpr (limitEnergy_zero_iff_mem.mp h)]
      trivial
    have ht := walkProjection_tendsto residueAtom id Function.surjective_id centeredParitySource
    change Tendsto (fun n => (finiteSpace n).starProjection centeredParitySource) atTop
      (𝓝 (closedSpace.starProjection centeredParitySource)) at ht
    rw [Submodule.starProjection_eq_self_iff.mpr hy] at ht
    have hz := ((tendsto_const_nhds (x:=centeredParitySource)).sub ht).norm.pow 2
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hz
    obtain ⟨n,hn⟩ := (hz.eventually_lt_const hε).exists
    change ‖centeredParitySource-(finiteSpace n).starProjection centeredParitySource‖^2 < ε at hn
    rw [centeredParityGram_error] at hn
    exact ⟨n,by linarith only [hn]⟩
  · intro h
    have hk := (by norm_num : (0:ℝ) < 1/3).trans one_third_lt_centeredParityLowerCoefficient
    by_contra he
    have hp : 0 < (2/5-1/(10*Real.sqrt 3))^2*limitEnergy :=
      mul_pos (sq_pos_of_pos hk) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm he))
    obtain ⟨n,hn⟩ := h _ (half_pos hp)
    linarith only [hn,limitEnergy_le_centeredParityGram_error n,hp]

/-- Arbitrary approximation of the exact centered source norm by these
ordinary inverse Gram capacities implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_centeredParityGram_capacity
    (h : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      2*Real.log 2-Real.pi^2/8+11/450 ≤ centeredParityGramCapacity n+ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_stageUnit_zero ((stageUnit_zero_iff_centeredParityGram_capacity 0).2 h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

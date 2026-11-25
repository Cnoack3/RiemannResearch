import RiemannResearch.RH.CenteredMeanParityGramSix

/-! # A signed parity observation of the genuine two-stage Gram remainder

The upper residual is orthogonal to doubled lower-stage legal vectors. This
allows an exact finite pairing against parity off the first site, without
substituting a limiting identity for the finite dyadic correlation.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization RiemannResearch.Analysis.ExhaustiveWalk

private theorem parity_first_site_value :
    hilbertSequence (ramanujanPacketHilbert 2) 1 = 1 := by
  rw [hilbertSequence_ramanujanPacketHilbert,ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
  norm_num [residue]

private theorem parity_mem_finite {n : ℕ} (hn : 1 ≤ n) : ramanujanPacketHilbert 2 ∈ finiteSpace n := by
  let i : Fin n := ⟨0,by omega⟩
  have h : ramanujanPacketHilbert (i.val+2) ∈
      Submodule.span ℝ (Set.range (fun j : Fin n => ramanujanPacketHilbert (j.val+2))) :=
    Submodule.subset_span (Set.mem_range_self i)
  rw [finitePacket_span_eq] at h
  exact h

theorem endpointGramRemainder_inner_double_lower {k n : ℕ} (hn : doubleStage k ≤ n)
    {v : ThresholdHilbert} (hv : v ∈ finiteSpace k) :
    inner ℝ (endpointGramRemainder k n) (doubleDilation v) = 0 := by
  have hlo := projectionResidual_inner_mem k v hv
  have hhi := projectionResidual_inner_mem n _ (walkSpan_mono residueAtom id hn (doubleDilation_mem_double hv))
  have hp : inner ℝ (paretoPointHilbert 0) (doubleDilation v) = 0 :=
    (real_inner_comm ..).trans (doubleDilation_inner_firstPoint v)
  rw [endpointGramRemainder,inner_sub_left,real_inner_smul_left,real_inner_smul_left,
    inner_sub_left,real_inner_smul_left,hhi,hp,doubleDilation_inner,hlo]
  ring

/-- The parity observation is signed and uses the lower adjoint coordinate
with the upper first site. -/
theorem endpointGramRemainder_inner_parity (k n : ℕ) (hn : doubleStage k ≤ n) :
    let K := (firstSiteGramCoordinates k).1
    let e := (firstSiteGramCoordinates n).1
    let b := (firstSiteGramCoordinates n).2
    let B := finiteAdjointParityResidual k
    inner ℝ (endpointGramRemainder k n) (ramanujanPacketHilbert 2-paretoPointHilbert 0) =
      -(K*b+(2*e-b)*B) := by
  let r := projectionResidual n
  let b := hilbertSequence r 1
  let p := paretoPointHilbert 0
  let q := ramanujanPacketHilbert 2
  have hpar : q ∈ finiteSpace n := parity_mem_finite (by dsimp [doubleStage] at hn; omega)
  have hrq : inner ℝ r q = 0 := projectionResidual_inner_mem n q hpar
  have hpq : inner ℝ p q = 1/2 := by
    rw [real_inner_comm,paretoPoint_zero_inner,parity_first_site_value,mul_one]
  have hpp : inner ℝ p p = 1/2 := (real_inner_self_eq_norm_sq _).trans paretoPoint_zero_norm_sq
  have hrp : inner ℝ r p = (1/2:ℝ)*b := paretoPoint_zero_inner r
  have hdp : inner ℝ (doubleDilation (projectionResidual k)) p = 0 := doubleDilation_inner_firstPoint _
  have hdq : inner ℝ (doubleDilation (projectionResidual k)) q = finiteAdjointParityResidual k := by
    rw [finiteAdjointParityResidual_eq]
    exact (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
      (projectionResidual k) (ramanujanPacketHilbert 2)).symm
  have hb : (firstSiteGramCoordinates n).2 = b := by
    rw [firstSiteGramCoordinates_eq]
    dsimp only [b,r,projectionResidual]
    rw [hilbertSequence_sub,hilbertOne_sequence]
    norm_num [zeroAnchor]
  rw [hb,firstSiteGramCoordinates_eq k,firstSiteGramCoordinates_eq n]
  change inner ℝ ((2*energy k) • (r-b • p) -
    (2*energy n-b) • doubleDilation (projectionResidual k)) (q-p) = _
  simp only [inner_sub_left,real_inner_smul_left,inner_sub_right,hrq,hrp,hpq,hpp,hdp,hdq]
  ring

/-- Finite two-stage Cauchy--Schwarz with the exact observed signed row. -/
theorem finite_two_stage_parity_gram (k n : ℕ) (hn : doubleStage k ≤ n) :
    let K := (firstSiteGramCoordinates k).1
    let e := (firstSiteGramCoordinates n).1
    let b := (firstSiteGramCoordinates n).2
    let B := finiteAdjointParityResidual k
    (K*b+(2*e-b)*B)^2 ≤ 2*K*(2*K*e-K*b^2-(2*e-b)^2)*(Real.log 2-1/2) := by
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le (endpointGramRemainder k n)
    (ramanujanPacketHilbert 2-paretoPointHilbert 0)
  have hq : ‖ramanujanPacketHilbert 2-paretoPointHilbert 0‖^2 = Real.log 2-1/2 := by
    simpa only [parity_first_site_value,one_smul,one_pow,ramanujanPacketHilbert_two_norm_sq] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  rw [endpointGramRemainder_inner_parity k n hn,neg_sq,finite_endpoint_remainder_norm_sq k n hn,hq] at hcs
  have hb : (firstSiteGramCoordinates n).2 = hilbertSequence (projectionResidual n) 1 := by
    rw [firstSiteGramCoordinates_eq,projectionResidual,hilbertSequence_sub,hilbertOne_sequence]
    norm_num [zeroAnchor]
  have he (j : ℕ) : (firstSiteGramCoordinates j).1 = energy j :=
    congrArg Prod.fst (firstSiteGramCoordinates_eq j)
  dsimp only at hcs ⊢
  simpa only [hb,he] using hcs

/-- Subtracting a doubled lower projection preserves the parity observation
exactly. The norm on the right retains its signed linear correction. -/
theorem two_stage_parity_pencil (k n : ℕ) (hn : doubleStage k ≤ n) (t : ℝ) :
    let K := (firstSiteGramCoordinates k).1
    let e := (firstSiteGramCoordinates n).1
    let b := (firstSiteGramCoordinates n).2
    let B := finiteAdjointParityResidual k
    let L := Real.log 2-1/2
    (K*b+(2*e-b)*B)^2 ≤ 2*K*(2*K*e-K*b^2-(2*e-b)^2) *
      (L-2*t*(2*L-B)+2*t^2*(1-K)) := by
  let q := ramanujanPacketHilbert 2-paretoPointHilbert 0
  let w := doubleDilation (projection k)
  let L := Real.log 2-1/2
  let B := finiteAdjointParityResidual k
  have hq : ‖q‖^2 = L := by
    simpa only [parity_first_site_value,one_smul,one_pow,ramanujanPacketHilbert_two_norm_sq,q,L] using
      remove_firstPoint_norm_sq (ramanujanPacketHilbert 2)
  have hm : ‖projection k‖^2 = 1-energy k := by
    have h := ProjectionSchur.error_eq_one_sub_captured k
    rw [ProjectionSchur.captured_eq_norm_sq] at h
    change energy k = 1-‖projection k‖^2 at h
    linarith
  have hw : ‖w‖^2 = 2*(1-energy k) := by
    rw [← real_inner_self_eq_norm_sq,doubleDilation_inner,real_inner_self_eq_norm_sq,hm]
  have hmean : inner ℝ hilbertOne parityAdjointPacket = 2*L := by
    have h := dyadicMomentProfile_mean
    rw [dyadicMomentProfile,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq,real_inner_comm hilbertOne parityAdjointPacket] at h
    dsimp only [L]; linarith only [h]
  have hqw : inner ℝ q w = 2*L-B := by
    dsimp only [q,w]
    rw [inner_sub_left,(real_inner_comm ..).trans (doubleDilation_inner_firstPoint (projection k)),sub_zero,
      real_inner_comm]
    have hu := (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous 2 (by decide))
      (projection k) (ramanujanPacketHilbert 2)).symm
    change inner ℝ (doubleDilation (projection k)) (ramanujanPacketHilbert 2) =
      inner ℝ (projection k) parityAdjointPacket at hu
    rw [hu]
    have hh := finiteAdjointParityResidual_eq k
    rw [inner_sub_left,hmean] at hh
    dsimp only [B]; linarith only [hh]
  have hnorm : ‖q-t • w‖^2 = L-2*t*(2*L-B)+2*t^2*(1-energy k) := by
    rw [norm_sub_sq_real,hq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hw,real_inner_smul_right,hqw]
    ring
  have hzw : inner ℝ (endpointGramRemainder k n) w = 0 :=
    endpointGramRemainder_inner_double_lower hn ((finiteSpace k).starProjection_apply_mem hilbertOne)
  have hpair := endpointGramRemainder_inner_parity k n hn
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le
    (endpointGramRemainder k n) (q-t • w)
  rw [inner_sub_right,real_inner_smul_right,hzw,mul_zero,sub_zero,hpair,neg_sq,
    finite_endpoint_remainder_norm_sq k n hn,hnorm] at hcs
  have hb : (firstSiteGramCoordinates n).2 = hilbertSequence (projectionResidual n) 1 := by
    rw [firstSiteGramCoordinates_eq,projectionResidual,hilbertSequence_sub,hilbertOne_sequence]
    norm_num [zeroAnchor]
  have he (j : ℕ) : (firstSiteGramCoordinates j).1 = energy j :=
    congrArg Prod.fst (firstSiteGramCoordinates_eq j)
  dsimp only at hcs ⊢
  simpa only [hb,he,L,B] using hcs

/-- The genuine optimized two-stage Gram expression is nonnegative at every
admissible positive lower stage. -/
theorem finite_two_stage_projected_parity_gram (k n : ℕ) (hk : 1 ≤ k) (hn : doubleStage k ≤ n) :
    let K := (firstSiteGramCoordinates k).1
    let e := (firstSiteGramCoordinates n).1
    let b := (firstSiteGramCoordinates n).2
    let B := finiteAdjointParityResidual k
    let L := Real.log 2-1/2
    (1-K)*(K*b+(2*e-b)*B)^2 ≤ K*(2*K*e-K*b^2-(2*e-b)^2) *
      (2*(1-K)*L-(2*L-B)^2) := by
  let K := (firstSiteGramCoordinates k).1
  let e := (firstSiteGramCoordinates n).1
  let b := (firstSiteGramCoordinates n).2
  let B := finiteAdjointParityResidual k
  let L := Real.log 2-1/2
  let G := 2*K*e-K*b^2-(2*e-b)^2
  let t := (2*L-B)/(2*(1-K))
  have hK : 0 < 1-K := by
    dsimp only [K]; rw [firstSiteGramCoordinates_eq]
    have hmono := energy_antitone hk
    rw [ProjectionSchur.energy_one] at hmono
    linarith only [hmono,Real.log_pos (by norm_num : (1:ℝ)<2)]
  have h := two_stage_parity_pencil k n hn t
  change (K*b+(2*e-b)*B)^2 ≤ 2*K*G*(L-2*t*(2*L-B)+2*t^2*(1-K)) at h
  have heq : 2*(1-K)*(L-2*t*(2*L-B)+2*t^2*(1-K)) = 2*(1-K)*L-(2*L-B)^2 := by
    dsimp only [t]
    field_simp [hK.ne'] <;> ring
  change (1-K)*(K*b+(2*e-b)*B)^2 ≤ K*G*(2*(1-K)*L-(2*L-B)^2)
  apply (mul_le_mul_of_nonneg_left h hK.le).trans_eq
  calc
    _ = K*G*(2*(1-K)*(L-2*t*(2*L-B)+2*t^2*(1-K))) := by ring
    _ = _ := by rw [heq]

/-- The limiting polynomial uses one energy, while the finite Hilbert
determinant retains the upper and lower energies separately. -/
def twoStageParityGramDefect (k n : ℕ) : ℝ :=
  let K := (firstSiteGramCoordinates k).1
  let e := (firstSiteGramCoordinates n).1
  let b := (firstSiteGramCoordinates n).2
  let B := finiteAdjointParityResidual k
  let L := Real.log 2-1/2
  K*(2*K*e-K*b^2-(2*e-b)^2)*(2*(1-K)*L-(2*L-B)^2) - (1-K)*(K*b+(2*e-b)*B)^2

theorem twoStageParityGramDefect_nonneg (k n : ℕ) (hk : 1 ≤ k) (hn : doubleStage k ≤ n) :
    0 ≤ twoStageParityGramDefect k n :=
  sub_nonneg.mpr (finite_two_stage_projected_parity_gram k n hk hn)

open Filter
open scoped Topology LegalMeanAlgebra
open MixedConductorBasis

theorem twoStageParityGramDefect_tendsto :
    Tendsto (fun k => twoStageParityGramDefect k (doubleStage k)) atTop
      (𝓝 (projectedParityGramDefect limitEnergy (hilbertSequence limitResidual 1)
        (inner ℝ limitResidual parityAdjointPacket))) := by
  let F (p : (ℝ × ℝ) × (ℝ × ℝ) × ℝ) :=
    let K := p.1.1
    let e := p.2.1.1
    let b := p.2.1.2
    let B := p.2.2
    let L := Real.log 2-1/2
    K*(2*K*e-K*b^2-(2*e-b)^2)*(2*(1-K)*L-(2*L-B)^2) - (1-K)*(K*b+(2*e-b)*B)^2
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hd : Tendsto doubleStage atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro N
    exact ⟨N,fun k hk => by dsimp [doubleStage]; omega⟩
  let p := (limitEnergy,hilbertSequence limitResidual 1)
  let B := inner ℝ limitResidual parityAdjointPacket
  have hf : F (p,p,B) = projectedParityGramDefect p.1 p.2 B := by
    dsimp only [F,projectedParityGramDefect,firstSiteGramGap]; ring
  have ht := (hc.tendsto _).comp (firstSiteGramCoordinates_tendsto.prodMk_nhds
    ((firstSiteGramCoordinates_tendsto.comp hd).prodMk_nhds finiteAdjointParityResidual_tendsto))
  rw [hf] at ht
  exact ht

/-- Vanishing of the centered unit is equivalent to arbitrarily small
cofinal values of genuine nonnegative two-stage determinants. -/
theorem stageUnit_zero_iff_cofinal_two_stage_parity_gram (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ k ≥ N,
      twoStageParityGramDefect k (doubleStage k) ≤ ε := by
  rw [stageUnit_zero_iff_boundary,boundary_eq_zero_iff_one_mem,← limitEnergy_zero_iff_mem]
  have ht := twoStageParityGramDefect_tendsto
  constructor
  · intro he
    have hb := firstCoordinate_zero_iff_residual_zero.mpr (limitResidual_zero_iff_energy_zero.mpr he)
    have hlim : projectedParityGramDefect limitEnergy (hilbertSequence limitResidual 1)
        (inner ℝ limitResidual parityAdjointPacket) = 0 := by
      rw [hb,he,limitResidual_zero_iff_energy_zero.mpr he]
      simp [projectedParityGramDefect,firstSiteGramGap]
    rw [hlim] at ht
    simpa only [zero_add] using RiemannResearch.Analysis.cofinal_le_add_of_tendsto ht
  · intro h
    have hle := RiemannResearch.Analysis.limit_le_of_cofinal_le_add (L:=0) ht
      (by simpa only [zero_add] using h)
    by_contra he
    exact (not_le_of_gt (limit_projectedParityGramDefect_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)))) hle

theorem riemannHypothesis_of_cofinal_two_stage_parity_gram
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ k ≥ N,
      twoStageParityGramDefect k (doubleStage k) ≤ ε) : RiemannHypothesis :=
  riemannHypothesis_of_stageUnit_zero ((stageUnit_zero_iff_cofinal_two_stage_parity_gram 0).2 h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

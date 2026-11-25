import RiemannResearch.RH.CenteredMeanDyadicGram

/-! # Observing the physical dyadic parity adjoint from one packet Gram solve

Doubling a packet retains its conductor exactly when that conductor is odd.
The finite parity-adjoint residual is therefore obtained from two columns
of ordinary Gram entries and the same inverse Gram vector as the energy.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary MixedConductorBasis

/-- Pair the doubled packet with parity in the ordinary larger Gram section. -/
def adjointParityGramRow (n : ℕ) (i : Fin n) : ℝ :=
  let j : Fin (2*n+2) := ⟨2*i.val+2, by omega⟩
  let k : Fin (2*n+2) := ⟨i.val, by omega⟩
  let z : Fin (2*n+2) := ⟨0, by omega⟩
  finitePacketGram (2*n+2) j z +
    if 2 ∣ i.val + 2 then 0 else finitePacketGram (2*n+2) k z

theorem adjointParityGramRow_eq (n : ℕ) (i : Fin n) :
    adjointParityGramRow n i = inner ℝ (ramanujanPacketHilbert (i.val+2)) parityAdjointPacket := by
  let q := i.val+2
  have hq : 1 < q := by dsimp [q]; omega
  change inner ℝ (ramanujanPacketHilbert (2*i.val+2+2)) (ramanujanPacketHilbert 2) +
    (if 2 ∣ q then 0 else inner ℝ (ramanujanPacketHilbert q) (ramanujanPacketHilbert 2)) =
    inner ℝ (ramanujanPacketHilbert q) ((hilbertDilationContinuous 2 (by decide)).adjoint
      (ramanujanPacketHilbert 2))
  rw [show 2*i.val+2+2 = 2*q by dsimp [q]; omega, ContinuousLinearMap.adjoint_inner_right,
    hilbertDilationContinuous_apply]
  by_cases hd : 2 ∣ q
  · have he : ramanujanPacketHilbert (2*q) = hilbertDilation 2 (by decide) (ramanujanPacketHilbert q) := by
      apply hilbertSequence_injective
      rw [hilbertDilation_sequence,hilbertSequence_ramanujanPacketHilbert,hilbertSequence_ramanujanPacketHilbert]
      funext k
      exact ramanujanPacket_mul_prime_of_dvd 2 q k Nat.prime_two hq hd
    rw [if_pos hd,add_zero,he]
  · have he : ramanujanPacketHilbert (2*q) =
        hilbertDilation 2 (by decide) (ramanujanPacketHilbert q) - ramanujanPacketHilbert q := by
      apply hilbertSequence_injective
      rw [hilbertSequence_sub,hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert,
        hilbertSequence_ramanujanPacketHilbert]
      funext k
      exact ramanujanPacket_mul_prime_of_not_dvd 2 q k Nat.prime_two hq hd
    rw [if_neg hd,he,inner_sub_left,sub_add_cancel]

/-- The signed third observable uses the same coefficients as the energy and
the physical first-site residual. -/
def finiteAdjointParityResidual (n : ℕ) : ℝ :=
  2*(Real.log 2-1/2) - dotProduct (adjointParityGramRow n) ((finitePacketGram n)⁻¹.mulVec (meanVector n))

theorem finiteAdjointParityResidual_eq (n : ℕ) :
    finiteAdjointParityResidual n = inner ℝ (hilbertOne-projection n) parityAdjointPacket := by
  have hmean : inner ℝ hilbertOne parityAdjointPacket = 2*(Real.log 2-1/2) := by
    have h := dyadicMomentProfile_mean
    rw [dyadicMomentProfile,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq,real_inner_comm hilbertOne parityAdjointPacket] at h
    linarith only [h]
  rw [finiteAdjointParityResidual,inner_sub_left,hmean,← packetCandidate_eq_projection]
  congr 1
  change dotProduct (adjointParityGramRow n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
    inner ℝ (∑ i : Fin n, packetCoefficients n i • ramanujanPacketHilbert (i.val+2)) parityAdjointPacket
  rw [sum_inner]
  simp only [real_inner_smul_left, packetCoefficients_eq_inverseGram,dotProduct,adjointParityGramRow_eq]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem finiteAdjointParityResidual_tendsto :
    Tendsto finiteAdjointParityResidual atTop (𝓝 (inner ℝ limitResidual parityAdjointPacket)) := by
  have h := ((innerSL ℝ parityAdjointPacket).continuous.tendsto limitResidual).comp
    (tendsto_const_nhds.sub projection_tendsto : Tendsto (fun n => hilbertOne-projection n) atTop (𝓝 limitResidual))
  simpa only [show finiteAdjointParityResidual = fun n => inner ℝ (hilbertOne-projection n) parityAdjointPacket
    from funext finiteAdjointParityResidual_eq, Function.comp_def, innerSL_apply_apply,
    real_inner_comm parityAdjointPacket] using h

open scoped LegalMeanAlgebra

/-- A cofinal upper bound on the signed observation controls the full
limiting residual energy linearly, even when the finite signs fluctuate. -/
theorem limitEnergy_le_six_mul_of_cofinal_adjoint_parity (τ : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, finiteAdjointParityResidual n ≤ τ+ε) :
    limitEnergy ≤ 6*τ := by
  have hb := RiemannResearch.Analysis.limit_le_of_cofinal_le_add finiteAdjointParityResidual_tendsto h
  linarith only [hb,parityAdjointPacket_residual_bounds.1]

/-- The arithmetic certificate uses a single signed row paired with the
existing inverse Gram coefficients. -/
theorem stageUnit_zero_iff_cofinal_adjoint_parity_row (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      2*(Real.log 2-1/2) ≤ dotProduct (adjointParityGramRow n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) + ε := by
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_one_mem, ← limitEnergy_zero_iff_mem]
  constructor
  · intro he
    have ht := finiteAdjointParityResidual_tendsto
    rw [limitResidual_zero_iff_energy_zero.mpr he,inner_zero_left] at ht
    simpa only [finiteAdjointParityResidual,zero_add,sub_le_iff_le_add',add_comm,add_zero] using
      RiemannResearch.Analysis.cofinal_le_add_of_tendsto ht
  · intro h
    have hE := limitEnergy_le_six_mul_of_cofinal_adjoint_parity 0
      (by simpa only [finiteAdjointParityResidual,zero_add,sub_le_iff_le_add',add_comm,add_zero] using h)
    rw [mul_zero] at hE
    exact le_antisymm hE (sq_nonneg _)

/-- Centering the parity row at the physical first site improves its
cofinal energy control. Both signed observations use the same solve. -/
def centeredAdjointParityResidual (n : ℕ) : ℝ :=
  finiteAdjointParityResidual n + (firstSiteGramCoordinates n).2/30

theorem centeredAdjointParityResidual_eq_one_solve (n : ℕ) :
    centeredAdjointParityResidual n = 2*(Real.log 2-1/2)+1/30 -
      dotProduct (fun i => adjointParityGramRow n i-finiteMoebiusSource n i/30)
        ((finitePacketGram n)⁻¹.mulVec (meanVector n)) := by
  simp only [centeredAdjointParityResidual,finiteAdjointParityResidual, firstSiteGramCoordinates,dotProduct]
  simp_rw [sub_mul,div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib,← Finset.sum_div]
  ring

theorem centeredAdjointParityResidual_tendsto :
    Tendsto centeredAdjointParityResidual atTop
      (𝓝 (inner ℝ limitResidual parityAdjointPacket + hilbertSequence limitResidual 1/30)) :=
  finiteAdjointParityResidual_tendsto.add (((continuous_snd.tendsto _).comp firstSiteGramCoordinates_tendsto).div_const 30)

theorem one_third_lt_centeredParityLowerCoefficient :
    (1/3:ℝ) < 2/5-1/(10*Real.sqrt 3) := by
  have hs : (3/2:ℝ) < Real.sqrt 3 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have hu : (1:ℝ)/(10*Real.sqrt 3) < 1/15 := by
    apply (div_lt_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)).mpr
    linarith only [hs]
  linarith only [hu]

/-- Lower correlation at the centered source, with the true limiting residual. -/
theorem centeredAdjointParity_limit_lower :
    (2/5-1/(10*Real.sqrt 3))*limitEnergy ≤
      inner ℝ limitResidual parityAdjointPacket + hilbertSequence limitResidual 1/30 := by
  have hl := (abs_le.mp parityAdjointPacket_first_site_coupling).1
  calc
    _ = 2*limitEnergy/5 - limitEnergy/(10*Real.sqrt 3) := by ring
    _ ≤ _ := by linarith only [hl]

/-- The coefficient is explicit and exceeds one third. -/
theorem centeredAdjointParity_energy_budget (τ : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, centeredAdjointParityResidual n ≤ τ+ε) :
    (2/5-1/(10*Real.sqrt 3))*limitEnergy ≤ τ := by
  have hb := RiemannResearch.Analysis.limit_le_of_cofinal_le_add centeredAdjointParityResidual_tendsto h
  exact centeredAdjointParity_limit_lower.trans hb

theorem stageUnit_zero_iff_cofinal_centered_adjoint_parity_row (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      centeredAdjointParityResidual n ≤ ε := by
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_one_mem, ← limitEnergy_zero_iff_mem]
  constructor
  · intro he
    have h := centeredAdjointParityResidual_tendsto
    have hb := firstCoordinate_zero_iff_residual_zero.mpr (limitResidual_zero_iff_energy_zero.mpr he)
    rw [hb,limitResidual_zero_iff_energy_zero.mpr he,inner_zero_left,zero_div,zero_add] at h
    simpa only [zero_add] using RiemannResearch.Analysis.cofinal_le_add_of_tendsto h
  · intro h
    have hscale := centeredAdjointParity_energy_budget 0 (by simpa only [zero_add] using h)
    have hc := (by norm_num : (0:ℝ) < 1/3).trans one_third_lt_centeredParityLowerCoefficient
    exact le_antisymm (nonpos_of_mul_nonpos_right hscale hc) (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake

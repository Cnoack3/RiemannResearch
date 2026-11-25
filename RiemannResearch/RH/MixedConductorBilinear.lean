import RiemannResearch.NumberTheory.FeketePowerSlope
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MixedOrthogonalMean
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.ResidueConductorVariation
import RiemannResearch.RH.ThresholdContractiveRepair
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bilinear mean extension, rank-one factorization, and the exact defect form

Source: the user's bilinear-extension discussion, November 24, 2026.
The arithmetic input is the independently proved logarithmic rigidity lemma
in MixedConductorRankOne, supported by DyadicAdditiveRigidity and
ResidueConductorVariation. The factorization proof below uses this input,
closed-span continuity, and the elementary membership and mean of the screened
seed. It does not invoke the existing geometric rank-one conclusions.

The mixed cross-pairing is zero. The meaningful pairing has domains
mixedClosureᗮ and closedSpace, and factors as R(h) C(v).
The symmetric screened form is ‖u‖² C(v) C(w); its centered defect form is
‖u - 1‖² C(v) C(w). Vanishing of that last coefficient remains an explicit
condition in every implication to the ambient constant or RH.
-/

noncomputable section
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear
open CoefficientStabilization

/-- Reassemble the orthogonal mixed-complement/mixed decomposition. -/
def directSumAssembly : (mixedClosureᗮ × mixedClosure) →L[ℝ] ThresholdHilbert :=
  mixedClosureᗮ.subtypeL.coprod mixedClosure.subtypeL

/-- The ambient inner product as a continuous bilinear form on the direct sum. -/
def directSumForm :
    (mixedClosureᗮ × mixedClosure) →L[ℝ]
      (mixedClosureᗮ × mixedClosure) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp directSumAssembly directSumAssembly

/-- The linear extension of the mean to the full orthogonal direct sum. -/
def directSumMean : (mixedClosureᗮ × mixedClosure) →L[ℝ] ℝ :=
  hilbertMeanContinuous.comp directSumAssembly

/-- The cross-pairing between the two orthogonal summands. -/
def mixedPairing : mixedClosureᗮ →L[ℝ] mixedClosure →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp mixedClosureᗮ.subtypeL mixedClosure.subtypeL

/-- The pairing that detects the legal quotient by the mixed closure. -/
def legalPairing : mixedClosureᗮ →L[ℝ] closedSpace →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp mixedClosureᗮ.subtypeL closedSpace.subtypeL

@[simp] theorem legalPairing_apply (h : mixedClosureᗮ) (v : closedSpace) :
    legalPairing h v = inner ℝ h.val v.val := rfl

theorem mixedPairing_eq_zero : mixedPairing = 0 := by
  ext h m
  change inner ℝ h.val m.val = 0
  exact (real_inner_comm _ _).trans (h.property m.val m.property)

theorem directSumMean_apply (h : mixedClosureᗮ) (m : mixedClosure) :
    directSumMean (h, m) = mixedOrthogonalMean h := by
  change inner ℝ hilbertOne (h.val + m.val) = inner ℝ hilbertOne h.val
  rw [inner_add_right]
  have hm : inner ℝ hilbertOne m.val = 0 :=
    (real_inner_comm _ _).trans
      (one_mem_mixedClosure_orthogonal m.val m.property)
  rw [hm, add_zero]

theorem directSumForm_apply
    (h k : mixedClosureᗮ) (m n : mixedClosure) :
    directSumForm (h, m) (k, n) =
      inner ℝ h.val k.val + inner ℝ m.val n.val := by
  change inner ℝ (h.val + m.val) (k.val + n.val) = _
  have hhn : inner ℝ h.val n.val = 0 :=
    (real_inner_comm _ _).trans (h.property n.val n.property)
  have hmk : inner ℝ m.val k.val = 0 := k.property m.val m.property
  simp only [inner_add_left, inner_add_right, hhn, hmk, add_zero, zero_add]

/-- Evaluating the direct-sum form at the ambient constant recovers the mean. -/
theorem directSumForm_one (x : mixedClosureᗮ × mixedClosure) :
    directSumForm x
      (⟨hilbertOne, one_mem_mixedClosure_orthogonal⟩, 0) = directSumMean x := by
  change inner ℝ (x.1.val + x.2.val) (hilbertOne + 0) =
    inner ℝ hilbertOne (x.1.val + x.2.val)
  rw [add_zero, real_inner_comm]

private theorem rawResidueAtom_inner_one_log (i : ℕ) :
    inner ℝ (rawResidueAtom i) hilbertOne = Real.log ((i + 2 : ℕ) : ℝ) := by
  rw [hilbert_inner_one]
  have hs : hilbertSequence (rawResidueAtom i) = residue (i + 2) :=
    funext (rawResidueAtom_sequence i)
  rw [hs, paretoMean_residue (i + 2) (by omega)]

/-- The exponent Fekete slope at two computes the coefficient of the
mixed-orthogonal/legal pairing from the residue pairings alone. -/
theorem pairing_eq_fekete_rate
    {h v : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) (hv : v ∈ closedSpace) :
    inner ℝ h v =
      (RiemannResearch.NumberTheory.powerRate (residuePairing h) 2 / Real.log 2) *
        inner ℝ v hilbertOne := by
  let c := RiemannResearch.NumberTheory.powerRate (residuePairing h) 2 / Real.log 2
  have hc : ∀ n : ℕ, 0 < n → residuePairing h n = c * Real.log (n : ℝ) :=
    RiemannResearch.NumberTheory.log_normalization_by_powerRate (residuePairing_eq_log hh)
  let L : Submodule ℝ ThresholdHilbert :=
    { carrier := {x | inner ℝ h x = c * inner ℝ x hilbertOne}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change inner ℝ h x = c * inner ℝ x hilbertOne at hx
        change inner ℝ h y = c * inner ℝ y hilbertOne at hy
        change inner ℝ h (x + y) = c * inner ℝ (x + y) hilbertOne
        rw [inner_add_right, inner_add_left, hx, hy, mul_add]
      smul_mem' := by
        intro a x hx
        change inner ℝ h x = c * inner ℝ x hilbertOne at hx
        change inner ℝ h (a • x) = c * inner ℝ (a • x) hilbertOne
        rw [real_inner_smul_right, real_inner_smul_left, hx]
        ring }
  have hLclosed : IsClosed (L : Set ThresholdHilbert) := by
    change IsClosed {x : ThresholdHilbert | inner ℝ h x = c * inner ℝ x hilbertOne}
    exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.mul (continuous_id.inner continuous_const))
  have hle : closedSpace ≤ L := by
    change (Submodule.span ℝ (Set.range residueAtom)).topologicalClosure ≤ L
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change inner ℝ h (residueAtom i) = c * inner ℝ (residueAtom i) hilbertOne
      have hi := hc (i + 2) (by omega)
      have hcond : 1 < i + 2 := by omega
      simp only [residuePairing, if_pos hcond, Nat.add_sub_cancel] at hi
      have hm := rawResidueAtom_inner_one_log i
      rw [rawResidueAtom, real_inner_smul_left] at hi hm
      calc
        inner ℝ h (residueAtom i) = inner ℝ (residueAtom i) h := real_inner_comm _ _
        _ = c * inner ℝ (residueAtom i) hilbertOne := by
          apply mul_left_cancel₀ (show ((i + 2 : ℕ) : ℝ) ≠ 0 by positivity)
          calc
            _ = c * Real.log ((i + 2 : ℕ) : ℝ) := hi
            _ = c * (((i + 2 : ℕ) : ℝ) *
                inner ℝ (residueAtom i) hilbertOne) := by rw [hm]
            _ = _ := by ring
    · exact hLclosed
  exact hle hv

/-- Every arithmetic base greater than one computes the legal pairing. -/
theorem pairing_eq_fekete_rate_at_base {h v : ThresholdHilbert}
    (hh : h ∈ mixedClosureᗮ) (hv : v ∈ closedSpace) {a : ℕ} (ha : 1 < a) :
    inner ℝ h v =
      (RiemannResearch.NumberTheory.powerRate (residuePairing h) a / Real.log (a : ℝ)) *
        inner ℝ v hilbertOne := by
  obtain ⟨c, hc⟩ := residuePairing_eq_log hh
  have htwo := RiemannResearch.NumberTheory.powerRate_div_log_eq_of_log hc
    (by decide : 1 < 2)
  have hbase := RiemannResearch.NumberTheory.powerRate_div_log_eq_of_log hc ha
  have hchange : RiemannResearch.NumberTheory.powerRate (residuePairing h) 2 / Real.log 2 =
      RiemannResearch.NumberTheory.powerRate (residuePairing h) a / Real.log (a : ℝ) :=
    htwo.trans hbase.symm
  rw [pairing_eq_fekete_rate hh hv, hchange]

/-- The coefficient functional can be read from the residue powers of any base. -/
theorem mixedPacketCoefficient_eq_fekete_rate (h : mixedClosureᗮ) {a : ℕ} (ha : 1 < a) :
    mixedPacketCoefficient h =
      RiemannResearch.NumberTheory.powerRate (residuePairing h.val) a / Real.log (a : ℝ) := by
  change inner ℝ normalizedScreenedTwo h.val = _
  rw [real_inner_comm]
  have hu := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  simpa only [normalizedScreenedTwo_mean, mul_one] using pairing_eq_fekete_rate_at_base h.property hu ha

/-- Evaluation at the legal mean-one seed identifies the arithmetic
Fekete coefficient with the Riesz coefficient of the rank-one form. -/
theorem pairing_factorization_of_rigidity
    {h v : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) (hv : v ∈ closedSpace) :
    inner ℝ h v =
      inner ℝ normalizedScreenedTwo h * inner ℝ v hilbertOne := by
  have hc := mixedPacketCoefficient_eq_fekete_rate (⟨h, hh⟩ : mixedClosureᗮ) (by decide : 1 < 2)
  change inner ℝ normalizedScreenedTwo h =
    RiemannResearch.NumberTheory.powerRate (residuePairing h) 2 / Real.log 2 at hc
  rw [pairing_eq_fekete_rate hh hv, hc]

/-- Dividing the rank-one pairing at the screened seed by its squared norm
recovers the Pareto mean of every legal vector. -/
theorem inner_screenedTwo_div_norm_sq {v : ThresholdHilbert} (hv : v ∈ closedSpace) :
    inner ℝ v normalizedScreenedTwo / ‖normalizedScreenedTwo‖ ^ 2 =
      inner ℝ v hilbertOne := by
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff _).mp mixed_starProjection_screenedTwo
  have hpos : 0 < ‖normalizedScreenedTwo‖ := zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo
  apply (div_eq_iff (sq_pos_of_pos hpos).ne').2
  calc
    inner ℝ v normalizedScreenedTwo = inner ℝ normalizedScreenedTwo v := real_inner_comm _ _
    _ = inner ℝ v hilbertOne * ‖normalizedScreenedTwo‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq, mul_comm] using
        pairing_factorization_of_rigidity hu hv

/-- The projected constant represents the ambient Pareto mean on the legal space. -/
theorem inner_limitProjection_eq_inner_one {v : ThresholdHilbert} (hv : v ∈ closedSpace) :
    inner ℝ v limitProjection = inner ℝ v hilbertOne := by
  rw [limitProjection_eq_inv_norm_sq_smul_screenedTwo, real_inner_smul_right]
  simpa only [div_eq_mul_inv, mul_comm] using inner_screenedTwo_div_norm_sq hv

/-- The genuine pairing equals the outer product R ⊗ C as a continuous
bilinear map with its two distinct domains retained. -/
theorem legalPairing_eq_rankOne :
    legalPairing = mixedPacketCoefficient.smulRight legalPacketMean := by
  ext h v
  change inner ℝ h.val v.val =
    inner ℝ normalizedScreenedTwo h.val * inner ℝ v.val hilbertOne
  exact pairing_factorization_of_rigidity h.property v.property

/-- The factorization is nontrivial: the constant pairs to one with the legal seed. -/
theorem legalPairing_one_seed :
    legalPairing ⟨hilbertOne, one_mem_mixedClosure_orthogonal⟩
      ⟨normalizedScreenedTwo,
        screenedPrimeClosure_le_closedSpace
          normalizedScreenedTwo_mem_screenedPrimeClosure⟩ = 1 := by
  change inner ℝ hilbertOne normalizedScreenedTwo = 1
  exact (real_inner_comm _ _).trans normalizedScreenedTwo_mean

theorem legalPairing_ne_zero : legalPairing ≠ 0 := by
  intro hz
  have h := legalPairing_one_seed
  rw [hz] at h
  exact zero_ne_one h

/-- The range of the pairing map is precisely the line generated by the legal mean. -/
theorem legalPairing_range :
    LinearMap.range legalPairing.toLinearMap =
      Submodule.span ℝ {legalPacketMean} := by
  rw [legalPairing_eq_rankOne]
  apply le_antisymm
  · rintro y ⟨h, rfl⟩
    change mixedPacketCoefficient h • legalPacketMean ∈
      Submodule.span ℝ {legalPacketMean}
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    refine ⟨⟨hilbertOne, one_mem_mixedClosure_orthogonal⟩, ?_⟩
    change inner ℝ normalizedScreenedTwo hilbertOne • legalPacketMean = legalPacketMean
    rw [normalizedScreenedTwo_mean, one_smul]

/-- The bilinear factorization recovers the screening operator as a rank-one
continuous map on V. This proof tests the difference against itself. -/
theorem screening_factorization :
    fullScreening.comp closedSpace.subtypeL =
      legalPacketMean.smulRight normalizedScreenedTwo := by
  apply ContinuousLinearMap.ext
  intro v
  change fullScreening v.val = inner ℝ v.val hilbertOne • normalizedScreenedTwo
  let w := fullScreening v.val - inner ℝ v.val hilbertOne • normalizedScreenedTwo
  have huO : normalizedScreenedTwo ∈ mixedClosureᗮ := by
    change (Real.log 2)⁻¹ • fullScreening (ramanujanPacketHilbert 2) ∈ mixedClosureᗮ
    exact mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
  have hw : w ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem (fullScreening_mem_orthogonal _)
      (mixedClosure.orthogonal.smul_mem _ huO)
  have he : inner ℝ w w = 0 := by
    change inner ℝ
      (fullScreening v.val - inner ℝ v.val hilbertOne • normalizedScreenedTwo) w = 0
    rw [inner_sub_left, real_inner_smul_left,
      fullScreening_inner_right_of_orthogonal v.val w hw]
    have hpair : inner ℝ v.val w =
        inner ℝ normalizedScreenedTwo w * inner ℝ v.val hilbertOne :=
      (real_inner_comm _ _).trans (pairing_factorization_of_rigidity hw v.property)
    rw [hpair]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp he)

/-- The legal screening factorization, obtained from the Fekete pairing,
sends every positive power of a prime to its logarithm times the screened seed. -/
theorem fekete_screened_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    fullScreening (ramanujanPacketHilbert (p ^ k)) =
      Real.log (p : ℝ) • normalizedScreenedTwo := by
  let v : closedSpace :=
    ⟨ramanujanPacketHilbert (p ^ k), packet_mem_closedSpace _ (Nat.one_lt_pow hk hp.one_lt)⟩
  have h := DFunLike.congr_fun screening_factorization v
  change fullScreening (ramanujanPacketHilbert (p ^ k)) =
    inner ℝ (ramanujanPacketHilbert (p ^ k)) hilbertOne • normalizedScreenedTwo at h
  rwa [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
    ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp] at h

/-- Dividing by the prime's logarithm gives the same screened vector at every exponent. -/
theorem fekete_normalized_screened_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (Real.log (p : ℝ))⁻¹ • fullScreening (ramanujanPacketHilbert (p ^ k)) =
      normalizedScreenedTwo := by
  have hp' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [fekete_screened_prime_pow hp hk, smul_smul,
    inv_mul_cancel₀ (Real.log_pos hp').ne', one_smul]

/-- The normalized screened prime-power packets still form this singleton after
discarding all first powers. Conductor four supplies a witness to the reverse inclusion. -/
theorem fekete_normalized_screened_prime_pow_set :
    {x : ThresholdHilbert | ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧
      (Real.log (p : ℝ))⁻¹ • fullScreening (ramanujanPacketHilbert (p ^ k)) = x} =
        {normalizedScreenedTwo} := by
  ext x
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    exact Set.mem_singleton_iff.mpr (fekete_normalized_screened_prime_pow hp (by omega))
  · intro hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨2, 2, Nat.prime_two, le_rfl, fekete_normalized_screened_prime_pow Nat.prime_two
      (by decide : (2 : ℕ) ≠ 0)⟩

/-- The packet at every positive prime power pairs to the rate at its prime base. -/
theorem prime_pow_packet_pairing_eq_powerRate {h : ThresholdHilbert}
    (hh : h ∈ mixedClosureᗮ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    inner ℝ (ramanujanPacketHilbert (p ^ k)) h =
      RiemannResearch.NumberTheory.powerRate (residuePairing h) p := by
  rw [← fullScreening_inner_right_of_orthogonal _ _ hh, fekete_screened_prime_pow hp hk,
    real_inner_smul_left]
  have hc := mixedPacketCoefficient_eq_fekete_rate (⟨h, hh⟩ : mixedClosureᗮ) hp.one_lt
  change inner ℝ normalizedScreenedTwo h =
    RiemannResearch.NumberTheory.powerRate (residuePairing h) p / Real.log (p : ℝ) at hc
  have hp' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  rw [mul_comm]
  exact (eq_div_iff (Real.log_pos hp').ne').mp hc

/-- The right radical is exactly M, so no nonzero legal quotient class is invisible. -/
theorem legalPairing_right_radical (v : closedSpace) :
    (∀ h : mixedClosureᗮ, legalPairing h v = 0) ↔ v.val ∈ mixedClosure := by
  constructor
  · intro hv
    have hs := fullScreening_mem_orthogonal v.val
    have ht := hv ⟨fullScreening v.val, hs⟩
    change inner ℝ (fullScreening v.val) v.val = 0 at ht
    have hz : inner ℝ (fullScreening v.val) (fullScreening v.val) = 0 :=
      (fullScreening_inner_right_of_orthogonal v.val _ hs).trans
        ((real_inner_comm _ _).trans ht)
    have he := inner_self_eq_zero.mp hz
    change v.val - mixedClosure.starProjection v.val = 0 at he
    rw [sub_eq_zero.mp he]
    exact mixedClosure.starProjection_apply_mem _
  · intro hv h
    change inner ℝ h.val v.val = 0
    exact (real_inner_comm _ _).trans (h.property v.val hv)

/-- The left radical is the ambient legal orthogonal complement. -/
theorem legalPairing_left_radical (h : mixedClosureᗮ) :
    (∀ v : closedSpace, legalPairing h v = 0) ↔ h.val ∈ closedSpaceᗮ := by
  constructor
  · intro hh v hv
    exact (real_inner_comm _ _).trans (hh ⟨v, hv⟩)
  · intro hh v
    exact (real_inner_comm _ _).trans (hh v.val v.property)

/-- Product of the ambient means, bundled as a continuous bilinear form. -/
def meanProduct : ThresholdHilbert →L[ℝ] ThresholdHilbert →L[ℝ] ℝ :=
  hilbertMeanContinuous.smulRight hilbertMeanContinuous

/-- The physical Hilbert form after removing M. -/
def screenedForm : ThresholdHilbert →L[ℝ] ThresholdHilbert →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp fullScreening fullScreening

/-- The exact difference of the screened form and the product of means. -/
def defectForm : ThresholdHilbert →L[ℝ] ThresholdHilbert →L[ℝ] ℝ :=
  screenedForm - meanProduct

/-- Remove both the mixed component and the constant component. -/
def centeredScreening : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  fullScreening - hilbertMeanContinuous.smulRight hilbertOne

@[simp] theorem meanProduct_apply (x y : ThresholdHilbert) :
    meanProduct x y = hilbertMeanContinuous x * hilbertMeanContinuous y := rfl

@[simp] theorem screenedForm_apply (x y : ThresholdHilbert) :
    screenedForm x y = inner ℝ (fullScreening x) (fullScreening y) := rfl

@[simp] theorem defectForm_apply (x y : ThresholdHilbert) :
    defectForm x y =
      inner ℝ (fullScreening x) (fullScreening y) -
        hilbertMeanContinuous x * hilbertMeanContinuous y := rfl

@[simp] theorem centeredScreening_apply (x : ThresholdHilbert) :
    centeredScreening x =
      fullScreening x - hilbertMeanContinuous x • hilbertOne := rfl

theorem mean_fullScreening (x : ThresholdHilbert) :
    hilbertMeanContinuous (fullScreening x) = hilbertMeanContinuous x := by
  change inner ℝ hilbertOne (fullScreening x) = inner ℝ hilbertOne x
  exact (real_inner_comm _ _).trans
    ((fullScreening_inner_right_of_orthogonal x hilbertOne
      one_mem_mixedClosure_orthogonal).trans (real_inner_comm _ _))

/-- The mean-zero part of the mixed orthogonal complement is closed. -/
instance ambientMixedMeanKernel_complete : CompleteSpace ambientMixedMeanKernel :=
  (show IsClosed (ambientMixedMeanKernel : Set ThresholdHilbert) from
    mixedClosure.isClosed_orthogonal.inter
      (Submodule.span ℝ {hilbertOne}).isClosed_orthogonal).completeSpace_coe

/-- Centered screening lands in the ambient mixed-orthogonal mean kernel. -/
theorem centeredScreening_mem (x : ThresholdHilbert) :
    centeredScreening x ∈ ambientMixedMeanKernel := by
  change fullScreening x - hilbertMeanContinuous x • hilbertOne ∈
    ambientMixedMeanKernel
  simpa only [CenteredMeanSnake.center_apply, mean_fullScreening] using
    (center_mem_mixedOrthogonal_kernel (fullScreening_mem_orthogonal x))

/-- Centered screening is exactly the orthogonal projection onto the
mixed-orthogonal mean kernel. This statement does not use Rank 1. -/
theorem centeredScreening_eq_starProjection :
    centeredScreening = ambientMixedMeanKernel.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (centeredScreening_mem x)
  intro y hy
  have hy0 : inner ℝ hilbertOne y = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hy.2
  change inner ℝ
    (x - (fullScreening x - hilbertMeanContinuous x • hilbertOne)) y = 0
  rw [inner_sub_left, inner_sub_left,
    fullScreening_inner_right_of_orthogonal x y hy.1,
    real_inner_smul_left, hy0, mul_zero, sub_zero, sub_self]

/-- The defect form is a Gram form on the centered screened vectors. -/
theorem defectForm_eq_inner (x y : ThresholdHilbert) :
    defectForm x y = inner ℝ (centeredScreening x) (centeredScreening y) := by
  have hx : inner ℝ (fullScreening x) hilbertOne = hilbertMeanContinuous x :=
    (fullScreening_inner_right_of_orthogonal x hilbertOne
      one_mem_mixedClosure_orthogonal).trans (real_inner_comm _ _)
  have hy : inner ℝ hilbertOne (fullScreening y) = hilbertMeanContinuous y :=
    mean_fullScreening y
  have he : inner ℝ hilbertOne hilbertOne = 1 := by
    rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  simp only [defectForm_apply, centeredScreening_apply, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, hx, hy, he]
  ring

theorem defectForm_self_eq_norm_sq (x : ThresholdHilbert) :
    defectForm x x = ‖centeredScreening x‖ ^ 2 := by
  rw [defectForm_eq_inner, real_inner_self_eq_norm_sq]

theorem defectForm_nonneg (x : ThresholdHilbert) : 0 ≤ defectForm x x := by
  rw [defectForm_self_eq_norm_sq]
  exact sq_nonneg _

theorem defectForm_symm (x y : ThresholdHilbert) :
    defectForm x y = defectForm y x := by
  rw [defectForm_eq_inner, defectForm_eq_inner, real_inner_comm]

/-- On legal vectors, the centered screened image is the mean times the defect. -/
theorem centeredScreening_legal (v : closedSpace) :
    centeredScreening v.val =
      legalPacketMean v • (normalizedScreenedTwo - hilbertOne) := by
  have hs := DFunLike.congr_fun screening_factorization v
  change fullScreening v.val = legalPacketMean v • normalizedScreenedTwo at hs
  have hm : hilbertMeanContinuous v.val = legalPacketMean v := by
    change inner ℝ hilbertOne v.val = inner ℝ v.val hilbertOne
    exact real_inner_comm _ _
  rw [centeredScreening_apply, hs, hm, smul_sub]

/-- Rank one retains the physical squared norm of the screened direction. -/
theorem screenedForm_legal (v w : closedSpace) :
    screenedForm v.val w.val =
      ‖normalizedScreenedTwo‖ ^ 2 * legalPacketMean v * legalPacketMean w := by
  have hv := DFunLike.congr_fun screening_factorization v
  have hw := DFunLike.congr_fun screening_factorization w
  change fullScreening v.val = legalPacketMean v • normalizedScreenedTwo at hv
  change fullScreening w.val = legalPacketMean w • normalizedScreenedTwo at hw
  rw [screenedForm_apply, hv, hw, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- The exact positive defect coefficient is preserved in the bilinear factorization. -/
theorem defectForm_legal (v w : closedSpace) :
    defectForm v.val w.val =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 *
        legalPacketMean v * legalPacketMean w := by
  rw [defectForm_eq_inner, centeredScreening_legal, centeredScreening_legal,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

/-- Evaluating at the known legal mean-one seed detects the entire defect. -/
theorem defectForm_normalizedScreenedTwo :
    defectForm normalizedScreenedTwo normalizedScreenedTwo =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  let u : closedSpace := ⟨normalizedScreenedTwo,
    screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure⟩
  have hm : legalPacketMean u = 1 := normalizedScreenedTwo_mean
  simpa only [hm, mul_one] using defectForm_legal u u

/-- Vanishing of the restricted defect form is precisely the ambient endpoint. -/
theorem defectForm_vanishes_iff :
    (∀ v w : closedSpace, defectForm v.val w.val = 0) ↔
      normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    let u : closedSpace := ⟨normalizedScreenedTwo,
      screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure⟩
    have hz := h u u
    change defectForm normalizedScreenedTwo normalizedScreenedTwo = 0 at hz
    rw [defectForm_normalizedScreenedTwo, pow_two, mul_eq_zero, or_self,
      norm_eq_zero, sub_eq_zero] at hz
    exact hz
  · intro h v w
    rw [defectForm_legal, h, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul, zero_mul]

/-- Replacing R by C in the mixed-orthogonal/legal factorization is exactly
the stronger ambient-constant assertion. -/
theorem legalPairing_eq_meanProduct_iff :
    legalPairing = mixedOrthogonalMean.smulRight legalPacketMean ↔
      normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    let d := normalizedScreenedTwo - hilbertOne
    have huO : normalizedScreenedTwo ∈ mixedClosureᗮ := by
      change (Real.log 2)⁻¹ • fullScreening (ramanujanPacketHilbert 2) ∈ mixedClosureᗮ
      exact mixedClosure.orthogonal.smul_mem _ (fullScreening_mem_orthogonal _)
    let hd : mixedClosureᗮ :=
      ⟨d, mixedClosure.orthogonal.sub_mem huO one_mem_mixedClosure_orthogonal⟩
    let u : closedSpace := ⟨normalizedScreenedTwo,
      screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure⟩
    have hm : legalPacketMean u = 1 := normalizedScreenedTwo_mean
    have he := congrArg (fun B : mixedClosureᗮ →L[ℝ] closedSpace →L[ℝ] ℝ => B hd u) h
    change inner ℝ d normalizedScreenedTwo = mixedOrthogonalMean hd * legalPacketMean u at he
    rw [hm, mul_one] at he
    have hz : inner ℝ d d = 0 := by
      change inner ℝ d (normalizedScreenedTwo - hilbertOne) = 0
      rw [inner_sub_right, he]
      change inner ℝ hilbertOne d - inner ℝ d hilbertOne = 0
      exact sub_eq_zero.mpr (real_inner_comm _ _)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  · intro h
    rw [legalPairing_eq_rankOne]
    have hfun : mixedPacketCoefficient = mixedOrthogonalMean := by
      ext x
      change inner ℝ normalizedScreenedTwo x.val = inner ℝ hilbertOne x.val
      rw [h]
    rw [hfun]

/-- RH follows once the positive defect form is shown to vanish on V. -/
theorem riemannHypothesis_of_defectForm_vanishes
    (h : ∀ v w : closedSpace, defectForm v.val w.val = 0) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo (defectForm_vanishes_iff.mp h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.Bilinear

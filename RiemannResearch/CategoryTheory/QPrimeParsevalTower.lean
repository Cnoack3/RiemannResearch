import RiemannResearch.CategoryTheory.PhysicalParityObject
import RiemannResearch.RH.PrimeSupportMeasureChange
import RiemannResearch.RH.MixedReciprocalDensity
import RiemannResearch.RH.QDivisorHilbertBasis
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # The physical Parseval tower ordered by largest prime
Each positive prime is admitted separately, with every power at that prime. The identity
map gives the actual native mixed tower. Removing the transported Pareto carry line
gives the native orthogonal CRT tower with that line held fixed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
open RiemannResearch.RH RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open RiemannResearch.RH.QParetoEquivalence RiemannResearch.RH.QPhysicalQuotientMetric
open RiemannResearch.Analysis.NestedOrthogonalDecomposition
open RiemannResearch.CategoryTheory.PhysicalParityObject
open MeasureChange (qMixed qParity qMixed_isClosed q_terminal_parity_zero_iff_rh qParity_norm_sq)

namespace RiemannResearch.CategoryTheory.QPrimeParsevalTower

abbrev native : QHilbert →L[ℝ] QHilbert := ContinuousLinearMap.id ℝ QHilbert

/-- All prime divisors have arrived by the cutoff. No exponent restriction is imposed. -/
def supportedThrough (B d : ℕ) : Prop := ∀ p ∈ d.primeFactors, p ≤ B

/-- A mixed packet with its original physical values under Q. -/
def physicalPacket (q : Index) : QHilbert := paretoEquiv.symm (ramanujanPacketHilbert q.val)

theorem physicalPacket_mem (q : Index) : physicalPacket q ∈ qMixed := by
  change paretoEquiv (paretoEquiv.symm _) ∈ mixedClosure
  rw [paretoEquiv.apply_symm_apply]
  exact (packet q).property

/-- Largest-prime filtration of a bounded linear image of the physical mixed packets. -/
def stage (T : QHilbert →L[ℝ] QHilbert) (B : ℕ) : Submodule ℝ QHilbert :=
  (Submodule.span ℝ ((fun q : Index => T (physicalPacket q)) ''
    {q | supportedThrough B q.val})).topologicalClosure

/-- The closed space exhausted by the tower. -/
def terminal (T : QHilbert →L[ℝ] QHilbert) : Submodule ℝ QHilbert :=
  (qMixed.map T.toLinearMap).topologicalClosure

theorem packet_mem_stage (T : QHilbert →L[ℝ] QHilbert) {B : ℕ} (q : Index)
    (h : supportedThrough B q.val) : T (physicalPacket q) ∈ stage T B :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, h, rfl⟩)

theorem stage_mono (T : QHilbert →L[ℝ] QHilbert) : Monotone (stage T) := by
  intro a b hab
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q, fun p hp => (hq p hp).trans hab, rfl⟩

theorem stage_two (T : QHilbert →L[ℝ] QHilbert) : stage T 2 = ⊥ := by
  have he : {q : Index | supportedThrough 2 q.val} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q h
    have hs : q.val.primeFactors ⊆ {2} := by
      intro p hp
      have hlo := (Nat.mem_primeFactors.mp hp).1.two_le
      exact Finset.mem_singleton.mpr (le_antisymm (h p hp) hlo)
    have hle := Finset.card_le_card hs
    rw [Finset.card_singleton] at hle
    have hpos := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr q.property.1)
    exact q.property.2 (isPrimePow_iff_card_primeFactors_eq_one.mpr (by omega))
  simp [stage, he]

/-- Composite cutoffs produce no new native layer. -/
theorem stage_succ_of_not_prime (T : QHilbert →L[ℝ] QHilbert) (B : ℕ)
    (h : ¬ (B+1).Prime) : stage T (B+1) = stage T B := by
  apply le_antisymm _ (stage_mono T (Nat.le_succ B))
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨q, ?_, rfl⟩
  intro p hp
  have hle := hq p hp
  have hne : p ≠ B+1 := fun he => h (he ▸ (Nat.mem_primeFactors.mp hp).1)
  omega

theorem stage_le_terminal (T : QHilbert →L[ℝ] QHilbert) (B : ℕ) :
    stage T B ≤ terminal T := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨q, _, rfl⟩
  exact ⟨_, physicalPacket_mem q, rfl⟩

instance stage_projection (T : QHilbert →L[ℝ] QHilbert) (B : ℕ) :
    (stage T B).HasOrthogonalProjection := by
  letI : CompleteSpace (stage T B) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

instance terminal_projection (T : QHilbert →L[ℝ] QHilbert) :
    (terminal T).HasOrthogonalProjection := by
  letI : CompleteSpace (terminal T) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Each mixed conductor enters by its own integer cutoff, giving exhaustive closure. -/
theorem stage_dense (T : QHilbert →L[ℝ] QHilbert) :
    (⨆ B, stage T B).topologicalClosure = terminal T := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le (stage_le_terminal T))
      (Submodule.isClosed_topologicalClosure _)
  · apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
    apply (MixedReciprocalDensity.mixed_image_le_iff T _
      (Submodule.isClosed_topologicalClosure _)).2
    intro d hd hm
    let q : Index := ⟨d, by omega, hm⟩
    apply Submodule.le_topologicalClosure
    apply le_iSup (stage T) d
    apply packet_mem_stage T q
    intro p hp
    exact Nat.le_of_dvd (by omega) (Nat.mem_primeFactors.mp hp).2.1

theorem projection_tendsto (T : QHilbert →L[ℝ] QHilbert) (x : QHilbert) :
    Tendsto (fun B => (stage T B).starProjection x) atTop (𝓝 ((terminal T).starProjection x)) := by
  simpa only [stage_dense] using
    Submodule.starProjection_tendsto_closure_iSup (stage T) (stage_mono T) x

/-- The layer indexed by k admits the prime k+1, when that number is prime. -/
abbrev layer (T : QHilbert →L[ℝ] QHilbert) (k : ℕ) : Submodule ℝ QHilbert :=
  stage T (k+1) ⊓ (stage T k)ᗮ

instance layer_projection (T : QHilbert →L[ℝ] QHilbert) (k : ℕ) :
    (layer T k).HasOrthogonalProjection :=
  carry_hasOrthogonalProjection (stage_mono T (Nat.le_succ k))

theorem layer_difference (T : QHilbert →L[ℝ] QHilbert) (k : ℕ) (x : QHilbert) :
    (layer T k).starProjection x =
      (stage T (k+1)).starProjection x - (stage T k).starProjection x :=
  carry_projection_apply (stage_mono T (Nat.le_succ k)) x

/-- The physical finite-coordinate functional used to distinguish new largest-prime rows. -/
def coordinate (d : ℕ) : QHilbert →L[ℝ] ℝ :=
  (mobiusDifferenceCLM d).comp paretoEquiv.toContinuousLinearMap

theorem old_stage_le_coordinate_ker (q : Index) {B p : ℕ}
    (hp : p ∈ q.val.primeFactors) (hB : B < p) :
    stage native B ≤ (coordinate q.val).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    have hr0 := Nat.zero_lt_one.trans r.property.1
    have hnd : ¬ q.val ∣ r.val := fun hd =>
      (not_lt_of_ge (hr p (Nat.primeFactors_mono hd hr0.ne' hp))) hB
    change mobiusDifferenceCLM q.val (paretoEquiv (paretoEquiv.symm _)) = 0
    rw [paretoEquiv.apply_symm_apply,
      mobiusDifferenceCLM_ramanujanPacketHilbert _ _ q.property.1 hr0, if_neg hnd]
  · exact (coordinate q.val).isClosed_ker

/-- A row admitted at its largest prime retains its own nonzero Möbius coordinate. -/
theorem arriving_packet_coordinate (B : ℕ) (q : Index)
    (hq : supportedThrough (B+1) q.val) (hp : B+1 ∈ q.val.primeFactors) :
    coordinate q.val ((layer native B).starProjection (physicalPacket q)) = -(q.val : ℝ) := by
  have htop : physicalPacket q ∈ stage native (B+1) := packet_mem_stage native q hq
  have hzero := old_stage_le_coordinate_ker q hp (Nat.lt_succ_self B)
    ((stage native B).starProjection_apply_mem (physicalPacket q))
  change coordinate q.val ((stage native B).starProjection (physicalPacket q)) = 0 at hzero
  rw [layer_difference, (stage native (B+1)).starProjection_eq_self_iff.mpr htop,
    map_sub, hzero, sub_zero]
  change mobiusDifferenceCLM q.val (paretoEquiv (paretoEquiv.symm _)) = _
  rw [paretoEquiv.apply_symm_apply, mobiusDifferenceCLM_ramanujanPacketHilbert _ _ q.property.1
    (Nat.zero_lt_one.trans q.property.1), if_pos (dvd_refl _), Nat.div_self
    (Nat.zero_lt_one.trans q.property.1)]
  simp

theorem layers_orthogonal (T : QHilbert →L[ℝ] QHilbert) {i j : ℕ} (h : i < j)
    {x y : QHilbert} (hx : x ∈ layer T i) (hy : y ∈ layer T j) : inner ℝ x y = 0 :=
  hy.2 x (stage_mono T h hx.1)

private theorem zero_fit (T : QHilbert →L[ℝ] QHilbert) (x : QHilbert) :
    (stage T 0).starProjection x = 0 := by
  have h := stage_mono T (by decide : 0 ≤ 2) ((stage T 0).starProjection_apply_mem x)
  rw [stage_two] at h
  exact (Submodule.mem_bot ℝ).mp h

theorem finite_reconstruction (T : QHilbert →L[ℝ] QHilbert) (B : ℕ) (x : QHilbert) :
    ∑ k ∈ Finset.range B, (layer T k).starProjection x = (stage T B).starProjection x := by
  induction B with
  | zero => simp [zero_fit]
  | succ B ih => rw [Finset.sum_range_succ, ih, layer_difference]; abel

theorem reconstruction (T : QHilbert →L[ℝ] QHilbert) (x : QHilbert) :
    Tendsto (fun B => ∑ k ∈ Finset.range B, (layer T k).starProjection x) atTop
      (𝓝 ((terminal T).starProjection x)) := by
  simpa only [finite_reconstruction] using projection_tendsto T x

theorem quotient_step (T : QHilbert →L[ℝ] QHilbert) (k : ℕ) (x : QHilbert) :
    ‖(stage T k).mkQ x‖^2 =
      ‖(stage T (k+1)).mkQ x‖^2 + ‖(layer T k).starProjection x‖^2 := by
  have hp := (layer T k).starProjection_apply_mem x
  have ho := (stage T (k+1)).sub_starProjection_mem_orthogonal x _ hp.1
  have he : x - (stage T k).starProjection x =
      (layer T k).starProjection x + (x - (stage T (k+1)).starProjection x) := by
    rw [layer_difference]
    abel
  rw [quotient_norm, quotient_norm, he, norm_add_sq_real, ho]
  ring

theorem finite_parseval (T : QHilbert →L[ℝ] QHilbert) (B : ℕ) (x : QHilbert) :
    ‖(stage T B).mkQ x‖^2 + (∑ k ∈ Finset.range B, ‖(layer T k).starProjection x‖^2) =
      ‖x‖^2 := by
  induction B with
  | zero => rw [quotient_norm, zero_fit, sub_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ B ih =>
    rw [Finset.sum_range_succ]
    linarith only [ih, quotient_step T B x]

/-- Strong projection convergence also gives convergence of the physical quotient energies. -/
theorem quotient_tendsto (T : QHilbert →L[ℝ] QHilbert) (x : QHilbert) :
    Tendsto (fun B => ‖(stage T B).mkQ x‖^2) atTop (𝓝 (‖(terminal T).mkQ x‖^2)) := by
  simpa only [quotient_norm] using
    ((tendsto_const_nhds (x := x)).sub (projection_tendsto T x)).norm.pow 2

theorem layer_energy_hasSum (T : QHilbert →L[ℝ] QHilbert) (x : QHilbert) :
    HasSum (fun k => ‖(layer T k).starProjection x‖^2) (‖x‖^2 - ‖(terminal T).mkQ x‖^2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => sq_nonneg _) _).2
  have hr := quotient_tendsto T x
  exact ((tendsto_const_nhds (x := ‖x‖^2)).sub hr).congr' (Filter.Eventually.of_forall fun B => by
    change ‖x‖^2 - ‖(stage T B).mkQ x‖^2 = ∑ k ∈ Finset.range B, ‖(layer T k).starProjection x‖^2
    linarith only [finite_parseval T B x])

theorem terminal_native : terminal native = qMixed := by
  change (qMixed.map LinearMap.id).topologicalClosure = qMixed
  rw [Submodule.map_id]
  exact le_antisymm (Submodule.topologicalClosure_minimal _ le_rfl qMixed_isClosed)
    (Submodule.le_topologicalClosure _)

theorem legal_parseval {v : QHilbert} (hv : v ∈ physicalSpace closedSpace) :
    HasSum (fun k => ‖(layer native k).starProjection v‖^2)
      (‖v‖^2 - (carryMeanQ v)^2 * ‖nativeCarry‖^2) := by
  have h := layer_energy_hasSum native v
  rwa [terminal_native, quotient_norm, nativeCarry_screen hv, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at h

theorem rh_iff_prime_quotient :
    RiemannHypothesis ↔ Tendsto (fun B => ‖(stage native B).mkQ qParity‖^2) atTop (𝓝 0) := by
  have h := quotient_tendsto native qParity
  rw [terminal_native] at h
  constructor
  · intro hr
    simpa only [q_terminal_parity_zero_iff_rh.mpr hr, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      using h
  · intro hr
    exact q_terminal_parity_zero_iff_rh.mp (norm_eq_zero.mp
      ((sq_eq_zero_iff).mp (tendsto_nhds_unique h hr)))

theorem rh_iff_prime_capture :
    RiemannHypothesis ↔ (∑' k, ‖(layer native k).starProjection qParity‖^2) =
      (3/4 : ℝ) * ((Real.log 2)⁻¹ - 1)^2 + 1/4 := by
  rw [(layer_energy_hasSum native qParity).tsum_eq, terminal_native, ← qParity_norm_sq]
  constructor
  · intro h
    rw [q_terminal_parity_zero_iff_rh.mpr h, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
  · intro h
    apply q_terminal_parity_zero_iff_rh.mp
    apply norm_eq_zero.mp
    nlinarith only [h, norm_nonneg (qMixed.mkQ qParity)]

/-- A second physical prime tower holds the Pareto carry itself fixed. -/
abbrev carryLine : Submodule ℝ QHilbert := ℝ ∙ transportedCarry

def removeCarry : QHilbert →L[ℝ] QHilbert := native - carryLine.starProjection

theorem carryLine_le_legal : carryLine ≤ physicalSpace closedSpace := by
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  change paretoEquiv (paretoEquiv.symm normalizedScreenedTwo) ∈ closedSpace
  rw [paretoEquiv.apply_symm_apply]
  exact screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure

theorem terminal_removeCarry :
    terminal removeCarry = physicalSpace closedSpace ⊓ carryLineᗮ := by
  let V := physicalSpace closedSpace
  have hu : transportedCarry ∈ V := by
    change paretoEquiv (paretoEquiv.symm normalizedScreenedTwo) ∈ closedSpace
    rw [paretoEquiv.apply_symm_apply]
    exact screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have hline : carryLine ≤ V := carryLine_le_legal
  have hclosed : IsClosed (V : Set QHilbert) :=
    (show IsClosed (closedSpace : Set ThresholdHilbert) from isClosed_closure).preimage
      paretoEquiv.continuous
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (hclosed.inter (Submodule.isClosed_orthogonal _))
    rintro _ ⟨m, hm, rfl⟩
    change m - carryLine.starProjection m ∈ V ⊓ carryLineᗮ
    exact ⟨V.sub_mem (mixedClosure_le_closedSpace hm)
      (hline (carryLine.starProjection_apply_mem _)),
      carryLine.sub_starProjection_mem_orthogonal _⟩
  · intro v hv
    apply Submodule.le_topologicalClosure
    have hm : v - carryMeanQ v • transportedCarry ∈ qMixed := by
      change paretoEquiv (v - carryMeanQ v • transportedCarry) ∈ mixedClosure
      apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).2
      rw [map_sub, map_smul]
      refine ⟨closedSpace.sub_mem hv.1 (closedSpace.smul_mem _ hu), ?_⟩
      rw [inner_sub_left, real_inner_smul_left]
      change carryMeanQ v - carryMeanQ v * carryMeanQ transportedCarry = 0
      rw [transportedCarry_mean, mul_one, sub_self]
    refine ⟨_, hm, ?_⟩
    have hv0 := carryLine.starProjection_apply_eq_zero_iff.mpr hv.2
    have hu1 := carryLine.starProjection_eq_self_iff.mpr
      (Submodule.subset_span (Set.mem_singleton transportedCarry) : transportedCarry ∈ carryLine)
    change (v - carryMeanQ v • transportedCarry) -
      carryLine.starProjection (v - carryMeanQ v • transportedCarry) = v
    rw [map_sub, map_smul, hv0, hu1]
    abel

/-- Complete Parseval for legal inputs with the Pareto scalar line held fixed in native Q. -/
theorem fixed_carry_parseval {v : QHilbert} (hv : v ∈ physicalSpace closedSpace) :
    HasSum (fun k => ‖(layer removeCarry k).starProjection v‖^2)
      (‖v‖^2 - ‖carryLine.starProjection v‖^2) := by
  have hA : v - carryLine.starProjection v ∈ terminal removeCarry := by
    rw [terminal_removeCarry]
    exact ⟨(physicalSpace closedSpace).sub_mem hv (carryLine_le_legal
      (carryLine.starProjection_apply_mem v)), carryLine.sub_starProjection_mem_orthogonal v⟩
  have hp : carryLine.starProjection v ∈ (terminal removeCarry)ᗮ := by
    intro z hz
    rw [terminal_removeCarry] at hz
    exact (real_inner_comm _ _).trans (hz.2 _ (carryLine.starProjection_apply_mem v))
  have he := (terminal removeCarry).starProjection_eq_self_iff.mpr hA
  rw [map_sub, (terminal removeCarry).starProjection_apply_eq_zero_iff.mpr hp, sub_zero] at he
  have h := layer_energy_hasSum removeCarry v
  rwa [quotient_norm, he, sub_sub_cancel] at h

/-- The constant valuation mode is in block zero; other modes are grouped by largest prime. -/
def valuationKey (d : ℕ+) : ℕ := (d : ℕ).primeFactors.sup id

theorem valuationKey_zero_iff (d : ℕ+) : valuationKey d = 0 ↔ (d : ℕ) = 1 := by
  constructor
  · intro h
    by_contra hn
    have hlt : 1 < (d : ℕ) := by have := d.pos; omega
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hlt
    have hle : p ≤ valuationKey d := Finset.le_sup (f := id) hp
    have hpos := (Nat.mem_primeFactors.mp hp).1.pos
    omega
  · intro h
    change (d : ℕ).primeFactors.sup id = 0
    simp [h]

/-- The ambient martingale block written in the normalized divisor Hilbert basis. -/
def valuationBlockVector (p : ℕ) (x : QHilbert) : QHilbert :=
  ∑' d : ↥(valuationKey ⁻¹' {p}),
    (QDivisorHilbert.divisorHilbertBasis.repr x d.val) • QDivisorHilbert.divisorHilbertBasis d.val

def valuationBlockEnergy (p : ℕ) (x : QHilbert) : ℝ :=
  ∑' d : ↥(valuationKey ⁻¹' {p}), (QDivisorHilbert.divisorHilbertBasis.repr x d.val)^2

/-- The full ambient tower reconstructs every Q vector, including all signed block vectors. -/
theorem valuation_reconstruction (x : QHilbert) :
    HasSum (fun p => valuationBlockVector p x) x :=
  (QDivisorHilbert.divisorHilbertBasis.hasSum_repr x).tsum_fiberwise valuationKey

/-- Ambient prime-block Parseval, with the constant coefficient included in block zero. -/
theorem valuation_parseval (x : QHilbert) :
    HasSum (fun p => valuationBlockEnergy p x) (‖x‖^2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
    (QDivisorHilbert.divisorHilbertBasis.repr x)
  have he : HasSum (fun d : ℕ+ => (QDivisorHilbert.divisorHilbertBasis.repr x d)^2) (‖x‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      LinearIsometryEquiv.norm_map] using h
  exact he.tsum_fiberwise valuationKey

end RiemannResearch.CategoryTheory.QPrimeParsevalTower

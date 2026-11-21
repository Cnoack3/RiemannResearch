import RiemannResearch.NumberTheory.DyadicAdditiveRigidity
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.IntegratedRamanujanBasis
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ResidueConductorVariation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reduction to one fully screened packet

I. Kátai, On additive functions (1978), equations (1.1) and (1.2),
https://doi.org/10.5486/PMD.1978.25.3-4.10, states the classical rigidity result
for additive functions with vanishing mean absolute adjacent differences,
and attributes the short-interval version to E. Wirsing. The dyadic case
is proved in DyadicAdditiveRigidity. Applied to mixed annihilators, it makes
the full-screened legal space one-dimensional and gives a fixed-seed test.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

theorem residuePairing_eq_log
    {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    ∃ c : ℝ, ∀ n : ℕ, 0 < n → residuePairing h n = c * Real.log (n : ℝ) := by
  apply RiemannResearch.NumberTheory.eq_log_of_coprime_additive_of_dyadic_variation
    (residuePairing h) _ (residuePairing_dyadic_variation_tendsto h)
  intro a b ha hb hc
  by_cases ha' : a = 1
  · subst a
    simp [residuePairing]
  by_cases hb' : b = 1
  · subst b
    simp [residuePairing]
  have ha1 : 1 < a := by omega
  have hb1 : 1 < b := by omega
  have hab : 1 < a * b := ha1.trans_le (Nat.le_mul_of_pos_right _ hb)
  simpa only [residuePairing, if_pos hab, if_pos ha1, if_pos hb1] using
    mixed_orthogonal_rawResidue_mul_of_coprime hh a b ha1 hb1 hc

private theorem packet_pairing_eq_of_residue_log {h : ThresholdHilbert} {c : ℝ}
    (hlog : ∀ n : ℕ, 0 < n → residuePairing h n = c * Real.log (n : ℝ))
    (q : ℕ) (hq : 1 < q) :
    inner ℝ (ramanujanPacketHilbert q) h = c * ArithmeticFunction.vonMangoldt q := by
  have hsrc (n : ℕ) (_hn : 0 < n) :
      (∑ d ∈ n.divisors, c * ArithmeticFunction.vonMangoldt d) = c * Real.log (n : ℝ) := by
    rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum]
  have hμ := (mobius_inversion (fun n => c * ArithmeticFunction.vonMangoldt n)
    (fun n => c * Real.log (n : ℝ))).mp hsrc q (by omega)
  rw [← hμ, ramanujanPacketHilbert_eq_divisor_sum q hq, sum_inner]
  calc
    _ = ∑ d ∈ q.divisors.filter (fun d => 1 < d),
        (ArithmeticFunction.moebius (q / d) : ℝ) * (c * Real.log (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      have he := hlog d (by omega)
      rw [residuePairing, if_pos hd'] at he
      rw [real_inner_smul_left, he]
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnd
      have hpos := Nat.pos_of_mem_divisors hd
      have hn : ¬ 1 < d := fun h => hnd (Finset.mem_filter.mpr ⟨hd, h⟩)
      have hd1 : d = 1 := by omega
      simp [hd1]

def normalizedScreenedTwo : ThresholdHilbert :=
  (Real.log 2)⁻¹ • limitScreenedPacket 2

theorem normalizedScreenedTwo_mean : inner ℝ normalizedScreenedTwo hilbertOne = 1 := by
  rw [normalizedScreenedTwo, real_inner_smul_left, limitScreenedPacket_inner_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  exact inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

theorem normalizedScreenedTwo_mem_screenedPrimeClosure :
    normalizedScreenedTwo ∈ screenedPrimeClosure :=
  screenedPrimeClosure.smul_mem _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨2, by norm_num, Nat.prime_two.isPrimePow⟩, rfl⟩))

theorem fullScreening_packet_eq_mangoldt_smul
    (q : ℕ) (hq : 1 < q) :
    fullScreening (ramanujanPacketHilbert q) =
      ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo := by
  let v := fullScreening (ramanujanPacketHilbert q) -
    ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo
  have hv : v ∈ mixedClosureᗮ :=
    mixedClosure.orthogonal.sub_mem (fullScreening_mem_orthogonal _)
      (mixedClosure.orthogonal.smul_mem _ (mixedClosure.orthogonal.smul_mem _
        (fullScreening_mem_orthogonal (ramanujanPacketHilbert 2))))
  obtain ⟨c, hc⟩ := residuePairing_eq_log hv
  have he : inner ℝ v v = 0 := by
    change inner ℝ (fullScreening (ramanujanPacketHilbert q) -
      ArithmeticFunction.vonMangoldt q • normalizedScreenedTwo) v = 0
    rw [inner_sub_left, real_inner_smul_left, normalizedScreenedTwo, real_inner_smul_left,
      ← fullScreening_packet, fullScreening_inner_right_of_orthogonal _ _ hv,
      fullScreening_inner_right_of_orthogonal _ _ hv, packet_pairing_eq_of_residue_log hc q hq,
      packet_pairing_eq_of_residue_log hc 2 (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp he)

theorem screenedPrimeClosure_eq_span_two :
    screenedPrimeClosure = Submodule.span ℝ {normalizedScreenedTwo} := by
  apply le_antisymm
  · unfold screenedPrimeClosure
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      change limitScreenedPacket q.val ∈ _
      rw [← fullScreening_packet,
        fullScreening_packet_eq_mangoldt_smul q.val q.property.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.closed_of_finiteDimensional _
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact normalizedScreenedTwo_mem_screenedPrimeClosure

theorem one_mem_closedSpace_iff_normalizedScreenedTwo
    :
    hilbertOne ∈ closedSpace ↔ normalizedScreenedTwo = hilbertOne := by
  rw [← one_mem_screenedPrimeClosure_iff, screenedPrimeClosure_eq_span_two]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    have he := congrArg (fun x : ThresholdHilbert => inner ℝ x hilbertOne) ha
    have ha' : a = 1 := by
      simpa only [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one,
        real_inner_self_eq_norm_sq, hilbertOne_norm_sq] using he
    simpa [ha'] using ha
  · intro h
    rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)

theorem riemannHypothesis_of_normalizedScreenedTwo (h : normalizedScreenedTwo = hilbertOne) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_one_mem_screenedPrimeClosure
  rw [← h]
  exact normalizedScreenedTwo_mem_screenedPrimeClosure

/-- On the legal closure, full screening keeps just the mean, in the
normalized direction of the screened conductor 2. -/
theorem fullScreening_eq_mean_smul {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    fullScreening x = inner ℝ x hilbertOne • normalizedScreenedTwo := by
  have hm := fullScreening_closedSpace_mem hx
  rw [screenedPrimeClosure_eq_span_two] at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hp := congrArg (fun z : ThresholdHilbert => inner ℝ z hilbertOne) ha
  have he : a = inner ℝ x hilbertOne := by
    simpa only [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one,
      fullScreening_inner_right_of_orthogonal x hilbertOne one_mem_mixedClosure_orthogonal]
      using hp
  rw [← ha, he]

theorem mem_mixedClosure_iff_mem_closedSpace_and_mean_zero (x : ThresholdHilbert) :
    x ∈ mixedClosure ↔ x ∈ closedSpace ∧ inner ℝ x hilbertOne = 0 := by
  constructor
  · intro hx
    exact ⟨mixedClosure_le_closedSpace hx,
      (mixedClosure.mem_orthogonal hilbertOne).mp one_mem_mixedClosure_orthogonal x hx⟩
  · rintro ⟨hx, hm⟩
    have hz := fullScreening_eq_mean_smul hx
    rw [hm, zero_smul] at hz
    change x - mixedClosure.starProjection x = 0 at hz
    rw [sub_eq_zero.mp hz]
    exact mixedClosure.starProjection_apply_mem _

/-- Every positive dilation acts trivially on the full legal mixed quotient. -/
theorem hilbertDilation_sub_self_mem_mixedClosure (m : ℕ) (hm : 0 < m)
    {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    hilbertDilation m hm x - x ∈ mixedClosure := by
  apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
  refine ⟨closedSpace.sub_mem (closedSpace_dilation hx m hm) hx, ?_⟩
  rw [inner_sub_left, hilbert_inner_one, hilbertDilation_mean, ← hilbert_inner_one, sub_self]

theorem fullScreening_hilbertDilation_eq (m : ℕ) (hm : 0 < m)
    {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    fullScreening (hilbertDilation m hm x) = fullScreening x := by
  rw [fullScreening_eq_mean_smul (closedSpace_dilation hx m hm), fullScreening_eq_mean_smul hx,
    hilbert_inner_one, hilbertDilation_mean, ← hilbert_inner_one]

theorem screenedPrimeClosure_eq_inf_orthogonal :
    screenedPrimeClosure = closedSpace ⊓ mixedClosureᗮ := by
  apply le_antisymm
  · apply le_inf screenedPrimeClosure_le_closedSpace
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      exact mixedClosure.sub_starProjection_mem_orthogonal _
    · exact mixedClosure.isClosed_orthogonal
  · intro x hx
    have he : fullScreening x = x := by
      change x - mixedClosure.starProjection x = x
      rw [(Submodule.starProjection_apply_eq_zero_iff _).mpr hx.2, sub_zero]
    rw [← he]
    exact fullScreening_closedSpace_mem hx.1

theorem mixed_sup_screenedPrimeClosure : mixedClosure ⊔ screenedPrimeClosure = closedSpace := by
  rw [screenedPrimeClosure_eq_inf_orthogonal]
  exact RiemannResearch.Analysis.NestedOrthogonalDecomposition.prime_sup_carry
    mixedClosure_le_closedSpace

theorem mixed_inf_screenedPrimeClosure : mixedClosure ⊓ screenedPrimeClosure = ⊥ := by
  rw [screenedPrimeClosure_eq_inf_orthogonal, inf_left_comm, Submodule.inf_orthogonal_eq_bot,
    inf_bot_eq]

/-- In the mixed split the algebraic span already contains its normalized generator. -/
theorem screenedPrimeSpan_eq_span_two :
    Submodule.span ℝ (Set.range fun q : {q : ℕ // 1 < q ∧ IsPrimePow q} =>
      limitScreenedPacket q.val) = Submodule.span ℝ {normalizedScreenedTwo} := by
  apply le_antisymm
  · rw [← screenedPrimeClosure_eq_span_two]
    exact Submodule.le_topologicalClosure _
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨2, by decide, Nat.prime_two.isPrimePow⟩, rfl⟩)

/-- The mean map in the mixed-conductor split exact sequence. -/
def legalPacketMean : closedSpace →L[ℝ] ℝ where
  toFun x := inner ℝ (x : ThresholdHilbert) hilbertOne
  map_add' _ _ := inner_add_left _ _ _
  map_smul' _ _ := real_inner_smul_left _ _ _
  cont := continuous_subtype_val.inner continuous_const

/-- A bounded linear section of the mean on the legal space. -/
def screenedMeanSection : ℝ →L[ℝ] closedSpace where
  toFun a := a • (⟨normalizedScreenedTwo,
    screenedPrimeClosure_le_closedSpace
      normalizedScreenedTwo_mem_screenedPrimeClosure⟩ : closedSpace)
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _
  cont := continuous_id.smul continuous_const

theorem legalPacketMean_comp_screenedMeanSection :
    legalPacketMean.comp screenedMeanSection = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro a
  change inner ℝ (a • normalizedScreenedTwo) hilbertOne = a
  rw [real_inner_smul_left, normalizedScreenedTwo_mean, mul_one]

theorem legalPacketMean_ker :
    legalPacketMean.ker = mixedClosure.comap closedSpace.subtype := by
  ext x
  change inner ℝ (x : ThresholdHilbert) hilbertOne = 0 ↔ (x : ThresholdHilbert) ∈ mixedClosure
  exact ⟨fun h => (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr ⟨x.property, h⟩,
    fun h => ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp h).2⟩

theorem mixed_orthogonal_eq_screened_sup_legal_orthogonal :
    mixedClosureᗮ = screenedPrimeClosure ⊔ closedSpaceᗮ := by
  have hVM : closedSpaceᗮ ≤ mixedClosureᗮ := by
    intro x hx m hm
    exact hx m (mixedClosure_le_closedSpace hm)
  have h := RiemannResearch.Analysis.NestedOrthogonalDecomposition.prime_sup_carry hVM
  rw [screenedPrimeClosure_eq_inf_orthogonal]
  simpa only [Submodule.orthogonal_orthogonal, inf_comm, sup_comm] using h.symm

/-- The constant and the screened line give two complements to the legal orthogonal
complement inside the mixed orthogonal complement. -/
theorem mixed_orthogonal_eq_target_sup_legal_orthogonal :
    mixedClosureᗮ = Submodule.span ℝ {hilbertOne} ⊔ closedSpaceᗮ := by
  apply le_antisymm
  · intro x hx
    let a := inner ℝ normalizedScreenedTwo x
    have hyM : x - a • hilbertOne ∈ mixedClosureᗮ :=
      mixedClosure.orthogonal.sub_mem hx
        (mixedClosure.orthogonal.smul_mem _ one_mem_mixedClosure_orthogonal)
    have hyU : inner ℝ normalizedScreenedTwo (x - a • hilbertOne) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, normalizedScreenedTwo_mean, mul_one]
      exact sub_self _
    have hyV : x - a • hilbertOne ∈ closedSpaceᗮ := by
      intro z hz
      rw [← mixed_sup_screenedPrimeClosure, screenedPrimeClosure_eq_span_two] at hz
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [inner_add_left, hyM m hm, real_inner_smul_left, hyU, mul_zero, add_zero]
    refine Submodule.mem_sup.mpr ⟨a • hilbertOne,
      Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, x - a • hilbertOne, hyV, ?_⟩
    abel
  · apply sup_le
    · apply Submodule.span_le.mpr
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact one_mem_mixedClosure_orthogonal
    · intro x hx m hm
      exact hx m (mixedClosure_le_closedSpace hm)

/-- The ambient orthogonal complement of the screened line contains the mixed packet at six. -/
theorem screened_sup_ambient_orthogonal_ne_mixed_orthogonal :
    screenedPrimeClosure ⊔ screenedPrimeClosureᗮ ≠ mixedClosureᗮ := by
  have h6 := mixed_packet_mem_closure 6 (by decide) (by decide)
  have hne : ramanujanPacketHilbert 6 ≠ 0 :=
    (finitePacket_independent 5).ne_zero (⟨4, by decide⟩ : Fin 5)
  have ho : ramanujanPacketHilbert 6 ∈ screenedPrimeClosureᗮ := by
    intro x hx
    rw [screenedPrimeClosure_eq_inf_orthogonal] at hx
    exact inner_eq_zero_symm.mp (hx.2 _ h6)
  intro he
  have hh : ramanujanPacketHilbert 6 ∈ mixedClosureᗮ :=
    he ▸ (show ramanujanPacketHilbert 6 ∈ screenedPrimeClosure ⊔ screenedPrimeClosureᗮ from
      (le_sup_right : screenedPrimeClosureᗮ ≤ screenedPrimeClosure ⊔ screenedPrimeClosureᗮ) ho)
  exact hne (inner_self_eq_zero.mp (hh _ h6))

/-- The proposed spanning condition is equivalent to asking the constant residual
to span the whole legal orthogonal complement. -/
theorem mixed_orthogonal_span_one_iff_residual_spans :
    mixedClosureᗮ = screenedPrimeClosure ⊔ Submodule.span ℝ {hilbertOne} ↔
      closedSpaceᗮ = Submodule.span ℝ {limitResidual} := by
  have hVM : closedSpaceᗮ ≤ mixedClosureᗮ :=
    fun _ hx m hm => hx m (mixedClosure_le_closedSpace hm)
  have hW : screenedPrimeClosure ≤ mixedClosureᗮ := by
    rw [screenedPrimeClosure_eq_inf_orthogonal]
    exact inf_le_right
  have hspan : Submodule.span ℝ {hilbertOne} ≤ mixedClosureᗮ :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr one_mem_mixedClosure_orthogonal)
  constructor
  · intro h
    apply le_antisymm _ (Submodule.span_le.mpr
      (Set.singleton_subset_iff.mpr limitResidual_mem_orthogonal))
    intro x hx
    have hxm := hVM hx
    rw [h] at hxm
    obtain ⟨w, hw, t, ht, he⟩ := Submodule.mem_sup.mp hxm
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    change a • (hilbertOne - closedSpace.starProjection hilbertOne) = x
    calc
      _ = (w + a • hilbertOne) - closedSpace.starProjection (w + a • hilbertOne) := by
        rw [map_add, map_smul,
          Submodule.starProjection_eq_self_iff.mpr (screenedPrimeClosure_le_closedSpace hw),
          smul_sub]
        abel
      _ = x := by rw [he, (Submodule.starProjection_apply_eq_zero_iff _).mpr hx, sub_zero]
  · intro h
    apply le_antisymm _ (sup_le hW hspan)
    rw [mixed_orthogonal_eq_screened_sup_legal_orthogonal, h]
    apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    have hPorth : limitProjection ∈ mixedClosureᗮ := by
      have hp := mixedClosure.orthogonal.sub_mem one_mem_mixedClosure_orthogonal
        (hVM limitResidual_mem_orthogonal)
      rw [limitResidual, sub_sub_cancel] at hp
      exact hp
    have hP : limitProjection ∈ screenedPrimeClosure := by
      rw [screenedPrimeClosure_eq_inf_orthogonal]
      exact ⟨closedSpace.starProjection_apply_mem _, hPorth⟩
    let S := screenedPrimeClosure ⊔ Submodule.span ℝ {hilbertOne}
    have hleft : screenedPrimeClosure ≤ S := le_sup_left
    have hright : Submodule.span ℝ {hilbertOne} ≤ S := le_sup_right
    exact S.sub_mem (hright (Submodule.subset_span (Set.mem_singleton _))) (hleft hP)

/-- The mean of the legal projection equals the mass captured from the unit target. -/
theorem limitProjection_inner_one :
    inner ℝ limitProjection hilbertOne = 1 - limitEnergy := by
  have h := limitResidual_inner_one
  rw [limitResidual, inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq] at h
  linarith

/-- The legal projection has the screened direction and squared projection norm as its scale. -/
theorem limitProjection_eq_scaled_screenedTwo :
    limitProjection = (1 - limitEnergy) • normalizedScreenedTwo := by
  have hmem : limitProjection ∈ closedSpace := closedSpace.starProjection_apply_mem _
  have ho : limitResidual ∈ mixedClosureᗮ :=
    fun m hm => limitResidual_mem_orthogonal m (mixedClosure_le_closedSpace hm)
  have hp : limitProjection ∈ mixedClosureᗮ := by
    have h := mixedClosure.orthogonal.sub_mem one_mem_mixedClosure_orthogonal ho
    rw [limitResidual, sub_sub_cancel] at h
    exact h
  have h := fullScreening_eq_mean_smul hmem
  change limitProjection - mixedClosure.starProjection limitProjection = _ at h
  rwa [(Submodule.starProjection_apply_eq_zero_iff _).mpr hp, sub_zero,
    limitProjection_inner_one] at h

instance : screenedPrimeClosure.HasOrthogonalProjection := by
  unfold screenedPrimeClosure
  infer_instance

theorem mixed_starProjection_screenedTwo :
    mixedClosure.starProjection normalizedScreenedTwo = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  have h := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at h
  exact h.2

theorem mixedOrthogonal_starProjection_one :
    mixedClosureᗮ.starProjection hilbertOne = hilbertOne :=
  Submodule.starProjection_eq_self_iff.mpr one_mem_mixedClosure_orthogonal

theorem screenedPrimeClosure_starProjection_one :
    screenedPrimeClosure.starProjection hilbertOne = limitProjection := by
  have hp : limitProjection ∈ screenedPrimeClosure := by
    rw [limitProjection_eq_scaled_screenedTwo]
    exact screenedPrimeClosure.smul_mem _ normalizedScreenedTwo_mem_screenedPrimeClosure
  have hr : hilbertOne - limitProjection ∈ screenedPrimeClosureᗮ :=
    fun v hv => limitResidual_mem_orthogonal v (screenedPrimeClosure_le_closedSpace hv)
  exact Submodule.eq_starProjection_of_mem_orthogonal hp hr

open RiemannResearch.Analysis.NestedOrthogonalDecomposition in
/-- On every ambient vector, screening the legal projection gives the projection
onto the screened legal line. -/
theorem mixedOrthogonal_starProjection_closedSpace (x : ThresholdHilbert) :
    mixedClosureᗮ.starProjection (closedSpace.starProjection x) =
      screenedPrimeClosure.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val,
    nested_projection_apply mixedClosure_le_closedSpace]
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [screenedPrimeClosure_eq_inf_orthogonal]
    exact projection_difference_mem mixedClosure_le_closedSpace x
  · rw [screenedPrimeClosure_eq_inf_orthogonal]
    exact sub_projection_difference_mem_orthogonal x

/-- Screening the legal projection of the constant recovers the constant
exactly when the legal residual vanishes. -/
theorem mixedOrthogonal_limitProjection_eq_one_iff :
    mixedClosureᗮ.starProjection limitProjection = hilbertOne ↔ limitEnergy = 0 := by
  rw [limitProjection, mixedOrthogonal_starProjection_closedSpace,
    screenedPrimeClosure_starProjection_one]
  exact Submodule.starProjection_eq_self_iff.trans limitEnergy_zero_iff_mem.symm

/-- The product is fixed by orthogonality and the exact mean of the screened packet. -/
theorem normalizedScreenedTwo_energy_product :
    (1 - limitEnergy) * ‖normalizedScreenedTwo‖ ^ 2 = 1 := by
  have hu := screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure
  have h := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hu
  rw [limitResidual, inner_sub_right, normalizedScreenedTwo_mean,
    limitProjection_eq_scaled_screenedTwo, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  linarith

/-- Positivity of the projection energy follows from the unit pairing alone. -/
theorem one_sub_limitEnergy_pos : 0 < 1 - limitEnergy := by
  by_contra! h
  have hprod := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg ‖normalizedScreenedTwo‖)
  rw [normalizedScreenedTwo_energy_product] at hprod
  exact (not_le_of_gt zero_lt_one) hprod

/-- The limiting fixed-seed error is the canonical legal projection error
rescaled by the squared norm of its projection. -/
theorem normalizedScreenedTwo_error_sq_eq_limitEnergy :
    ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 = limitEnergy / (1 - limitEnergy) := by
  apply (eq_div_iff one_sub_limitEnergy_pos.ne').mpr
  rw [norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq]
  nlinarith only [normalizedScreenedTwo_energy_product]

/-- Equality with the orthogonal projection already forces equality with the target. -/
theorem normalizedScreenedTwo_eq_limitProjection_iff :
    normalizedScreenedTwo = limitProjection ↔ normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    have he := limitResidual_inner_one
    rw [limitResidual, ← h, inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq,
      normalizedScreenedTwo_mean, sub_self] at he
    have herr := normalizedScreenedTwo_error_sq_eq_limitEnergy
    rw [← he, zero_div, pow_two, mul_eq_zero, or_self, norm_eq_zero, sub_eq_zero] at herr
    exact herr
  · intro h
    have hm := one_mem_closedSpace_iff_normalizedScreenedTwo.mpr h
    rw [h]
    exact (Submodule.starProjection_eq_self_iff.mpr hm).symm

/-- The prime input is fixed at conductor 2 while the mixed cutoff grows. -/
def fixedTwoTrial (M : ℕ) : ThresholdHilbert :=
  (Real.log 2)⁻¹ • screenedPacket (Finset.Icc 2 M) 2

theorem fixedTwoTrial_tendsto :
    Tendsto fixedTwoTrial atTop (𝓝 normalizedScreenedTwo) :=
  (screenedPacket_tendsto 2).const_smul (Real.log 2)⁻¹

theorem fixedTwoTrial_tendsto_one_iff :
    Tendsto fixedTwoTrial atTop (𝓝 hilbertOne) ↔ hilbertOne ∈ closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  exact ⟨tendsto_nhds_unique fixedTwoTrial_tendsto, fun h => h ▸ fixedTwoTrial_tendsto⟩

theorem ramanujanPacketHilbert_two_norm_sq :
    ‖ramanujanPacketHilbert 2‖ ^ 2 = Real.log 2 := by
  rw [hilbert_norm_weighted_sq, hilbertSequence_ramanujanPacketHilbert]
  have hs (n : ℕ) : ramanujanPacket 2 n ^ 2 = ramanujanPacket 2 n := by
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    have hn := Nat.mod_lt n (by norm_num : 0 < 2)
    have he : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases he with h | h <;> norm_num [residue, h]
  simp_rw [hs]
  change paretoMean (ramanujanPacket 2) = _
  rw [paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]

private theorem fixedTwo_error_eq_capture (K : Submodule ℝ ThresholdHilbert)
    [K.HasOrthogonalProjection] (hK : hilbertOne ∈ Kᗮ) :
    ‖hilbertOne - (Real.log 2)⁻¹ •
      (ramanujanPacketHilbert 2 - K.starProjection (ramanujanPacketHilbert 2))‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 - ‖K.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) /
        (Real.log 2) ^ 2 := by
  let z := ramanujanPacketHilbert 2
  let p := K.starProjection z
  have hp : p ∈ K := K.starProjection_apply_mem z
  have ho : z - p ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal z
  have hzp : inner ℝ z p = ‖p‖ ^ 2 := by
    have h := (K.mem_orthogonal _).mp ho p hp
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero] at h
    rwa [real_inner_comm]
  have hzmean : inner ℝ z hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num only [Nat.cast_ofNat]
  have hpmean : inner ℝ p hilbertOne = 0 := (K.mem_orthogonal _).mp hK p hp
  have hnorm : ‖z - p‖ ^ 2 = Real.log 2 - ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real, hzp, ramanujanPacketHilbert_two_norm_sq]
    ring
  change ‖hilbertOne - (Real.log 2)⁻¹ • (z - p)‖ ^ 2 =
    (Real.log 2 - (Real.log 2) ^ 2 - ‖p‖ ^ 2) / (Real.log 2) ^ 2
  have hmean : inner ℝ hilbertOne (z - p) = Real.log 2 := by
    rw [real_inner_comm, inner_sub_left, hzmean, hpmean, sub_zero]
  rw [norm_sub_sq_real, hilbertOne_norm_sq, real_inner_smul_right, hmean,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

theorem fixedTwoTrial_error_eq_capture (M : ℕ) :
    ‖hilbertOne - fixedTwoTrial M‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 -
        ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2) /
        (Real.log 2) ^ 2 :=
  fixedTwo_error_eq_capture _ (one_mem_mixed_orthogonal _)

theorem full_capture_saturation_iff :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
        Real.log 2 - (Real.log 2) ^ 2 ↔ hilbertOne ∈ closedSpace := by
  have he : ‖hilbertOne - normalizedScreenedTwo‖ ^ 2 =
      (Real.log 2 - (Real.log 2) ^ 2 -
        ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) / (Real.log 2) ^ 2 :=
    fixedTwo_error_eq_capture _ one_mem_mixedClosure_orthogonal
  have hn := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    rw [h, sub_self, zero_div] at he
    rw [pow_two, mul_eq_zero, or_self] at he
    exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm
  · intro h
    rw [h, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at he
    exact (sub_eq_zero.mp ((div_eq_zero_iff.mp he.symm).resolve_right (pow_ne_zero _ hn))).symm

theorem fixed_capture_tendsto_saturation_iff :
    Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) ↔ hilbertOne ∈ closedSpace := by
  have hmono : Monotone (fun M : ℕ => mixedSpace (Finset.Icc 2 M)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  have h := (Submodule.starProjection_tendsto_closure_iSup
    (fun M => mixedSpace (Finset.Icc 2 M)) hmono (ramanujanPacketHilbert 2)).norm.pow 2
  rw [← full_capture_saturation_iff]
  exact ⟨tendsto_nhds_unique h, fun he => he ▸ h⟩

theorem fixed_capture_tendsto_saturation_iff_naturalApproximation :
    Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) ↔ BaezDuarte.NaturalApproximation :=
  fixed_capture_tendsto_saturation_iff.trans BaezDuarte.naturalApproximation_iff_one_mem.symm

theorem riemannHypothesis_of_fixed_capture_saturation
    (h : Tendsto (fun M : ℕ =>
      ‖(mixedSpace (Finset.Icc 2 M)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2)
      atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2))) : RiemannHypothesis :=
  riemannHypothesis_of_one_mem_screenedPrimeClosure
    (one_mem_screenedPrimeClosure_iff.mpr (fixed_capture_tendsto_saturation_iff.mp h))

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PsiNormalizedRamanujan
open PrimePowerSchur RiemannResearch.LinearAlgebra

theorem fullScreening_centeredInput (N : ℕ) :
    fullScreening (centeredInput N) =
      Chebyshev.psi (N : ℝ) • (normalizedScreenedTwo - hilbertOne) := by
  have hp : fullScreening (primeCombination (window N) (fun _ => 1)) =
      Chebyshev.psi (N : ℝ) • normalizedScreenedTwo := by
    unfold primeCombination finiteSchurCombination
    simp only [one_smul, map_sum]
    rw [← prime_source_eq_psi, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro q _
    exact fullScreening_packet_eq_mangoldt_smul q.val (by
      have h := (Finset.mem_Icc.mp (Finset.mem_filter.mp q.property).1).1
      omega)
  rw [centeredInput, map_sub, map_smul, fullScreening_one, hp, smul_sub]

theorem fullCovarianceMass_eq_fixed_error (N : ℕ) :
    fullCovarianceMass N =
      (Chebyshev.psi (N : ℝ)) ^ 2 * ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [fullCovarianceMass, fullScreening_centeredInput, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem fullCovarianceMass_normalized_tendsto_fixed_error
    :
    Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop
      (𝓝 (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)) := by
  have h : Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) / (N : ℝ)) ^ 2 *
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2) atTop
      (𝓝 (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)) := by
    simpa only [one_pow, one_mul] using
      (psi_div_nat_tendsto.pow 2).mul_const (‖normalizedScreenedTwo - hilbertOne‖ ^ 2)
  apply h.congr
  intro N
  rw [fullCovarianceMass_eq_fixed_error N, div_pow]
  ring

theorem fullCovarianceMass_subquadratic_iff_one_mem :
    Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop (𝓝 0) ↔
      hilbertOne ∈ CoefficientStabilization.closedSpace := by
  rw [one_mem_closedSpace_iff_normalizedScreenedTwo]
  constructor
  · intro h
    have he := tendsto_nhds_unique fullCovarianceMass_normalized_tendsto_fixed_error h
    rw [pow_two, mul_eq_zero, or_self] at he
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  · intro h
    simpa only [h, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      fullCovarianceMass_normalized_tendsto_fixed_error

theorem riemannHypothesis_of_fullCovarianceMass_subquadratic
    (h : Tendsto (fun N => fullCovarianceMass N / (N : ℝ) ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (fullCovarianceMass_subquadratic_iff_one_mem.mp h))

theorem covarianceMass_eq_fixed_error_add_diagonal_tail (N : ℕ) :
    covarianceMass N =
      (Chebyshev.psi (N : ℝ)) ^ 2 *
          (CoefficientStabilization.limitEnergy / (1 - CoefficientStabilization.limitEnergy)) +
        ‖mixedClosure.starProjection (centeredInput N) -
          (mixedSpace (Finset.Icc 2 N)).starProjection (centeredInput N)‖ ^ 2 := by
  rw [← offDiagonalCovarianceMass_diagonal, offDiagonalCovarianceMass_split,
    fullCovarianceMass_eq_fixed_error, normalizedScreenedTwo_error_sq_eq_limitEnergy]

end RiemannResearch.RH.Pareto.PsiNormalizedRamanujan

import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.MixedConductorCovariance
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedConductorSpanCriterion
import RiemannResearch.RH.ParetoAnnihilatorOneSided
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.ThresholdContractiveRepair
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.Linarith

/-!
# The Pareto mean on the orthogonal complement of the mixed packets

Christian Noack's *The Von-Mangoldt Pattern*, §§2–3 (22 November 2026), motivates
comparing the Pareto mean with the scalar in the packet pairings. Their Riesz
vectors on the mixed complement are the constant and the normalized screened
packet. The restricted mean is onto, and its injectivity is equivalent to the
constant belonging to the closed residue span.

Every mixed-orthogonal vector bounded on either side is constant. The proof
uses the Pareto dilation adjoints and the one-sided mean estimate for legal
annihilators. The final implication from a real-line bound on the kernel uses
the repository's independent Mellin functionals at conjugate right-hand zeros.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

open CoefficientStabilization

/-- The Pareto mean on the full ambient orthogonal complement of the mixed packets. -/
def mixedOrthogonalMean : mixedClosureᗮ →L[ℝ] ℝ :=
  hilbertMeanContinuous.comp mixedClosureᗮ.subtypeL

/-- The constant realizes every scalar as a mean on the mixed complement. -/
theorem mixedOrthogonalMean_surjective : Function.Surjective mixedOrthogonalMean := by
  intro a
  refine ⟨⟨a • hilbertOne, mixedClosureᗮ.smul_mem a one_mem_mixedClosure_orthogonal⟩, ?_⟩
  change hilbertMeanContinuous (a • hilbertOne) = a
  simp

/-- The quotient by the ambient restricted kernel is a real line. -/
def mixedOrthogonalMeanQuotient :
    (mixedClosureᗮ ⧸ mixedOrthogonalMean.ker) ≃ₗ[ℝ] ℝ :=
  mixedOrthogonalMean.toLinearMap.quotKerEquivOfSurjective mixedOrthogonalMean_surjective

/-- The scalar multiplying the von Mangoldt pattern on the ambient mixed complement. -/
def mixedPacketCoefficient : mixedClosureᗮ →L[ℝ] ℝ :=
  (innerSL ℝ normalizedScreenedTwo).comp mixedClosureᗮ.subtypeL

theorem packet_pairing_eq_mixedPacketCoefficient (q : ℕ) (hq : 1 < q) (h : mixedClosureᗮ) :
    inner ℝ (ramanujanPacketHilbert q) (h : ThresholdHilbert) =
      ArithmeticFunction.vonMangoldt q * mixedPacketCoefficient h := by
  change _ = ArithmeticFunction.vonMangoldt q * inner ℝ normalizedScreenedTwo (h : ThresholdHilbert)
  rw [← fullScreening_inner_right_of_orthogonal (ramanujanPacketHilbert q) _ h.property,
    fullScreening_packet_eq_mangoldt_smul q hq, real_inner_smul_left]

/-- With the draft convention, the discrepancy represents the difference of the two functionals. -/
theorem mixedOrthogonalMean_sub_packetCoefficient (h : mixedClosureᗮ) :
    mixedOrthogonalMean h - mixedPacketCoefficient h =
      inner ℝ (hilbertOne - normalizedScreenedTwo) (h : ThresholdHilbert) := by
  rw [inner_sub_left]
  rfl

/-- The kernel consists of the vectors of the mixed complement perpendicular to the constant. -/
theorem mixedOrthogonalMean_ker :
    mixedOrthogonalMean.ker = (Submodule.span ℝ {hilbertOne})ᗮ.comap mixedClosureᗮ.subtype := by
  rw [← CenteredMeanSnake.meanZero_eq_orthogonal]
  rfl

/-- Subtracting the constant with the same mean preserves mixed orthogonality. -/
theorem center_mem_mixedOrthogonal_kernel {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    CenteredMeanSnake.center h ∈ mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ := by
  refine ⟨mixedClosureᗮ.sub_mem hh (mixedClosureᗮ.smul_mem _ one_mem_mixedClosure_orthogonal), ?_⟩
  rw [← CenteredMeanSnake.meanZero_eq_orthogonal]
  exact CenteredMeanSnake.center_mem h

/-- Splitting off the constant inside the mixed complement leaves its ambient mean-zero part.
The second summand is orthogonal to the whole first summand. -/
theorem mixedOrthogonal_split_at_one :
    mixedClosureᗮ = Submodule.span ℝ {hilbertOne} ⊔
      (mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ) := by
  apply le_antisymm
  · intro h hh
    refine Submodule.mem_sup.mpr
      ⟨hilbertMeanContinuous h • hilbertOne, Submodule.mem_span_singleton.mpr ⟨_, rfl⟩,
        CenteredMeanSnake.center h, center_mem_mixedOrthogonal_kernel hh, ?_⟩
    rw [CenteredMeanSnake.center_apply, add_comm, sub_add_cancel]
  · exact sup_le
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr one_mem_mixedClosure_orthogonal))
      inf_le_left

private theorem mean_injOn_span_of_mean_one {v : ThresholdHilbert}
    (hv : hilbertMeanContinuous v = 1) :
    Set.InjOn hilbertMeanContinuous (Submodule.span ℝ {v} : Set ThresholdHilbert) := by
  intro x hx y hy hxy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hab : a = b := by simpa [hv] using hxy
  rw [hab]

/-- On the legal part of the mixed complement the mean is injective unconditionally. -/
theorem mean_injOn_legal_mixedOrthogonal :
    Set.InjOn hilbertMeanContinuous
      ((closedSpace ⊓ mixedClosureᗮ : Submodule ℝ ThresholdHilbert) : Set ThresholdHilbert) := by
  rw [← screenedPrimeClosure_eq_inf_orthogonal, screenedPrimeClosure_eq_span_two]
  exact mean_injOn_span_of_mean_one ((real_inner_comm _ _).trans normalizedScreenedTwo_mean)

/-- On the entire mixed complement, injectivity is equivalent to the constant spanning it. -/
theorem mixedOrthogonalMean_injective_iff_span_one :
    Function.Injective mixedOrthogonalMean ↔ mixedClosureᗮ = Submodule.span ℝ {hilbertOne} := by
  constructor
  · intro hinj
    apply le_antisymm
    · intro h hh
      let c := hilbertMeanContinuous h
      have he : (⟨h, hh⟩ : mixedClosureᗮ) =
          ⟨c • hilbertOne, mixedClosureᗮ.smul_mem _ one_mem_mixedClosure_orthogonal⟩ := by
        apply hinj
        change c = hilbertMeanContinuous (c • hilbertOne)
        simp
      exact Submodule.mem_span_singleton.mpr ⟨c, (congrArg Subtype.val he).symm⟩
    · apply Submodule.span_le.mpr
      rintro _ rfl
      exact one_mem_mixedClosure_orthogonal
  · intro hspan x y hxy
    apply Subtype.ext
    apply mean_injOn_span_of_mean_one (v := hilbertOne) (by simp)
    · rw [← hspan]
      exact x.property
    · rw [← hspan]
      exact y.property
    · exact hxy

/-- The converse uses density of the residue space once the constant belongs to it. -/
theorem mixedOrthogonal_eq_span_one_iff_one_mem :
    mixedClosureᗮ = Submodule.span ℝ {hilbertOne} ↔ hilbertOne ∈ closedSpace := by
  calc
    mixedClosureᗮ = Submodule.span ℝ {hilbertOne} ↔
        mixedClosure = (Submodule.span ℝ {hilbertOne})ᗮ := by
      constructor <;> intro he <;>
        simpa only [Submodule.orthogonal_orthogonal] using
          congrArg (fun K : Submodule ℝ ThresholdHilbert => Kᗮ) he
    _ ↔ hilbertOne ∈ closedSpace :=
      CenteredMeanSnake.closedSpace_eq_top_iff_mixedClosure_eq_one_orthogonal.symm.trans
        closedSpace_eq_top_iff_one_mem

/-- Injectivity on the mixed complement is equivalent to vanishing of the draft's discrepancy. -/
theorem mixedOrthogonalMean_injective_iff_discrepancy_zero :
    Function.Injective mixedOrthogonalMean ↔ hilbertOne - normalizedScreenedTwo = 0 := by
  rw [mixedOrthogonalMean_injective_iff_span_one, mixedOrthogonal_eq_span_one_iff_one_mem,
    one_mem_closedSpace_iff_normalizedScreenedTwo, sub_eq_zero]
  exact eq_comm

/-- Vanishing of the intersection of the two ambient orthogonal complements is exactly
vanishing of the discrepancy. -/
theorem mixedOrthogonal_inf_oneOrthogonal_eq_bot_iff_discrepancy_zero :
    mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ = ⊥ ↔
      hilbertOne - normalizedScreenedTwo = 0 := by
  calc
    _ ↔ mixedClosureᗮ = Submodule.span ℝ {hilbertOne} := by
      constructor
      · intro hK
        simpa only [hK, sup_bot_eq] using mixedOrthogonal_split_at_one
      · intro hspan
        rw [hspan, Submodule.inf_orthogonal_eq_bot]
    _ ↔ _ := mixedOrthogonalMean_injective_iff_span_one.symm.trans
      mixedOrthogonalMean_injective_iff_discrepancy_zero

/-- Injectivity of the ambient restricted mean suffices for RH. -/
theorem riemannHypothesis_of_mixedOrthogonalMean_injective
    (hinj : Function.Injective mixedOrthogonalMean) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo
    (sub_eq_zero.mp (mixedOrthogonalMean_injective_iff_discrepancy_zero.mp hinj)).symm

/-- Every mixed-orthogonal vector bounded above or below on the positive sites equals its mean. -/
theorem mixedOrthogonal_eq_mean_smul_one_of_oneSidedBound {h : ThresholdHilbert}
    (hh : h ∈ mixedClosureᗮ)
    (hb : (∃ B : ℝ, ∀ n : ℕ, 0 < n → hilbertSequence h n ≤ B) ∨
      (∃ B : ℝ, ∀ n : ℕ, 0 < n → B ≤ hilbertSequence h n)) :
    h = hilbertMeanContinuous h • hilbertOne := by
  rw [mixed_orthogonal_eq_target_sup_legal_orthogonal] at hh
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hh
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hsite (n : ℕ) (hn : 0 < n) :
      hilbertSequence (a • hilbertOne + z) n = a + hilbertSequence z n := by
    simp [zeroAnchor, hn.ne']
  have hz0 : z = 0 := by
    rcases hb with ⟨B, hB⟩ | ⟨B, hB⟩
    · apply annihilator_eq_zero_of_upper_bound z hz
      refine ⟨B - a, fun n hn => ?_⟩
      have he := hB n hn
      rw [hsite n hn] at he
      linarith
    · apply neg_eq_zero.mp
      apply annihilator_eq_zero_of_upper_bound (-z) (closedSpaceᗮ.neg_mem hz)
      refine ⟨a - B, fun n hn => ?_⟩
      have he := hB n hn
      rw [hsite n hn] at he
      change hilbertSequenceLinear (-z) n ≤ _
      rw [map_neg, Pi.neg_apply]
      change -hilbertSequence z n ≤ a - B
      linarith
  simp [hz0]

/-- Mean-zero vectors in the ambient mixed orthogonal complement. -/
abbrev ambientMixedMeanKernel : Submodule ℝ ThresholdHilbert :=
  mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ

/-- Remove the component along the constant detected by the screened packet.
On the ambient mixed complement the result annihilates the whole legal space. -/
def subtractPacketCoefficient : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ normalizedScreenedTwo).smulRight hilbertOne

private theorem subtractPacketCoefficient_mem {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    subtractPacketCoefficient h ∈ closedSpaceᗮ := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (mixed_orthogonal_eq_target_sup_legal_orthogonal ▸ hh)
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have huz : inner ℝ normalizedScreenedTwo z = 0 :=
    hz _ (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
  change a • hilbertOne + z - inner ℝ normalizedScreenedTwo (a • hilbertOne + z) • hilbertOne ∈ _
  simpa only [inner_add_right, real_inner_smul_right, normalizedScreenedTwo_mean, huz,
    mul_one, add_zero, add_sub_cancel_left] using hz

/-- Centering by the Pareto mean is a continuous linear equivalence from the
legal annihilator onto the mean-zero part of the ambient mixed complement. -/
def legalOrthogonalEquivMeanZeroMixed :
    closedSpaceᗮ ≃L[ℝ] ambientMixedMeanKernel := by
  let f : closedSpaceᗮ →L[ℝ] ambientMixedMeanKernel :=
    (CenteredMeanSnake.center.comp closedSpaceᗮ.subtypeL).codRestrict ambientMixedMeanKernel
      fun z => center_mem_mixedOrthogonal_kernel fun m hm =>
        z.property m (mixedClosure_le_closedSpace hm)
  let g : ambientMixedMeanKernel →L[ℝ] closedSpaceᗮ :=
    (subtractPacketCoefficient.comp ambientMixedMeanKernel.subtypeL).codRestrict closedSpaceᗮ
      fun y => subtractPacketCoefficient_mem y.property.1
  refine { toFun := f, invFun := g, map_add' := f.map_add, map_smul' := f.map_smul,
           continuous_toFun := f.continuous, continuous_invFun := g.continuous,
           left_inv := ?_, right_inv := ?_ }
  · intro z
    apply Subtype.ext
    have huz : inner ℝ normalizedScreenedTwo (z : ThresholdHilbert) = 0 :=
      z.property _
        (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
    change (z : ThresholdHilbert) - hilbertMeanContinuous z • hilbertOne -
      inner ℝ normalizedScreenedTwo
        ((z : ThresholdHilbert) - hilbertMeanContinuous z • hilbertOne) • hilbertOne = z
    simp only [inner_sub_right, real_inner_smul_right, huz, normalizedScreenedTwo_mean,
      mul_one, zero_sub, neg_smul, sub_neg_eq_add, sub_add_cancel]
  · intro y
    apply Subtype.ext
    have hy : hilbertMeanContinuous (y : ThresholdHilbert) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property.2
    change (y : ThresholdHilbert) - inner ℝ normalizedScreenedTwo y • hilbertOne -
      hilbertMeanContinuous
        ((y : ThresholdHilbert) - inner ℝ normalizedScreenedTwo y • hilbertOne) • hilbertOne = y
    simp [hy]

@[simp] theorem legalOrthogonalEquivMeanZeroMixed_apply (z : closedSpaceᗮ) :
    (legalOrthogonalEquivMeanZeroMixed z : ThresholdHilbert) =
      (z : ThresholdHilbert) - hilbertMeanContinuous z • hilbertOne := rfl

@[simp] theorem legalOrthogonalEquivMeanZeroMixed_symm_apply
    (y : ambientMixedMeanKernel) :
    (legalOrthogonalEquivMeanZeroMixed.symm y : ThresholdHilbert) =
      (y : ThresholdHilbert) - inner ℝ normalizedScreenedTwo y • hilbertOne := rfl

/-- The inverse adds exactly the squared packet coefficient to the input energy. -/
theorem legalOrthogonalEquivMeanZeroMixed_symm_norm_sq
    (y : ambientMixedMeanKernel) :
    ‖legalOrthogonalEquivMeanZeroMixed.symm y‖ ^ 2 =
      ‖y‖ ^ 2 + (inner ℝ normalizedScreenedTwo (y : ThresholdHilbert)) ^ 2 := by
  have hy : inner ℝ (y : ThresholdHilbert) hilbertOne = 0 :=
    (real_inner_comm _ _).trans (Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property.2)
  change ‖(y : ThresholdHilbert) - inner ℝ normalizedScreenedTwo y • hilbertOne‖ ^ 2 = _
  rw [norm_sub_sq_real, real_inner_smul_right, hy, mul_zero, mul_zero, sub_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq, mul_one]
  simp

/-- Vanishing of either space under the centering equivalence is equivalent to
vanishing of the other, with no finite-dimensionality assumption. -/
theorem ambientMixedMeanKernel_eq_bot_iff_legalOrthogonal_eq_bot :
    ambientMixedMeanKernel = ⊥ ↔ closedSpaceᗮ = ⊥ := by
  have transport {U W : Submodule ℝ ThresholdHilbert} (e : U ≃L[ℝ] W) (hW : W = ⊥) :
      U = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    let z : U := ⟨x, hx⟩
    have hy : (e z : ThresholdHilbert) = 0 := by simpa using hW.le (e z).property
    have he : e z = 0 := Subtype.ext hy
    change x = 0
    exact congrArg Subtype.val (e.injective (he.trans e.map_zero.symm))
  exact ⟨transport legalOrthogonalEquivMeanZeroMixed,
    transport legalOrthogonalEquivMeanZeroMixed.symm⟩

/-- Even containment of the mean-zero part in one real line suffices for RH.
The inverse of the centering equivalence carries the containing line into a line. -/
theorem riemannHypothesis_of_mixedOrthogonal_meanZero_le_line (v : ThresholdHilbert)
    (hker : mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ ≤ Submodule.span ℝ {v}) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.ParetoComplementTransfer.riemannHypothesis_of_pareto_complement_le_line
    (subtractPacketCoefficient v)
  intro z hz
  let y := legalOrthogonalEquivMeanZeroMixed ⟨z, hz⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hker y.property)
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  calc
    a • subtractPacketCoefficient v = subtractPacketCoefficient (a • v) :=
      (subtractPacketCoefficient.map_smul a v).symm
    _ = subtractPacketCoefficient y := congrArg subtractPacketCoefficient ha
    _ = z := congrArg Subtype.val (legalOrthogonalEquivMeanZeroMixed.symm_apply_apply ⟨z, hz⟩)

end RiemannResearch.RH.Pareto.PrimePowerSchur

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

/-- Even containment of the mean-zero part in one real line suffices for RH.
Centering embeds the legal annihilator in that part. Subtraction of the packet
coefficient recovers the original annihilator and carries a line into a line. -/
theorem riemannHypothesis_of_mixedOrthogonal_meanZero_le_line (v : ThresholdHilbert)
    (hker : mixedClosureᗮ ⊓ (Submodule.span ℝ {hilbertOne})ᗮ ≤ Submodule.span ℝ {v}) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.ParetoComplementTransfer.riemannHypothesis_of_pareto_complement_le_line
    (v - inner ℝ normalizedScreenedTwo v • hilbertOne)
  intro z hz
  have hzM : z ∈ mixedClosureᗮ := fun m hm => hz m (mixedClosure_le_closedSpace hm)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hker (center_mem_mixedOrthogonal_kernel hzM))
  change a • v = z - hilbertMeanContinuous z • hilbertOne at ha
  have huz : inner ℝ normalizedScreenedTwo z = 0 :=
    hz _ (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
  have hcoef := congrArg (fun x : ThresholdHilbert => inner ℝ normalizedScreenedTwo x) ha
  change inner ℝ normalizedScreenedTwo (a • v) =
    inner ℝ normalizedScreenedTwo (z - hilbertMeanContinuous z • hilbertOne) at hcoef
  simp only [real_inner_smul_right, inner_sub_right, huz, normalizedScreenedTwo_mean,
    mul_one, zero_sub] at hcoef
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  rw [smul_sub, smul_smul, hcoef, neg_smul, sub_neg_eq_add, ha, sub_add_cancel]

end RiemannResearch.RH.Pareto.PrimePowerSchur

import RiemannResearch.RH.MixedConductorSquareZero
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Ring.Opposite

/-!
# The mixed Pareto space as a bimodule over the screened legal algebra

Both regular products with a mixed vector act by the scalar mean. The actions
therefore factor through the augmentation quotient. The regular module sequence
has no module-linear section, although the mean has a continuous real-linear
section and its scalar quotient has a real-algebra section.

For the underlying module idealization see D. D. Anderson and M. Winders,
*Idealization of a module*, J. Commut. Algebra 1 (2009), 3–56.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra
open CoefficientStabilization
open scoped LegalMeanAlgebra

scoped instance mixedLeftModule : Module closedSpace mixedClosure :=
  Module.compHom mixedClosure meanHom.toRingHom

scoped instance mixedRightModule : Module closedSpaceᵐᵒᵖ mixedClosure :=
  Module.compHom mixedClosure (meanHom.toRingHom.fromOpposite fun _ _ => mul_comm _ _)

@[simp] theorem mixedLeft_smul (v : closedSpace) (m : mixedClosure) :
    v • m = legalPacketMean v • m := rfl

@[simp] theorem mixedRight_smul (v : closedSpaceᵐᵒᵖ) (m : mixedClosure) :
    v • m = legalPacketMean v.unop • m := rfl

scoped instance mixedActionsCommute : SMulCommClass closedSpace closedSpaceᵐᵒᵖ mixedClosure :=
  ⟨fun x y m => smul_comm (legalPacketMean x) (legalPacketMean y.unop) m⟩

scoped instance mixedLeftContinuous : ContinuousSMul closedSpace mixedClosure :=
  ⟨(legalPacketMean.continuous.comp continuous_fst).smul continuous_snd⟩

scoped instance mixedRightContinuous : ContinuousSMul closedSpaceᵐᵒᵖ mixedClosure :=
  ⟨((legalPacketMean.continuous.comp MulOpposite.continuous_unop).comp continuous_fst).smul
    continuous_snd⟩

scoped instance mixedRealTower : IsScalarTower ℝ closedSpace mixedClosure where
  smul_assoc t v m := by
    change legalPacketMean (t • v) • m = t • (legalPacketMean v • m)
    rw [map_smul, smul_eq_mul, mul_smul]

scoped instance mixedRealRightTower : IsScalarTower ℝ closedSpaceᵐᵒᵖ mixedClosure where
  smul_assoc t v m := by
    change legalPacketMean (t • v.unop) • m = t • (legalPacketMean v.unop • m)
    rw [map_smul, smul_eq_mul, mul_smul]

theorem mixed_smul_norm (v : closedSpace) (m : mixedClosure) :
    ‖v • m‖ = |legalPacketMean v| * ‖m‖ := by rw [mixedLeft_smul, norm_smul, Real.norm_eq_abs]

/-- Both sides of the bimodule structure come from the original multiplication on legal vectors. -/
theorem legalMixedInclusion_left (v : closedSpace) (m : mixedClosure) :
    legalMixedInclusion (v • m) = v * legalMixedInclusion m := by
  rw [mixedLeft_smul, map_smul, mul_def, mulWith, legalPacketMean_legalMixedInclusion]
  simp

theorem legalMixedInclusion_right (m : mixedClosure) (v : closedSpace) :
    legalMixedInclusion (MulOpposite.op v • m) = legalMixedInclusion m * v := by
  rw [mul_comm]
  exact legalMixedInclusion_left v m

/-- Changing the lift used for the product preserves multiplication on either side of the ideal. -/
theorem mulWith_mixed_actions (e v : closedSpace) (m : mixedClosure) :
    mulWith e v (legalMixedInclusion m) = legalMixedInclusion (v • m) ∧
    mulWith e (legalMixedInclusion m) v = legalMixedInclusion (MulOpposite.op v • m) := by
  simp [mulWith]

/-- The physical mixed subspace and the augmentation ideal agree as modules over the legal ring. -/
def mixedIdealModuleEquiv : mixedClosure ≃ₗ[closedSpace] mixedIdeal where
  toFun m := ⟨legalMixedInclusion m, (mem_mixedIdeal _).2 m.property⟩
  invFun x := ⟨x.val.val, (mem_mixedIdeal _).1 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' v m := Subtype.ext (legalMixedInclusion_left v m)

scoped instance mixedQuotientLeftModule : Module (closedSpace ⧸ mixedIdeal) mixedClosure :=
  Module.compHom mixedClosure quotientEquiv.toRingEquiv.toRingHom

scoped instance mixedQuotientRightModule : Module (closedSpace ⧸ mixedIdeal)ᵐᵒᵖ mixedClosure :=
  Module.compHom mixedClosure
    (quotientEquiv.toRingEquiv.toRingHom.fromOpposite fun _ _ => mul_comm _ _)

scoped instance mixedQuotientActionsCommute :
    SMulCommClass (closedSpace ⧸ mixedIdeal) (closedSpace ⧸ mixedIdeal)ᵐᵒᵖ mixedClosure :=
  ⟨fun x y m => smul_comm (quotientEquiv x) (quotientEquiv y.unop) m⟩

private theorem continuous_mixedQuotientScalar : Continuous quotientEquiv :=
  quotientHomeomorph.continuous_toFun

scoped instance mixedQuotientLeftContinuous :
    ContinuousSMul (closedSpace ⧸ mixedIdeal) mixedClosure :=
  ⟨(continuous_mixedQuotientScalar.comp continuous_fst).smul continuous_snd⟩

scoped instance mixedQuotientRightContinuous :
    ContinuousSMul (closedSpace ⧸ mixedIdeal)ᵐᵒᵖ mixedClosure :=
  ⟨((continuous_mixedQuotientScalar.comp MulOpposite.continuous_unop).comp continuous_fst).smul
    continuous_snd⟩

/-- Passage to the quotient preserves both actions, on the same physical mixed vector. -/
theorem mixedQuotient_actions (x : closedSpace) (m : mixedClosure) :
    Ideal.Quotient.mk mixedIdeal x • m = x • m ∧
    MulOpposite.op (Ideal.Quotient.mk mixedIdeal x) • m = MulOpposite.op x • m :=
  ⟨rfl, rfl⟩

theorem mixedIdeal_isTwoSided : mixedIdeal.IsTwoSided := inferInstance

private theorem inclusion_injective : Function.Injective legalMixedInclusion :=
  fun _ _ h => Subtype.ext (congrArg (fun v : closedSpace => (v : ThresholdHilbert)) h)

/-- The kernel of either scalar action is precisely the mixed ideal. The conductor-six
packet witnesses that the mixed module is nonzero. -/
theorem mixedLeft_annihilator (v : closedSpace) :
    (∀ m : mixedClosure, v • m = 0) ↔ v ∈ mixedIdeal := by
  constructor
  · intro h
    let m : mixedClosure := ⟨ramanujanPacketHilbert 6,
      mixed_packet_mem_closure 6 (by decide) (by decide)⟩
    have hm : m ≠ 0 := fun he =>
      ((finitePacket_independent 5).ne_zero (⟨4, by decide⟩ : Fin 5))
        (congrArg Subtype.val he)
    exact (smul_eq_zero.mp (show legalPacketMean v • m = 0 from h m)).resolve_right hm
  · intro hv m
    change legalPacketMean v = 0 at hv
    rw [mixedLeft_smul, hv, zero_smul]

theorem mixedRight_annihilator (v : closedSpace) :
    (∀ m : mixedClosure, MulOpposite.op v • m = 0) ↔ v ∈ mixedIdeal :=
  mixedLeft_annihilator v

/-- The regular-module exact sequence is the kernel sequence of the quotient projection. -/
theorem regularMean_shortExact :
    mixedIdeal.mkQ.shortComplexKer.ShortExact :=
  LinearMap.shortExact_shortComplexKer mixedIdeal.mkQ_surjective

/-- Any legal-module map back from the quotient lands in the mixed ideal. -/
theorem quotientLinearMap_mem_mixedIdeal
    (s : (closedSpace ⧸ mixedIdeal) →ₗ[closedSpace] closedSpace)
    (q : closedSpace ⧸ mixedIdeal) : s q ∈ mixedIdeal := by
  apply (mixedLeft_annihilator (s q)).mp
  intro m
  apply inclusion_injective
  rw [map_zero, legalMixedInclusion_left, mul_comm]
  change legalMixedInclusion m • s q = 0
  rw [← s.map_smul]
  have hz : legalMixedInclusion m • q = 0 := by
    obtain ⟨v, rfl⟩ := mixedIdeal.mkQ_surjective q
    rw [← mixedIdeal.mkQ.map_smul]
    apply (Submodule.Quotient.mk_eq_zero mixedIdeal).2
    change legalMixedInclusion m * v ∈ mixedIdeal
    rw [mul_comm]
    exact mixedIdeal.smul_mem v ((mem_mixedIdeal _).2 m.property)
  rw [hz, map_zero]

/-- The real-linear splitting cannot be upgraded to a splitting of the regular module sequence. -/
theorem regularMean_no_linear_section :
    ¬ ∃ s : (closedSpace ⧸ mixedIdeal) →ₗ[closedSpace] closedSpace,
      mixedIdeal.mkQ.comp s = LinearMap.id := by
  rintro ⟨s, hs⟩
  have he : mixedIdeal.mkQ (s 1) = 1 := DFunLike.congr_fun hs 1
  have hz : mixedIdeal.mkQ (s 1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (quotientLinearMap_mem_mixedIdeal s 1)
  exact one_ne_zero (he.symm.trans hz)

end RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra

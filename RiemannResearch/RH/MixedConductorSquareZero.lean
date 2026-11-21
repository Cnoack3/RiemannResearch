import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MixedConductorMetricLifting
import RiemannResearch.RH.MeanOneSix
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# The square-zero algebra of the screened legal mean

Opening the scope `RiemannResearch.RH.Pareto.PrimePowerSchur.LegalMeanAlgebra`
equips the existing real topological vector space with the product belonging to
the screened section. Its ideal is the mixed-conductor mean kernel.
The coordinate model is the idealization in D. D. Anderson and M. Winders,
*Idealization of a module*, J. Commut. Algebra 1 (2009), 3–56,
https://doi.org/10.1216/JCA-2009-1-1-3. For the Hilbert minimum used in the
naturality argument see E. Kreyszig, *Introductory Functional Analysis with
Applications*, Theorem 6.2-5. All statements below use the physical Pareto norm.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
namespace LegalMeanAlgebra

/-- The product for a proposed lift of the scalar one. -/
def mulWith (e x y : closedSpace) : closedSpace :=
  legalPacketMean x • y + legalPacketMean y • x -
    (legalPacketMean x * legalPacketMean y) • e

theorem mean_mulWith {e : closedSpace} (he : legalPacketMean e = 1) (x y : closedSpace) :
    legalPacketMean (mulWith e x y) = legalPacketMean x * legalPacketMean y := by
  simp only [mulWith, map_sub, map_add, map_smul, smul_eq_mul, he, mul_one]
  ring

theorem mulWith_assoc {e : closedSpace} (he : legalPacketMean e = 1) (x y z : closedSpace) :
    mulWith e (mulWith e x y) z = mulWith e x (mulWith e y z) := by
  simp only [mulWith, map_sub, map_add, map_smul, smul_eq_mul, he]
  module

theorem mulWith_comm (e x y : closedSpace) : mulWith e x y = mulWith e y x := by
  unfold mulWith
  module

theorem mulWith_unit {e : closedSpace} (he : legalPacketMean e = 1) (x : closedSpace) :
    mulWith e e x = x := by simp [mulWith, he]

theorem mulWith_add (e x y z : closedSpace) :
    mulWith e x (y + z) = mulWith e x y + mulWith e x z := by
  simp only [mulWith, map_add]
  module

theorem mulWith_smul (e : closedSpace) (a : ℝ) (x y : closedSpace) :
    mulWith e x (a • y) = a • mulWith e x y := by
  simp only [mulWith, map_smul, smul_eq_mul]
  module

theorem mulWith_zero (e x : closedSpace) : mulWith e x 0 = 0 := by simp [mulWith]

/-- Fixing the unit and requiring the kernel to have zero products determines every
bilinear product, even before imposing associativity or commutativity. -/
theorem mulWith_unique {e : closedSpace} (he : legalPacketMean e = 1)
    (B : closedSpace →ₗ[ℝ] closedSpace →ₗ[ℝ] closedSpace)
    (hL : ∀ v, B e v = v) (hR : ∀ v, B v e = v)
    (hker : ∀ m n, legalPacketMean m = 0 → legalPacketMean n = 0 → B m n = 0)
    (x y : closedSpace) : B x y = mulWith e x y := by
  have h0 (v : closedSpace) : legalPacketMean (v - legalPacketMean v • e) = 0 := by
    simp [he]
  calc
    B x y = B (x - legalPacketMean x • e) (y - legalPacketMean y • e) + mulWith e x y := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hL, hR, mulWith]
      module
    _ = mulWith e x y := by rw [hker _ _ (h0 x) (h0 y), zero_add]

theorem continuous_mulWith (e : closedSpace) :
    Continuous (fun p : closedSpace × closedSpace => mulWith e p.1 p.2) :=
  (((legalPacketMean.continuous.comp continuous_fst).smul continuous_snd).add
    ((legalPacketMean.continuous.comp continuous_snd).smul continuous_fst)).sub
    (((legalPacketMean.continuous.comp continuous_fst).mul
      (legalPacketMean.continuous.comp continuous_snd)).smul continuous_const)

/-- The screened product on the original additive group of legal vectors. -/
scoped instance screenedCommRing : CommRing closedSpace where
  __ := (inferInstance : AddCommGroup closedSpace)
  one := screenedMeanSection 1
  mul := mulWith (screenedMeanSection 1)
  mul_assoc := mulWith_assoc (legalPacketMean_screenedMeanSection 1)
  mul_comm := mulWith_comm _
  one_mul := mulWith_unit (legalPacketMean_screenedMeanSection 1)
  mul_one x := (mulWith_comm _ _ _).trans (mulWith_unit (legalPacketMean_screenedMeanSection 1) x)
  left_distrib := mulWith_add _
  right_distrib x y z := by
    change mulWith _ (x + y) z = mulWith _ x z + mulWith _ y z
    rw [mulWith_comm _ (x + y), mulWith_add, mulWith_comm _ z x, mulWith_comm _ z y]
  mul_zero := mulWith_zero _
  zero_mul x := (mulWith_comm _ _ _).trans (mulWith_zero _ x)

theorem mul_def (x y : closedSpace) : x * y = mulWith (screenedMeanSection 1) x y := rfl

/-- The algebra uses the original scalar action and embeds a real via its screened section. -/
scoped instance screenedAlgebra : Algebra ℝ closedSpace :=
  Algebra.ofModule
    (fun a x y => by rw [mul_comm, mul_def, mulWith_smul, ← mul_def, mul_comm y x])
    (mulWith_smul _)

@[simp] theorem algebraMap_apply (a : ℝ) :
    algebraMap ℝ closedSpace a = screenedMeanSection a := by
  change a • screenedMeanSection 1 = screenedMeanSection a
  simpa using (screenedMeanSection.map_smul a (1 : ℝ)).symm

scoped instance screenedTopologicalRing : IsTopologicalRing closedSpace where
  continuous_mul := continuous_mulWith _

/-- The original continuous mean as a unital algebra homomorphism. -/
def meanHom : closedSpace →ₐ[ℝ] ℝ :=
  AlgHom.ofLinearMap legalPacketMean.toLinearMap (legalPacketMean_screenedMeanSection 1)
    (mean_mulWith (legalPacketMean_screenedMeanSection 1))

@[simp] theorem meanHom_apply (x : closedSpace) : meanHom x = legalPacketMean x := rfl

/-- The mean-zero ideal of the screened algebra, expressed on the legal space. -/
def mixedIdeal : Ideal closedSpace := RingHom.ker meanHom

theorem mem_mixedIdeal (x : closedSpace) :
    x ∈ mixedIdeal ↔ (x : ThresholdHilbert) ∈ mixedClosure := by
  change x ∈ legalPacketMean.ker ↔ _
  rw [legalPacketMean_ker]
  rfl

theorem mul_eq_zero_of_mem {x y : closedSpace} (hx : x ∈ mixedIdeal) (hy : y ∈ mixedIdeal) :
    x * y = 0 := by
  change legalPacketMean x = 0 at hx
  change legalPacketMean y = 0 at hy
  simp [mul_def, mulWith, hx, hy]

@[simp] theorem mixedIdeal_sq : mixedIdeal ^ 2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, Ideal.mul_le, Ideal.mem_bot]
  exact fun _ hx _ hy => mul_eq_zero_of_mem hx hy

instance mixedIdeal_isMaximal : mixedIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective meanHom
    (fun a => ⟨screenedMeanSection a, legalPacketMean_screenedMeanSection a⟩)

/-- The usual quotient field structure coming from maximality of the mixed ideal. -/
noncomputable abbrev quotientField : Field (closedSpace ⧸ mixedIdeal) :=
  Ideal.Quotient.field _

/-- The first isomorphism theorem, using the screened right inverse. -/
def quotientEquiv : (closedSpace ⧸ mixedIdeal) ≃ₐ[ℝ] ℝ :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := meanHom) (g := screenedMeanSection)
    legalPacketMean_screenedMeanSection

@[simp] theorem quotientEquiv_mk (x : closedSpace) :
    quotientEquiv (Ideal.Quotient.mk mixedIdeal x) = legalPacketMean x := rfl

@[simp] theorem quotientEquiv_symm_apply (a : ℝ) :
    quotientEquiv.symm a = Ideal.Quotient.mk mixedIdeal (screenedMeanSection a) := rfl

/-- Every mean-one splitting induces this same multiplication on the quotient. -/
theorem quotient_mk_mulWith {e : closedSpace} (he : legalPacketMean e = 1) (x y : closedSpace) :
    Ideal.Quotient.mk mixedIdeal (mulWith e x y) =
      Ideal.Quotient.mk mixedIdeal x * Ideal.Quotient.mk mixedIdeal y := by
  apply quotientEquiv.injective
  simp only [map_mul, quotientEquiv_mk, mean_mulWith he]

/-- The same quotient identification respects the Hilbert quotient topology. -/
def quotientHomeomorph : (closedSpace ⧸ mixedIdeal) ≃ₜ ℝ where
  __ := quotientEquiv.toEquiv
  continuous_toFun :=
    (QuotientRing.isOpenQuotientMap_mk mixedIdeal).isQuotientMap.continuous_iff.2
      legalPacketMean.continuous
  continuous_invFun :=
    (QuotientRing.isOpenQuotientMap_mk mixedIdeal).continuous.comp screenedMeanSection.continuous

/-- Both the algebra quotient and the categorical cokernel send the class of a vector to its mean. -/
theorem quotientEquiv_agrees_cokernel (x : closedSpace) :
    quotientEquiv (Ideal.Quotient.mk mixedIdeal x) =
      legalMixedQuotientIso.hom (TopModuleCat.cokerπ legalMeanComplex.f x) :=
  (CategoryTheory.ConcreteCategory.congr_hom legalMixedQuotientIso_π x).symm

private theorem retraction_inclusion (m : mixedClosure) :
    legalMixedRetraction (legalMixedInclusion m) = m :=
  CategoryTheory.ConcreteCategory.congr_hom legalMeanSplitting.f_r m

private theorem retraction_section (a : ℝ) :
    legalMixedRetraction (screenedMeanSection a) = 0 :=
  CategoryTheory.ConcreteCategory.congr_hom legalMeanSplitting.s_r a

/-- In the coordinates of the categorical splitting the algebra is mathlib's idealization.
The two components are the actual mean and the mixed retraction. -/
def splitCoordinates : closedSpace ≃ₐ[ℝ] TrivSqZeroExt ℝ mixedClosure where
  toFun x := (legalPacketMean x, legalMixedRetraction x)
  invFun z := legalMixedInclusion z.snd + screenedMeanSection z.fst
  left_inv x := by
    change legalMixedInclusion (legalMixedRetraction x) + screenedMeanSection (legalPacketMean x) = x
    rw [legalMixedInclusion_legalMixedRetraction, sub_add_cancel]
  right_inv z := by
    apply TrivSqZeroExt.ext
    · change legalPacketMean (legalMixedInclusion z.snd + screenedMeanSection z.fst) = z.fst
      simp
    · change legalMixedRetraction (legalMixedInclusion z.snd + screenedMeanSection z.fst) = z.snd
      simp [retraction_inclusion, retraction_section]
  map_add' x y := TrivSqZeroExt.ext (map_add legalPacketMean x y) (map_add legalMixedRetraction x y)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact mean_mulWith (legalPacketMean_screenedMeanSection 1) x y
    · change legalMixedRetraction (mulWith (screenedMeanSection 1) x y) =
        legalPacketMean x • legalMixedRetraction y +
          MulOpposite.op (legalPacketMean y) • legalMixedRetraction x
      simp [mulWith, op_smul_eq_smul, retraction_section]
  commutes' a := by
    rw [algebraMap_apply]
    exact TrivSqZeroExt.ext (legalPacketMean_screenedMeanSection a) (retraction_section a)

theorem splitCoordinates_continuous :
    Continuous (fun x : closedSpace =>
      ((splitCoordinates x).fst, (splitCoordinates x).snd)) :=
  legalPacketMean.continuous.prodMk legalMixedRetraction.continuous

theorem splitCoordinates_symm_continuous :
    Continuous (fun z : ℝ × mixedClosure => splitCoordinates.symm (z.1, z.2)) :=
  (legalMixedInclusion.continuous.comp continuous_snd).add
    (screenedMeanSection.continuous.comp continuous_fst)

/-- The shear between two sections on the original Hilbert space. -/
def changeUnit (e f : closedSpace) : closedSpace →L[ℝ] closedSpace :=
  ContinuousLinearMap.id ℝ closedSpace + legalPacketMean.smulRight (f - e)

theorem changeUnit_apply (e f x : closedSpace) :
    changeUnit e f x = x + legalPacketMean x • (f - e) := rfl

theorem mean_changeUnit {e f : closedSpace} (he : legalPacketMean e = 1)
    (hf : legalPacketMean f = 1) (x : closedSpace) :
    legalPacketMean (changeUnit e f x) = legalPacketMean x := by
  simp [changeUnit_apply, he, hf]

theorem changeUnit_unit {e : closedSpace} (he : legalPacketMean e = 1) (f : closedSpace) :
    changeUnit e f e = f := by rw [changeUnit_apply, he, one_smul]; abel

theorem changeUnit_fixed {x : closedSpace} (hx : x ∈ mixedIdeal) (e f : closedSpace) :
    changeUnit e f x = x := by
  change legalPacketMean x = 0 at hx
  simp [changeUnit_apply, hx]

theorem changeUnit_cancel {e f : closedSpace} (he : legalPacketMean e = 1)
    (hf : legalPacketMean f = 1) (x : closedSpace) : changeUnit f e (changeUnit e f x) = x := by
  rw [changeUnit_apply f e, mean_changeUnit he hf, changeUnit_apply]
  module

/-- The inverse of the shear interchanges the two units. -/
def changeUnitEquiv {e f : closedSpace} (he : legalPacketMean e = 1)
    (hf : legalPacketMean f = 1) : closedSpace ≃L[ℝ] closedSpace where
  toLinearEquiv := { (changeUnit e f).toLinearMap with
    invFun := changeUnit f e
    left_inv := changeUnit_cancel he hf
    right_inv := changeUnit_cancel hf he }
  continuous_toFun := (changeUnit e f).continuous
  continuous_invFun := (changeUnit f e).continuous

/-- A linear map over the scalar quotient transports the product to the image unit. -/
theorem map_mulWith {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : F →ₗ[ℝ] ℝ) (T : closedSpace →ₗ[ℝ] F) (hT : ∀ x, D (T x) = legalPacketMean x)
    (e x y : closedSpace) :
    T (mulWith e x y) = D (T x) • T y + D (T y) • T x - (D (T x) * D (T y)) • T e := by
  simp only [mulWith, hT, map_sub, map_add, map_smul]

/-- Changing the splitting gives isomorphic products by a map inducing the identity on
both the mixed ideal and the scalar quotient. -/
theorem changeUnit_mul {e f : closedSpace} (he : legalPacketMean e = 1)
    (hf : legalPacketMean f = 1) (x y : closedSpace) :
    changeUnitEquiv he hf (mulWith e x y) =
      mulWith f (changeUnitEquiv he hf x) (changeUnitEquiv he hf y) := by
  change changeUnit e f (mulWith e x y) = mulWith f (changeUnit e f x) (changeUnit e f y)
  simp only [mulWith, map_sub, map_add, map_smul, mean_changeUnit he hf, changeUnit_unit he]

private theorem coe_screenedUnit :
    (screenedMeanSection 1 : ThresholdHilbert) = normalizedScreenedTwo := one_smul _ _

/-- Pythagoras on the physical mean-one fiber, with the entire mixed remainder. -/
theorem meanOne_pythagoras {x : closedSpace} (hx : legalPacketMean x = 1) :
    ‖x‖ ^ 2 = ‖screenedMeanSection 1‖ ^ 2 + ‖x - screenedMeanSection 1‖ ^ 2 := by
  have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
  rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
  have hm : (x : ThresholdHilbert) - normalizedScreenedTwo ∈ mixedClosure := by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).2
    exact ⟨closedSpace.sub_mem x.property hu.1, by
      rw [inner_sub_left, normalizedScreenedTwo_mean]
      exact sub_eq_zero.mpr hx⟩
  have ho := (mixedClosure.mem_orthogonal _).mp hu.2 _ hm
  rw [inner_sub_left, real_inner_self_eq_norm_sq, sub_eq_zero] at ho
  change ‖(x : ThresholdHilbert)‖ ^ 2 =
    ‖(screenedMeanSection 1 : ThresholdHilbert)‖ ^ 2 +
      ‖(x : ThresholdHilbert) - (screenedMeanSection 1 : ThresholdHilbert)‖ ^ 2
  rw [coe_screenedUnit, norm_sub_sq_real, ho]
  ring

/-- The point of minimum norm in the mean-one fiber is unique. -/
theorem eq_screenedUnit_of_norm_le {x : closedSpace} (hx : legalPacketMean x = 1)
    (hn : ‖x‖ ≤ ‖screenedMeanSection 1‖) : x = screenedMeanSection 1 := by
  have hp := meanOne_pythagoras hx
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have hz : ‖x - screenedMeanSection 1‖ ^ 2 = 0 :=
    le_antisymm (by linarith only [hp, h]) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa using hz))

/-- Equality in the operator-norm minimum determines the whole right inverse. -/
theorem eq_screenedSection_of_norm_le (s : ℝ →L[ℝ] closedSpace)
    (hs : legalPacketMean.comp s = ContinuousLinearMap.id ℝ ℝ)
    (hn : ‖s‖ ≤ ‖screenedMeanSection‖) : s = screenedMeanSection := by
  have h1 : s 1 = screenedMeanSection 1 := by
    apply eq_screenedUnit_of_norm_le (DFunLike.congr_fun hs (1 : ℝ))
    calc
      ‖s 1‖ ≤ ‖s‖ := by simpa using s.le_opNorm (1 : ℝ)
      _ ≤ ‖screenedMeanSection‖ := hn
      _ = ‖screenedMeanSection 1‖ := by
        change ‖screenedMeanSection‖ = ‖(screenedMeanSection 1 : ThresholdHilbert)‖
        rw [norm_screenedMeanSection, coe_screenedUnit]
  apply ContinuousLinearMap.ext
  intro a
  calc
    s a = a • s 1 := by simpa using s.map_smul a (1 : ℝ)
    _ = a • screenedMeanSection 1 := by rw [h1]
    _ = screenedMeanSection a := by simpa using (screenedMeanSection.map_smul a (1 : ℝ)).symm

/-- A surjective linear isometry over the scalar quotient carries the screened unit
to the target's unique minimum-norm lift. The target can be a different space. -/
theorem screenedUnit_natural {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : F →L[ℝ] ℝ) (T : closedSpace ≃ₗᵢ[ℝ] F)
    (hT : ∀ x, D (T x) = legalPacketMean x) {v : F} (hv : D v = 1)
    (hmin : ∀ z, D z = 1 → ‖z‖ ≤ ‖v‖ → z = v) : T (screenedMeanSection 1) = v := by
  apply hmin _ ((hT _).trans (legalPacketMean_screenedMeanSection 1))
  have hx : legalPacketMean (T.symm v) = 1 := by rw [← hT, T.apply_symm_apply, hv]
  have h := legalPacketMean_fiber_bound (T.symm v)
  rw [hx, abs_one, one_mul, T.symm.norm_map] at h
  rw [T.norm_map]
  change ‖(screenedMeanSection 1 : ThresholdHilbert)‖ ≤ ‖v‖
  rwa [coe_screenedUnit]

/-- Every automorphism of the Hilbert space preserving the mean and norm
preserves the screened product. -/
theorem isometry_mul (T : closedSpace ≃ₗᵢ[ℝ] closedSpace)
    (hT : ∀ x, legalPacketMean (T x) = legalPacketMean x) (x y : closedSpace) :
    T (x * y) = T x * T y := by
  have h1 := screenedUnit_natural legalPacketMean T hT (legalPacketMean_screenedMeanSection 1)
    (fun _ hx hn => eq_screenedUnit_of_norm_le hx hn)
  simp only [mul_def, mulWith, map_sub, map_add, map_smul, hT, h1]

/-- The conductor-six packet as an element of the mixed ideal inside the legal space. -/
def packetSix : closedSpace :=
  legalMixedInclusion ⟨ramanujanPacketHilbert 6, mixed_packet_mem_closure 6 (by decide) (by decide)⟩

/-- The screened square vanishes. The actual packet has first value minus one,
so its arithmetic pointwise square has first value one. -/
theorem packetSix_square_test :
    packetSix * packetSix = 0 ∧ hilbertSequence (packetSix : ThresholdHilbert) 1 = -1 := by
  constructor
  · have hm : packetSix ∈ mixedIdeal := (mem_mixedIdeal _).2
      (mixed_packet_mem_closure 6 (by decide) (by decide))
    exact mul_eq_zero_of_mem hm hm
  · change hilbertSequence (ramanujanPacketHilbert 6) 1 = -1
    rw [hilbertSequence_ramanujanPacketHilbert, MeanOneSix.packet_six_residue]
    norm_num [residue]

/-- The underlying topological exact sequence admits a shear that acts identically on both
end terms and moves the screened unit. -/
theorem exists_shear_moving_unit :
    ∃ T : closedSpace ≃L[ℝ] closedSpace, (∀ x, legalPacketMean (T x) = legalPacketMean x) ∧
      (∀ x ∈ mixedIdeal, T x = x) ∧ T 1 ≠ 1 := by
  have he : legalPacketMean (1 : closedSpace) = 1 := legalPacketMean_screenedMeanSection 1
  have h6 : legalPacketMean packetSix = 0 := legalPacketMean_legalMixedInclusion _
  have hf : legalPacketMean ((1 : closedSpace) + packetSix) = 1 := by rw [map_add, he, h6, add_zero]
  refine ⟨changeUnitEquiv he hf, mean_changeUnit he hf, fun _ hx => changeUnit_fixed hx _ _, ?_⟩
  change changeUnit (1 : closedSpace) (1 + packetSix) 1 ≠ 1
  rw [changeUnit_unit he]
  intro h
  have hz : packetSix = 0 := add_left_cancel (h.trans (add_zero (1 : closedSpace)).symm)
  have hz' : ramanujanPacketHilbert 6 = 0 := congrArg (fun x : closedSpace => (x : ThresholdHilbert)) hz
  exact ((finitePacket_independent 5).ne_zero (⟨4, by decide⟩ : Fin 5)) hz'

/-- The square-zero algebra's unit retains the full physical error from the ambient constant. -/
theorem unit_error_sq :
    ‖((1 : closedSpace) : ThresholdHilbert) - hilbertOne‖ ^ 2 =
      limitEnergy / (1 - limitEnergy) := by
  change ‖(screenedMeanSection 1 : ThresholdHilbert) - hilbertOne‖ ^ 2 = _
  rw [coe_screenedUnit]
  exact normalizedScreenedTwo_error_sq_eq_limitEnergy

end LegalMeanAlgebra
end RiemannResearch.RH.Pareto.PrimePowerSchur

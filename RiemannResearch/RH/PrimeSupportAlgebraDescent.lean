import RiemannResearch.CategoryTheory.SquarefreeResidueCRT
import RiemannResearch.RH.CenteredMeanLongExact
import RiemannResearch.RH.MixedConductorPrimeSupport
import RiemannResearch.RH.MixedConductorSquareZero
import RiemannResearch.RH.MixedConductorBimodule
import RiemannResearch.RH.PrimeSupportParityDescent
import RiemannResearch.RH.QRamanujanContrastGram
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Algebra descent along the prime-support tower

In the screened square-zero algebra `V`, the closed span of the mixed packets
with at most `n` distinct prime factors is an ideal `Iₙ`. Quotienting gives a
direct system of real algebras. Compatible continuous maps to a Hausdorff
algebra descend uniquely through `V/M` by density of the stages in `M`.

The connecting map pulled back to each algebra quotient carries its unit to
the same class `[u - 1_H]`. The last theorem identifies it with the descended
parity class of the ambient quotient tower.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open CoefficientStabilization LegalMeanAlgebra CenteredMeanSnake
open scoped LegalMeanAlgebra

private abbrev legalSupport (n : ℕ) : Submodule ℝ closedSpace :=
  (supportSpace n).map legalMixedInclusion.toLinearMap

/-- A mixed vector multiplies any legal vector by its scalar mean. This makes
every real support subspace in the mixed ideal an ideal of the screened algebra. -/
def supportIdeal (n : ℕ) : Ideal closedSpace where
  carrier := (legalSupport n : Set closedSpace)
  zero_mem' := (legalSupport n).zero_mem
  add_mem' := (legalSupport n).add_mem
  smul_mem' a x := by
    rintro ⟨m, hm, rfl⟩
    change a * legalMixedInclusion m ∈ legalSupport n
    rw [mul_def, mulWith, legalPacketMean_legalMixedInclusion]
    simpa using (legalSupport n).smul_mem (legalPacketMean a)
      (show legalMixedInclusion m ∈ legalSupport n from ⟨m, hm, rfl⟩)

theorem supportIdeal_mono : Monotone supportIdeal := by
  intro n k hn
  exact Submodule.map_mono (supportSpace_mono hn)

theorem supportIdeal_le_mixed (n : ℕ) : supportIdeal n ≤ mixedIdeal := by
  rintro x ⟨m, _, rfl⟩
  exact legalPacketMean_legalMixedInclusion m

theorem supportIdeal_sq (n : ℕ) : supportIdeal n ^ 2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, Ideal.mul_le, Ideal.mem_bot]
  exact fun _ hx _ hy =>
    mul_eq_zero_of_mem (supportIdeal_le_mixed n hx) (supportIdeal_le_mixed n hy)

/-- The scalar by which a class in the support quotient acts on the physical mixed space. -/
def supportScalar (n : ℕ) : (closedSpace ⧸ supportIdeal n) →ₐ[ℝ] ℝ :=
  quotientEquiv.toAlgHom.comp (Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n))

theorem continuous_supportScalar (n : ℕ) : Continuous (supportScalar n) :=
  (QuotientRing.isOpenQuotientMap_mk (supportIdeal n)).isQuotientMap.continuous_iff.2
    legalPacketMean.continuous

scoped instance supportLeftModule (n : ℕ) : Module (closedSpace ⧸ supportIdeal n) mixedClosure :=
  Module.compHom mixedClosure (supportScalar n).toRingHom

scoped instance supportRightModule (n : ℕ) :
    Module (closedSpace ⧸ supportIdeal n)ᵐᵒᵖ mixedClosure :=
  Module.compHom mixedClosure
    ((supportScalar n).toRingHom.fromOpposite fun _ _ => mul_comm _ _)

scoped instance supportActionsCommute (n : ℕ) :
    SMulCommClass (closedSpace ⧸ supportIdeal n) (closedSpace ⧸ supportIdeal n)ᵐᵒᵖ mixedClosure :=
  ⟨fun x y m => smul_comm (supportScalar n x) (supportScalar n y.unop) m⟩

scoped instance supportLeftContinuous (n : ℕ) :
    ContinuousSMul (closedSpace ⧸ supportIdeal n) mixedClosure :=
  ⟨((continuous_supportScalar n).comp continuous_fst).smul continuous_snd⟩

scoped instance supportRightContinuous (n : ℕ) :
    ContinuousSMul (closedSpace ⧸ supportIdeal n)ᵐᵒᵖ mixedClosure :=
  ⟨(((continuous_supportScalar n).comp MulOpposite.continuous_unop).comp continuous_fst).smul
    continuous_snd⟩

/-- Passing from a legal representative to its class preserves left and right multiplication. -/
theorem supportActions_mk (n : ℕ) (v : closedSpace) (m : mixedClosure) :
    Ideal.Quotient.mk (supportIdeal n) v • m = v • m ∧
    MulOpposite.op (Ideal.Quotient.mk (supportIdeal n) v) • m = MulOpposite.op v • m :=
  ⟨rfl, rfl⟩

/-- The two actions agree along every arrow in the support tower and at its mixed quotient. -/
theorem supportActions_transition {n k : ℕ} (h : n ≤ k) (q : closedSpace ⧸ supportIdeal n)
    (m : mixedClosure) :
    (Ideal.Quotient.factorₐ ℝ (supportIdeal_mono h) q) • m = q • m ∧
    MulOpposite.op (Ideal.Quotient.factorₐ ℝ (supportIdeal_mono h) q) • m =
      MulOpposite.op q • m ∧
    (Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n) q) • m = q • m ∧
    MulOpposite.op (Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n) q) • m =
      MulOpposite.op q • m := by
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.factorₐ_apply_mk]
  have hn := supportActions_mk n v m
  have hk := supportActions_mk k v m
  have hm := mixedQuotient_actions v m
  exact ⟨hk.1.trans hn.1.symm, hk.2.trans hn.2.symm,
    hm.1.trans hn.1.symm, hm.2.trans hn.2.symm⟩

/-- The annihilator at a support stage is the kernel of its map to the mixed quotient. -/
theorem supportActions_annihilator (n : ℕ) (q : closedSpace ⧸ supportIdeal n) :
    (∀ m : mixedClosure, q • m = 0) ↔
      Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n) q = 0 := by
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective q
  change (∀ m : mixedClosure, v • m = 0) ↔ Ideal.Quotient.mk mixedIdeal v = 0
  rw [mixedLeft_annihilator, Ideal.Quotient.eq_zero_iff_mem]

theorem supportSpace_stable_actions {n : ℕ} {m : mixedClosure} (hm : m ∈ supportSpace n)
    (v : closedSpace) : v • m ∈ supportSpace n ∧ MulOpposite.op v • m ∈ supportSpace n :=
  ⟨(supportSpace n).smul_mem (legalPacketMean v) hm,
    (supportSpace n).smul_mem (legalPacketMean v) hm⟩

section
variable {A : Type} [CommRing A] [Algebra ℝ A]

private def idealTower (I : ℕ → Ideal A) (hI : Monotone I) : ℕ ⥤ AlgCat ℝ where
  obj n := AlgCat.of ℝ (A ⧸ I n)
  map f := AlgCat.ofHom (Ideal.Quotient.factorₐ ℝ (hI (leOfHom f)))
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  map_comp {i j k} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl

private def idealCocone (I : ℕ → Ideal A) (hI : Monotone I) (J : Ideal A)
    (hJ : ∀ n, I n ≤ J) : Limits.Cocone (idealTower I hI) where
  pt := AlgCat.of ℝ (A ⧸ J)
  ι := {
    app := fun n => AlgCat.ofHom (Ideal.Quotient.factorₐ ℝ (hJ n))
    naturality := by
      intro i j f
      apply ConcreteCategory.hom_ext
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      rfl }

private theorem linear_factor_comp {I J K : Ideal A} (hIJ : I ≤ J) (hJK : J ≤ K)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (f : (A ⧸ K) →ₗ[ℝ] E) :
    (f.comp (Ideal.Quotient.factorₐ ℝ hJK).toLinearMap).comp
        (Ideal.Quotient.factorₐ ℝ hIJ).toLinearMap =
      f.comp (Ideal.Quotient.factorₐ ℝ (hIJ.trans hJK)).toLinearMap := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

private theorem factor_shortExact {I J : Ideal A} (hIJ : I ≤ J) :
    (Ideal.Quotient.factorₐ ℝ hIJ).toLinearMap.shortComplexKer.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨Ideal.Quotient.mk I a, rfl⟩

end

/-- Quotients of the legal algebra by successively larger mixed support ideals. -/
def supportAlgebraTower : ℕ ⥤ AlgCat ℝ := idealTower supportIdeal supportIdeal_mono

/-- The cocone to the quotient by the closed mixed ideal. -/
def supportAlgebraCocone : Limits.Cocone supportAlgebraTower :=
  idealCocone supportIdeal supportIdeal_mono mixedIdeal supportIdeal_le_mixed

/-- Each transition is surjective and gives the kernel-to-quotient short exact sequence. -/
theorem supportTransition_shortExact {n k : ℕ} (h : n ≤ k) :
    (Ideal.Quotient.factorₐ ℝ (supportIdeal_mono h)).toLinearMap.shortComplexKer.ShortExact :=
  factor_shortExact (supportIdeal_mono h)

/-- Representatives of the transition kernel are exactly the vectors in the later ideal. -/
theorem supportTransition_kernel_mk_iff {n k : ℕ} (h : n ≤ k) (v : closedSpace) :
    Ideal.Quotient.mk (supportIdeal n) v ∈
      (Ideal.Quotient.factorₐ ℝ (supportIdeal_mono h)).toLinearMap.ker ↔ v ∈ supportIdeal k :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Universal property against Hausdorff targets, written on representatives.
Continuity of the stage-zero leg already suffices. -/
theorem supportAlgebra_hausdorff_desc {Y : Type*} [Ring Y] [Algebra ℝ Y]
    [TopologicalSpace Y] [T2Space Y]
    (t : ∀ n, (closedSpace ⧸ supportIdeal n) →ₐ[ℝ] Y) (h₀ : Continuous (t 0))
    (ht : ∀ n v, t n (Ideal.Quotient.mk (supportIdeal n) v) =
      t 0 (Ideal.Quotient.mk (supportIdeal 0) v)) :
    ∃! f : (closedSpace ⧸ mixedIdeal) →ₐ[ℝ] Y, Continuous f ∧
      ∀ n v, f (Ideal.Quotient.mk mixedIdeal v) = t n (Ideal.Quotient.mk (supportIdeal n) v) := by
  let T := (t 0).comp (Ideal.Quotient.mkₐ ℝ (supportIdeal 0))
  have hT : Continuous T := h₀.comp (QuotientRing.isOpenQuotientMap_mk (supportIdeal 0)).continuous
  let L := T.toLinearMap.comp legalMixedInclusion.toLinearMap
  have hclosed : IsClosed (L.ker : Set mixedClosure) :=
    isClosed_eq (hT.comp legalMixedInclusion.continuous) continuous_const
  have hi : (⨆ n, supportSpace n) ≤ L.ker := by
    refine iSup_le fun n m hm => ?_
    change t 0 (Ideal.Quotient.mk (supportIdeal 0) (legalMixedInclusion m)) = 0
    rw [← ht n, (Ideal.Quotient.eq_zero_iff_mem).2
      (show legalMixedInclusion m ∈ supportIdeal n from ⟨m, hm, rfl⟩), map_zero]
  have hd := Submodule.topologicalClosure_minimal _ hi hclosed
  rw [supportSpace_dense] at hd
  have hM (v : closedSpace) (hv : v ∈ mixedIdeal) : T v = 0 :=
    hd (show (⟨v.val, (mem_mixedIdeal v).1 hv⟩ : mixedClosure) ∈ ⊤ from trivial)
  refine ⟨Ideal.Quotient.liftₐ mixedIdeal T hM, ⟨?_, ?_⟩, ?_⟩
  · exact (QuotientRing.isOpenQuotientMap_mk mixedIdeal).isQuotientMap.continuous_iff.2 hT
  · intro n v
    exact (ht n v).symm
  · intro f hf
    apply AlgHom.ext
    intro q
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact hf.2 0 v

/-- Pull the connecting map of the full centered diagram back along the algebra cocone. -/
def stageMeanBoundary (n : ℕ) : (closedSpace ⧸ supportIdeal n) →ₗ[ℝ] BoundaryTarget :=
  quotientBoundary.comp (Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n)).toLinearMap

theorem stageMeanBoundary_natural {n k : ℕ} (h : n ≤ k) :
    (stageMeanBoundary k).comp (Ideal.Quotient.factorₐ ℝ (supportIdeal_mono h)).toLinearMap =
      stageMeanBoundary n :=
  linear_factor_comp (supportIdeal_mono h) (supportIdeal_le_mixed k) quotientBoundary

/-- In particular an arbitrary legal representative has the centered connecting class. -/
theorem stageMeanBoundary_mk (n : ℕ) (v : closedSpace) :
    stageMeanBoundary n (Ideal.Quotient.mk (supportIdeal n) v) =
      mixedInMeanZero.mkQ ⟨center v.val, center_mem v.val⟩ := quotientBoundary_mk v

theorem stageMeanBoundary_unit (n : ℕ) :
    stageMeanBoundary n 1 = mixedInMeanZero.mkQ defect := by
  change quotientBoundary ((Ideal.Quotient.factorₐ ℝ (supportIdeal_le_mixed n)) 1) = _
  rw [map_one, quotientBoundary_apply, map_one, boundary_apply, one_smul]

/-- The ambient mixed quotient contains the centered snake target via inclusion. -/
def boundaryToMixedQuotient : BoundaryTarget →ₗ[ℝ] (ThresholdHilbert ⧸ mixedClosure) :=
  mixedInMeanZero.liftQ (mixedClosure.mkQ.comp meanZero.subtype)
    fun _ hx => (Submodule.Quotient.mk_eq_zero mixedClosure).2 hx

theorem boundaryToMixedQuotient_injective : Function.Injective boundaryToMixedQuotient := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨z, rfl⟩ := mixedInMeanZero.mkQ_surjective q
  exact (Submodule.Quotient.mk_eq_zero mixedInMeanZero).2
    ((Submodule.Quotient.mk_eq_zero mixedClosure).1 hq)

/-- The algebra unit and the centered parity packet determine the same obstruction
after descent through their respective towers. -/
theorem stageMeanBoundary_unit_eq_descended_parity (n : ℕ) :
    boundaryToMixedQuotient (stageMeanBoundary n 1) =
      (supportQuotientCocone.ι.app n) (parityQuotientClass n) := by
  rw [stageMeanBoundary_unit, supportCocone_parity_eq_defect]
  rfl

open RiemannResearch.SquarefreeResidueCRT

/-- The product of the centered prime-coordinate indicators on the actual CRT product. -/
def coordinateContrast (S : PrimeFamily) (x : Coordinates S) : ℝ :=
  ∏ p : S.val, ((if x p = 0 then (p.val : ℝ) else 0) - 1)

theorem coordinateContrast_natCast (S : PrimeFamily) (n : ℕ) :
    coordinateContrast S (crtEquiv S (n : ZMod (conductor S))) =
      ∏ p ∈ S.val, ((if p ∣ n then (p : ℝ) else 0) - 1) := by
  rw [show crtEquiv S (n : ZMod (conductor S)) = (n : Coordinates S) from
    map_natCast (crtEquiv S) n]
  change (∏ p : S.val, ((if (n : ZMod p.val) = 0 then (p.val : ℝ) else 0) - 1)) = _
  simp only [ZMod.natCast_eq_zero_iff]
  exact Finset.prod_attach S.val (fun p => (if p ∣ n then (p : ℝ) else 0) - 1)

/-- The squarefree Ramanujan sum is the product of the local contrasts after CRT. -/
theorem ramanujanSum_eq_crtContrast (S : PrimeFamily) (n : ℕ) :
    ramanujanSum (conductor S) n =
      coordinateContrast S (crtEquiv S (n : ZMod (conductor S))) := by
  rw [coordinateContrast_natCast, ramanujanSum_prime_contrasts _ _ (conductor_squarefree S),
    primeFactors_conductor]

/-- The integrated squarefree packet is reconstructed by summing the products
along the diagonal residue classes of the first n positive integers. -/
theorem squarefree_packet_prefix_crt (S : PrimeFamily) (n : ℕ) (hq : 1 < conductor S) :
    ramanujanPacket (conductor S) n = -∑ m ∈ Finset.Ico 1 (n + 1),
      coordinateContrast S (crtEquiv S (m : ZMod (conductor S))) := by
  rw [ramanujanPacket_prefix _ _ hq]
  simp_rw [ramanujanSum_eq_crtContrast]

/-- A mixed packet enters the support filtration exactly at the number of its distinct primes. -/
theorem packet_mem_supportIdeal_iff (q : Index) (k : ℕ) :
    legalMixedInclusion (packet q) ∈ supportIdeal k ↔ q.val.primeFactors.card ≤ k := by
  constructor
  · rintro ⟨m, hm, he⟩
    have hmq : m = packet q :=
      Subtype.ext (congrArg (fun v : closedSpace => v.val) he)
    by_contra! hk
    have hz := supportSpace_le_coordinate_ker q hk (hmq ▸ hm)
    change supportCoordinate q (packet q) = 0 at hz
    rw [supportCoordinate_self] at hz
    have hp : (0 : ℝ) < q.val := by exact_mod_cast Nat.zero_lt_one.trans q.property.1
    linarith
  · intro h
    exact ⟨packet q, packet_mem_supportSpace q h, rfl⟩

/-- The mixed conductor attached to a CRT family with at least two coordinates. -/
def familyMixedIndex (S : PrimeFamily) (h : 2 ≤ S.val.card) : Index :=
  ⟨conductor S, by
    apply Nat.nonempty_primeFactors.mp
    apply Finset.card_pos.mp
    rw [primeFactors_conductor]
    omega, by
    intro hp
    have h₁ := isPrimePow_iff_card_primeFactors_eq_one.mp hp
    rw [primeFactors_conductor] at h₁
    omega⟩

/-- The class of a squarefree mixed packet becomes zero precisely when its whole
prime support fits the stage. Its mean already vanishes in the legal algebra. -/
theorem squarefree_packet_descent (S : PrimeFamily) (h : 2 ≤ S.val.card) (k : ℕ) :
    let v := legalMixedInclusion (packet (familyMixedIndex S h))
    (Ideal.Quotient.mk (supportIdeal k) v = 0 ↔ S.val.card ≤ k) ∧ legalPacketMean v = 0 := by
  dsimp only
  refine ⟨?_, legalPacketMean_legalMixedInclusion _⟩
  rw [Ideal.Quotient.eq_zero_iff_mem, packet_mem_supportIdeal_iff]
  change (conductor S).primeFactors.card ≤ k ↔ _
  rw [primeFactors_conductor]

/-- In the one-prime direction every positive exponent has the same screened packet. -/
theorem primePower_screened (p a : ℕ) (hp : p.Prime) (ha : a ≠ 0) :
    fullScreening (ramanujanPacketHilbert (p ^ a)) = Real.log p • normalizedScreenedTwo := by
  rw [fullScreening_packet_eq_mangoldt_smul _ (Nat.one_lt_pow ha hp.one_lt),
    ArithmeticFunction.vonMangoldt_apply_pow ha, ArithmeticFunction.vonMangoldt_apply_prime hp]

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

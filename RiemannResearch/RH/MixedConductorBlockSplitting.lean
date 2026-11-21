import RiemannResearch.RH.MixedConductorHilbertBasis
import RiemannResearch.RH.MixedConductorSplitExact
import RiemannResearch.RH.MixedConductorSquareZero
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel

/-!
# Categorical decompositions of the mixed Pareto ideal

Each orthogonal pair of complementary closed subspaces supplies a split exact
sequence and a binary biproduct in `TopModuleCat ℝ`. One application splits an
arithmetic set of raw packets from the screened remaining packets. Another splits
any partition of the conductor-ordered Hilbert basis.

The underlying real subspaces of the mixed kernel correspond in order, with
closedness preserved, to the subideals of the square-zero mixed ideal.
The algebra acts on that kernel through the legal scalar mean.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open CoefficientStabilization

private theorem projection_congr {K L : Submodule ℝ mixedClosure}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : K = L) :
    K.starProjection = L.starProjection := by
  subst L
  rfl

/-- The projections for an orthogonal block partition reconstruct the original vector. -/
theorem projection_add {K L : Submodule ℝ mixedClosure} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : L = Kᗮ) (x : mixedClosure) :
    K.starProjection x + L.starProjection x = x := by
  rw [projection_congr h, Submodule.starProjection_orthogonal_val]
  abel

theorem block_norm_sq (s : Set Index) (x : mixedClosure) :
    ‖x‖ ^ 2 = ‖(block s).starProjection x‖ ^ 2 + ‖(block sᶜ).starProjection x‖ ^ 2 := by
  rw [projection_congr (block_compl s)]
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection x (block s)

/-- Inclusion of a mixed subspace followed by projection onto its orthogonal complement. -/
def blockComplex {K L : Submodule ℝ mixedClosure} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : L = Kᗮ) : ShortComplex (TopModuleCat ℝ) :=
  ShortComplex.mk (TopModuleCat.ofHom K.subtypeL) (TopModuleCat.ofHom L.orthogonalProjectionOnto)
    (by
      apply ConcreteCategory.hom_ext
      intro m
      apply Subtype.ext
      change L.starProjection (m : mixedClosure) = 0
      rw [projection_congr h, Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_mem_subspace_eq_self, sub_self])

/-- The retraction is orthogonal projection and the section is the isometric inclusion. -/
def blockSplitting {K L : Submodule ℝ mixedClosure} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : L = Kᗮ) : (blockComplex h).Splitting where
  r := TopModuleCat.ofHom K.orthogonalProjectionOnto
  s := TopModuleCat.ofHom L.subtypeL
  f_r := by
    apply ConcreteCategory.hom_ext
    intro m
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self m
  s_g := by
    apply ConcreteCategory.hom_ext
    intro m
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self m
  id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact projection_add h x

local instance : HasZeroObject (TopModuleCat.{0} ℝ) :=
  ⟨⟨_, (terminalIsTerminal (C := TopModuleCat.{0} ℝ)).isZero⟩⟩

local instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

theorem block_shortExact {K L : Submodule ℝ mixedClosure} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : L = Kᗮ) : (blockComplex h).ShortExact :=
  (blockSplitting h).shortExact

/-- Any partition of the orthonormal conductor labels gives a categorical biproduct. -/
def blockBiprodIso (s : Set Index) :
    TopModuleCat.of ℝ mixedClosure ≅ TopModuleCat.of ℝ (block s) ⊞ TopModuleCat.of ℝ (block sᶜ) :=
  (blockSplitting (block_compl s)).isoBinaryBiproduct

instance screenedComplement_hasOrthogonalProjection (s : Set Index) :
    (screenedComplement s).HasOrthogonalProjection := by
  rw [screenedComplement_eq_orthogonal]
  infer_instance

/-- A raw arithmetic packet selection splits off with the screened remaining packets. -/
def packetBiprodIso (s : Set Index) :
    TopModuleCat.of ℝ mixedClosure ≅
      TopModuleCat.of ℝ (packetBlock s) ⊞ TopModuleCat.of ℝ (screenedComplement s) :=
  (blockSplitting (screenedComplement_eq_orthogonal s)).isoBinaryBiproduct

open scoped LegalMeanAlgebra

/-- Every linear subspace of the mixed kernel is an ideal of the screened algebra. -/
def subspaceIdeal (K : Submodule ℝ mixedClosure) : Ideal closedSpace where
  __ := (K.map legalMixedInclusion.toLinearMap).toAddSubmonoid
  smul_mem' x _ hy := by
    obtain ⟨m, hm, rfl⟩ := hy
    refine ⟨legalPacketMean x • m, K.smul_mem _ hm, ?_⟩
    change legalMixedInclusion (legalPacketMean x • m) = x * legalMixedInclusion m
    simp only [map_smul, LegalMeanAlgebra.mul_def, LegalMeanAlgebra.mulWith,
      legalPacketMean_legalMixedInclusion, zero_smul, mul_zero, add_zero, sub_zero]

theorem subspaceIdeal_le (K : Submodule ℝ mixedClosure) :
    subspaceIdeal K ≤ LegalMeanAlgebra.mixedIdeal := by
  rintro _ ⟨m, _, rfl⟩
  exact (LegalMeanAlgebra.mem_mixedIdeal _).mpr m.property

private theorem inclusion_injective : Function.Injective legalMixedInclusion := by
  intro m n h
  exact Subtype.ext (congrArg (fun x : closedSpace => (x : ThresholdHilbert)) h)

theorem inclusion_mem_subspaceIdeal (K : Submodule ℝ mixedClosure) (m : mixedClosure) :
    legalMixedInclusion m ∈ subspaceIdeal K ↔ m ∈ K := by
  constructor
  · rintro ⟨n, hn, he⟩
    exact inclusion_injective he ▸ hn
  · intro hm
    exact ⟨m, hm, rfl⟩

/-- The subobject lattice of the real mixed space is the entire interval of algebra
ideals contained in the square-zero mixed ideal. -/
def subspaceIdealOrderIso :
    Submodule ℝ mixedClosure ≃o Set.Iic LegalMeanAlgebra.mixedIdeal where
  toFun K := ⟨subspaceIdeal K, subspaceIdeal_le K⟩
  invFun I := (I.val.restrictScalars ℝ).comap legalMixedInclusion.toLinearMap
  left_inv K := by
    ext m
    exact inclusion_mem_subspaceIdeal K m
  right_inv I := by
    apply Subtype.ext
    ext v
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hv
      let m : mixedClosure :=
        ⟨(v : ThresholdHilbert), (LegalMeanAlgebra.mem_mixedIdeal v).mp (I.property hv)⟩
      exact ⟨m, hv, rfl⟩
  map_rel_iff' := by
    intro K L
    change subspaceIdeal K ≤ subspaceIdeal L ↔ K ≤ L
    constructor
    · intro h m hm
      exact (inclusion_mem_subspaceIdeal L m).mp (h ((inclusion_mem_subspaceIdeal K m).mpr hm))
    · rintro h _ ⟨m, hm, rfl⟩
      exact ⟨m, h hm, rfl⟩

theorem subspaceIdeal_isClosed_iff (K : Submodule ℝ mixedClosure) :
    IsClosed (subspaceIdeal K : Set closedSpace) ↔ IsClosed (K : Set mixedClosure) := by
  constructor
  · intro h
    have he : (K : Set mixedClosure) =
        legalMixedInclusion ⁻¹' (subspaceIdeal K : Set closedSpace) :=
      Set.ext fun x => (inclusion_mem_subspaceIdeal K x).symm
    rw [he]
    exact h.preimage legalMixedInclusion.continuous
  · intro hK
    have hset : (subspaceIdeal K : Set closedSpace) =
        (legalPacketMean ⁻¹' {0}) ∩ (legalMixedRetraction ⁻¹' (K : Set mixedClosure)) := by
      ext v
      constructor
      · rintro ⟨m, hm, rfl⟩
        refine ⟨legalPacketMean_legalMixedInclusion m, ?_⟩
        have h : legalMixedRetraction (legalMixedInclusion m) = m :=
          ConcreteCategory.congr_hom legalMeanSplitting.f_r m
        change legalMixedRetraction (legalMixedInclusion m) ∈ K
        rwa [h]
      · rintro ⟨h0, hm⟩
        refine ⟨legalMixedRetraction v, hm, ?_⟩
        change legalPacketMean v = 0 at h0
        change legalMixedInclusion (legalMixedRetraction v) = v
        rw [legalMixedInclusion_legalMixedRetraction, h0, map_zero, sub_zero]
    rw [hset]
    exact (isClosed_singleton.preimage legalPacketMean.continuous).inter
      (hK.preimage legalMixedRetraction.continuous)

/-- Orthogonal complements give complementary ideals inside the mixed ideal. -/
theorem complementary_subspaceIdeals {K L : Submodule ℝ mixedClosure}
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (h : L = Kᗮ) :
    subspaceIdeal K ⊔ subspaceIdeal L = LegalMeanAlgebra.mixedIdeal ∧
      Disjoint (subspaceIdeal K) (subspaceIdeal L) := by
  constructor
  · apply le_antisymm (sup_le (subspaceIdeal_le _) (subspaceIdeal_le _))
    intro v hv
    let m : mixedClosure := ⟨(v : ThresholdHilbert), (LegalMeanAlgebra.mem_mixedIdeal v).mp hv⟩
    have he := congrArg legalMixedInclusion (projection_add h m)
    rw [map_add] at he
    change legalMixedInclusion m ∈ _
    rw [← he]
    apply (subspaceIdeal K ⊔ subspaceIdeal L).add_mem
    · exact (le_sup_left : subspaceIdeal K ≤ _) ⟨_, K.starProjection_apply_mem m, rfl⟩
    · exact (le_sup_right : subspaceIdeal L ≤ _) ⟨_, L.starProjection_apply_mem m, rfl⟩
  · rw [disjoint_iff_inf_le]
    intro v hv
    obtain ⟨m, hm, he⟩ := hv.1
    obtain ⟨n, hn, he'⟩ := hv.2
    have hnm : n = m := inclusion_injective (he'.trans he.symm)
    subst n
    rw [h] at hn
    have hm0 : m = 0 := inner_self_eq_zero.mp (hn m hm)
    change v = 0
    simpa only [hm0, map_zero] using he.symm

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

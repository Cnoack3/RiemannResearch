import RiemannResearch.RH.MixedConductorHilbertBasis
import RiemannResearch.RH.IntegratedRamanujanHilbert
import RiemannResearch.RH.MobiusDifferenceCLM
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# The mixed conductor filtration by number of distinct prime factors

The Möbius difference at a conductor annihilates every strictly lower support
stage and detects the conductor's own packet. The resulting orthogonal layers
are nonzero at every support size from two onward. Their finite partial sums
converge to the identity in the strong operator sense.

The arithmetic input is the exact packet incidence relation in
`IntegratedRamanujanHilbert`. Projection differences use `NestedOrthogonalDecomposition`.
-/

noncomputable section
open Filter CategoryTheory CategoryTheory.Limits
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
open RiemannResearch.Analysis.NestedOrthogonalDecomposition

/-- Closed span of the raw packets with at most `k` distinct prime divisors. -/
abbrev supportSpace (k : ℕ) : Submodule ℝ mixedClosure :=
  packetBlock {q | q.val.primeFactors.card ≤ k}

theorem supportSpace_mono : Monotone supportSpace := by
  intro k l h
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q, le_trans hq h, rfl⟩

/-- A raw mixed packet belongs to every stage containing its prime support. -/
theorem packet_mem_supportSpace (q : Index) {k : ℕ} (h : q.val.primeFactors.card ≤ k) :
    packet q ∈ supportSpace k :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, h, rfl⟩)

theorem supportSpace_one : supportSpace 1 = ⊥ := by
  have he : {q : Index | q.val.primeFactors.card ≤ 1} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q h
    change q.val.primeFactors.card ≤ 1 at h
    have hp := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr q.property.1)
    exact q.property.2 (isPrimePow_iff_card_primeFactors_eq_one.mpr (by omega))
  change (Submodule.span ℝ (packet '' {q : Index | q.val.primeFactors.card ≤ 1})).topologicalClosure
    = ⊥
  simp [he]

/-- The finite Möbius difference restricted to the mixed kernel. -/
def supportCoordinate (q : Index) : mixedClosure →L[ℝ] ℝ :=
  (mobiusDifferenceCLM q.val).comp mixedClosure.subtypeL

/-- The conductor's own Möbius coordinate detects its raw packet. -/
theorem supportCoordinate_self (q : Index) :
    supportCoordinate q (packet q) = -(q.val : ℝ) := by
  have hp := Nat.zero_lt_one.trans q.property.1
  change mobiusDifferenceCLM q.val (ramanujanPacketHilbert q.val) = _
  rw [mobiusDifferenceCLM_ramanujanPacketHilbert _ _ q.property.1 hp, if_pos (dvd_refl _),
    Nat.div_self hp]
  simp

/-- Divisibility prevents the coordinate at a larger prime support from seeing any
packet in the lower closed stage. -/
theorem supportSpace_le_coordinate_ker {k : ℕ} (q : Index) (hq : k < q.val.primeFactors.card) :
    supportSpace k ≤ (supportCoordinate q).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, rfl⟩
    change r.val.primeFactors.card ≤ k at hr
    have hr0 := Nat.zero_lt_one.trans r.property.1
    have hnd : ¬ q.val ∣ r.val := by
      intro hd
      have hc := Finset.card_le_card (Nat.primeFactors_mono hd hr0.ne')
      omega
    change mobiusDifferenceCLM q.val (ramanujanPacketHilbert r.val) = 0
    rw [mobiusDifferenceCLM_ramanujanPacketHilbert _ _ q.property.1 hr0, if_neg hnd]
  · exact (supportCoordinate q).isClosed_ker

/-- Projecting off a strictly lower support stage leaves the diagonal value intact. -/
theorem supportCoordinate_residual {k : ℕ} (q : Index) (hq : k < q.val.primeFactors.card) :
    supportCoordinate q (packet q - (supportSpace k).starProjection (packet q)) = -(q.val : ℝ) := by
  have hz : supportCoordinate q ((supportSpace k).starProjection (packet q)) = 0 :=
    supportSpace_le_coordinate_ker q hq ((supportSpace k).starProjection_apply_mem _)
  rw [map_sub, supportCoordinate_self, hz, sub_zero]

/-- The first three-prime packet retains the Möbius coordinate minus thirty after
orthogonal projection off all two-prime packets. -/
theorem conductor_thirty_witness :
    let q : Index := ⟨30, by decide, by decide⟩
    supportCoordinate q (packet q - (supportSpace 2).starProjection (packet q)) = -(30 : ℝ) := by
  apply supportCoordinate_residual
  change 2 < (30 : ℕ).primeFactors.card
  rw [show (30 : ℕ) = 2 * (3 * 5) by decide,
    Nat.primeFactors_mul (by decide : (2 : ℕ) ≠ 0) (by decide : (3 * 5 : ℕ) ≠ 0),
    Nat.primeFactors_mul (by decide : (3 : ℕ) ≠ 0) (by decide : (5 : ℕ) ≠ 0),
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
    (show Nat.Prime 5 by norm_num).primeFactors]
  decide

private theorem exists_nat_support_card (k : ℕ) : ∃ n : ℕ, n ≠ 0 ∧ n.primeFactors.card = k := by
  induction k with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ k ih =>
    obtain ⟨n, hn, hc⟩ := ih
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
    have hf : p ∉ n.primeFactors :=
      fun h => (not_lt_of_ge (Nat.le_of_mem_primeFactors h)) (Nat.lt_of_succ_le hpn)
    refine ⟨p * n, Nat.mul_ne_zero hp.ne_zero hn, ?_⟩
    rw [Nat.primeFactors_mul hp.ne_zero hn, hp.primeFactors, Finset.singleton_union,
      Finset.card_insert_of_notMem hf, hc]

/-- Every support size at least two contributes a genuinely new packet. -/
theorem supportSpace_strict (k : ℕ) (hk : 1 ≤ k) : supportSpace k < supportSpace (k + 1) := by
  obtain ⟨n, hn, hc⟩ := exists_nat_support_card (k + 1)
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp at hc
  let q : Index := ⟨n, by omega, fun h => by
    have h1 := isPrimePow_iff_card_primeFactors_eq_one.mp h
    omega⟩
  have hq : q.val.primeFactors.card = k + 1 := hc
  apply lt_of_le_of_ne (supportSpace_mono (Nat.le_succ k))
  intro he
  have hmem : packet q ∈ supportSpace k := by
    rw [he]
    exact packet_mem_supportSpace q hq.le
  have hz : supportCoordinate q (packet q) = 0 :=
    supportSpace_le_coordinate_ker q (by omega) hmem
  rw [supportCoordinate_self, neg_eq_zero] at hz
  exact hn (by exact_mod_cast hz)

/-- The layer with `k+1` distinct primes inside the mixed space. -/
abbrev supportLayer (k : ℕ) : Submodule ℝ mixedClosure :=
  supportSpace (k + 1) ⊓ (supportSpace k)ᗮ

instance supportLayer_hasOrthogonalProjection (k : ℕ) : (supportLayer k).HasOrthogonalProjection :=
  carry_hasOrthogonalProjection (supportSpace_mono (Nat.le_succ k))

theorem supportSpace_sup_layer (k : ℕ) :
    supportSpace k ⊔ supportLayer k = supportSpace (k + 1) :=
  prime_sup_carry (supportSpace_mono (Nat.le_succ k))

theorem supportLayer_ne_bot (k : ℕ) (hk : 1 ≤ k) : supportLayer k ≠ ⊥ := by
  intro h
  have e := supportSpace_sup_layer k
  rw [h, sup_bot_eq] at e
  exact (supportSpace_strict k hk).ne e

theorem supportLayer_orthogonal {i j : ℕ} (h : i < j) {x y : mixedClosure}
    (hx : x ∈ supportLayer i) (hy : y ∈ supportLayer j) : inner ℝ x y = 0 :=
  hy.2 x (supportSpace_mono (Nat.succ_le_of_lt h) hx.1)

theorem supportLayer_projection (k : ℕ) (x : mixedClosure) :
    (supportLayer k).starProjection x =
      (supportSpace (k + 1)).starProjection x - (supportSpace k).starProjection x :=
  carry_projection_apply (supportSpace_mono (Nat.le_succ k)) x

theorem supportSpace_dense : (⨆ k, supportSpace k).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← packet_span_dense]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact (le_iSup supportSpace q.val.primeFactors.card) (packet_mem_supportSpace q le_rfl)

theorem sum_supportLayer_projection (n : ℕ) (x : mixedClosure) :
    (∑ k ∈ Finset.range n, (supportLayer k).starProjection x) =
      (supportSpace n).starProjection x := by
  induction n with
  | zero =>
    have h0 : supportSpace 0 ≤ ⊥ :=
      (supportSpace_mono (by decide : 0 ≤ 1)).trans supportSpace_one.le
    have hz := h0 ((supportSpace 0).starProjection_apply_mem x)
    simpa only [Finset.range_zero, Finset.sum_empty] using ((Submodule.mem_bot ℝ).mp hz).symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, supportLayer_projection]
    abel

/-- The orthogonal support-layer expansion converges in the original norm for every mixed vector. -/
theorem tendsto_sum_supportLayer_projection (x : mixedClosure) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (supportLayer k).starProjection x) atTop (𝓝 x) := by
  simp_rw [sum_supportLayer_projection]
  have h := Submodule.starProjection_tendsto_closure_iSup supportSpace supportSpace_mono x
  have hx : x ∈ (⨆ k, supportSpace k).topologicalClosure := by rw [supportSpace_dense]; trivial
  rwa [Submodule.starProjection_eq_self_iff.mpr hx] at h

/-- The finite sum of squared layer projections is the energy captured at the cutoff. -/
theorem sum_supportLayer_energy (n : ℕ) (x : mixedClosure) :
    (∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection x‖ ^ 2) =
      ‖(supportSpace n).starProjection x‖ ^ 2 := by
  induction n with
  | zero =>
    have hz := congrArg (fun y : mixedClosure => ‖y‖ ^ 2) (sum_supportLayer_projection 0 x)
    simpa using hz
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have ho : inner ℝ ((supportSpace n).starProjection x) ((supportLayer n).starProjection x) = 0 :=
      ((supportLayer n).starProjection_apply_mem x).2 _
        ((supportSpace n).starProjection_apply_mem x)
    have hs : (supportSpace n).starProjection x + (supportLayer n).starProjection x =
        (supportSpace (n + 1)).starProjection x := by
      rw [supportLayer_projection]
      abel
    rw [← hs, norm_add_sq_real, ho]
    simp

/-- Parseval for the grading by number of distinct prime divisors. -/
theorem tendsto_sum_supportLayer_energy (x : mixedClosure) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection x‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2)) := by
  simpa only [sum_supportLayer_projection, sum_supportLayer_energy] using
    (tendsto_sum_supportLayer_projection x).norm.pow 2

private def includeIn {U V : Submodule ℝ mixedClosure} (h : U ≤ V) : U →L[ℝ] V :=
  U.subtypeL.codRestrict V fun x => h x.property

/-- The sequence realizing the next support layer as a categorical quotient. -/
def layerComplex (k : ℕ) : ShortComplex (TopModuleCat ℝ) :=
  ShortComplex.mk (TopModuleCat.ofHom (includeIn (supportSpace_mono (Nat.le_succ k))))
    (TopModuleCat.ofHom ((supportLayer k).orthogonalProjectionOnto.comp
      (supportSpace (k + 1)).subtypeL))
    (by
      apply ConcreteCategory.hom_ext
      intro m
      apply Subtype.ext
      change (supportLayer k).starProjection (m : mixedClosure) = 0
      rw [supportLayer_projection,
        Submodule.starProjection_eq_self_iff.mpr (supportSpace_mono (Nat.le_succ k) m.property),
        Submodule.starProjection_mem_subspace_eq_self, sub_self])

def layerSplitting (k : ℕ) : (layerComplex k).Splitting where
  r := TopModuleCat.ofHom ((supportSpace k).orthogonalProjectionOnto.comp
    (supportSpace (k + 1)).subtypeL)
  s := TopModuleCat.ofHom (includeIn (show supportLayer k ≤ supportSpace (k + 1) from inf_le_left))
  f_r := by
    apply ConcreteCategory.hom_ext
    intro m
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self m
  s_g := by
    apply ConcreteCategory.hom_ext
    intro z
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
  id := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact projection_split_of_mem (supportSpace_mono (Nat.le_succ k)) x.property

local instance : HasZeroObject (TopModuleCat.{0} ℝ) :=
  ⟨⟨_, (terminalIsTerminal (C := TopModuleCat.{0} ℝ)).isZero⟩⟩

theorem layer_shortExact (k : ℕ) : (layerComplex k).ShortExact := (layerSplitting k).shortExact

/-- The layer projection is a categorical cokernel of the previous-stage inclusion. -/
def layerIsCokernel (k : ℕ) :
    IsColimit (CokernelCofork.ofπ (layerComplex k).g (layerComplex k).zero) :=
  (layerSplitting k).gIsCokernel

local instance : HasBinaryBiproducts (TopModuleCat.{0} ℝ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

def supportSpaceBiprodIso (k : ℕ) :
    TopModuleCat.of ℝ (supportSpace (k + 1)) ≅
      TopModuleCat.of ℝ (supportSpace k) ⊞ TopModuleCat.of ℝ (supportLayer k) :=
  (layerSplitting k).isoBinaryBiproduct

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

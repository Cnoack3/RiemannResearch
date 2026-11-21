import RiemannResearch.RH.PrimePowerRamanujanClosure
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.PrimePowerRamanujanSchur
import RiemannResearch.RH.PhysicalCompensatedSource
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.ScreenedPrimePowerTelescope
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# A conductor-indexed Hilbert basis and arithmetic blocks of the mixed closure

The independent mixed Ramanujan packets span a dense subspace of the physical
Pareto kernel. Increasing conductor order determines their Gram–Schmidt basis.
Choosing any group of raw packets gives an orthogonal splitting after the
remaining packets are projected off its closed span.

The Hilbert construction uses mathlib's `InnerProductSpace.gramSchmidtNormed`
and `HilbertBasis.mkOfOrthogonalEqBot`. The arithmetic inputs are the finite
packet independence theorem, the conductor-six Gram entries, and the exact
full mixed projection identity in the imported Pareto modules.
-/

noncomputable section
open Filter InnerProductSpace
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

/-- Conductors greater than one with at least two distinct prime divisors, in numerical order. -/
abbrev Index := {q : ℕ // 1 < q ∧ ¬ IsPrimePow q}

/-- The actual integrated packet in the mixed closure. -/
def packet (q : Index) : mixedClosure :=
  ⟨ramanujanPacketHilbert q.val, mixed_packet_mem_closure q.val q.property.1 q.property.2⟩

theorem packet_independent : LinearIndependent ℝ packet := by
  classical
  apply LinearIndependent.of_comp mixedClosure.subtype
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  let t := s.image (fun q : Index => q.val)
  have ht : ∀ q ∈ t, 1 < q := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact i.property.1
  let inc (i : s) : t := ⟨i.val.val, Finset.mem_image_of_mem _ i.property⟩
  have hi : Function.Injective inc := by
    intro a b h
    have hval := congrArg (fun j : t => j.val) h
    exact Subtype.ext (Subtype.ext hval)
  exact (PhysicalCompensatedSource.packetFamily_independent t ht).comp inc hi

theorem span_packets_closure :
    (Submodule.span ℝ (Set.range fun q : Index =>
      (packet q : ThresholdHilbert))).topologicalClosure = mixedClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      exact (packet q).property
    · exact isClosed_closure
  · change (⨆ N : ℕ, mixedSpace (Finset.Icc 2 N)).topologicalClosure ≤ _
    apply Submodule.topologicalClosure_mono
    apply iSup_le
    intro N
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨hq, hp⟩ := Finset.mem_filter.mp q.property
    exact Submodule.subset_span ⟨⟨q.val, (Finset.mem_Icc.mp hq).1, hp⟩, rfl⟩

private theorem packet_span_orthogonal :
    (Submodule.span ℝ (Set.range packet))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hz : (x : ThresholdHilbert) ∈ mixedClosureᗮ := by
    apply Submodule.orthogonal_le span_packets_closure.ge
    rw [Submodule.orthogonal_closure]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, rfl⟩ := hz
      exact hx (packet q) (Submodule.subset_span (Set.mem_range_self q))
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  apply (Submodule.mem_bot ℝ).mpr
  apply Subtype.ext
  exact inner_self_eq_zero.mp (hz x x.property)

private instance mixed_complete : CompleteSpace mixedClosure :=
  (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure).completeSpace_coe

/-- The conductor-ordered Pareto Hilbert basis of the mixed closure. -/
def basis : HilbertBasis Index ℝ mixedClosure :=
  HilbertBasis.mkOfOrthogonalEqBot (gramSchmidtNormed_orthonormal packet_independent) (by
    rw [span_gramSchmidtNormed_range, span_gramSchmidt, packet_span_orthogonal])

theorem basis_apply (q : Index) : basis q = gramSchmidtNormed ℝ packet q := by
  simp only [basis, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The raw mixed packets have dense span inside the mixed Hilbert space. -/
theorem packet_span_dense :
    (Submodule.span ℝ (Set.range packet)).topologicalClosure = ⊤ := by
  have h := basis.dense_span
  have hb : (⇑basis : Index → mixedClosure) = gramSchmidtNormed ℝ packet := funext basis_apply
  rwa [hb, span_gramSchmidtNormed_range, span_gramSchmidt] at h

/-- At each mixed conductor the modes and the raw packets span the same finite prefix. -/
theorem basis_span_through (q : Index) :
    Submodule.span ℝ (basis '' Set.Iic q) = Submodule.span ℝ (packet '' Set.Iic q) := by
  have hb : (⇑basis : Index → mixedClosure) = gramSchmidtNormed ℝ packet := funext basis_apply
  rw [hb, span_gramSchmidtNormed, span_gramSchmidt_Iic]

/-- Reconstruction in the complete physical norm. -/
theorem hasSum_modes (x : mixedClosure) :
    HasSum (fun q : Index => inner ℝ (basis q) x • basis q) x := by
  simpa only [HilbertBasis.repr_apply_apply] using basis.hasSum_repr x

/-- Closed coordinate block for a set of conductor labels. -/
def block (s : Set Index) : Submodule ℝ mixedClosure :=
  (Submodule.span ℝ (basis '' s)).topologicalClosure

instance block_hasOrthogonalProjection (s : Set Index) : (block s).HasOrthogonalProjection := by
  unfold block
  infer_instance

theorem basis_mem_block {s : Set Index} {q : Index} (hq : q ∈ s) : basis q ∈ block s :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, hq, rfl⟩)

private theorem basis_mem_block_orthogonal {s : Set Index} {q : Index} (hq : q ∉ s) :
    basis q ∈ (block s)ᗮ := by
  rw [block, Submodule.orthogonal_closure]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    exact basis.orthonormal.2 (fun h => hq (h ▸ hi))
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]

/-- A block contains exactly the vectors whose coefficients vanish outside its labels. -/
theorem mem_block_iff (s : Set Index) (x : mixedClosure) :
    x ∈ block s ↔ ∀ q ∉ s, inner ℝ (basis q) x = 0 := by
  constructor
  · intro hx q hq
    exact inner_eq_zero_symm.mp (basis_mem_block_orthogonal hq x hx)
  · intro hx
    apply (show IsClosed (block s : Set mixedClosure) from isClosed_closure).mem_of_tendsto
      (hasSum_modes x)
    apply Eventually.of_forall
    intro t
    apply (block s).sum_mem
    intro q _
    by_cases hq : q ∈ s
    · exact (block s).smul_mem _ (basis_mem_block hq)
    · rw [hx q hq, zero_smul]
      exact (block s).zero_mem

/-- Complementary sets of labels give orthogonal complements inside the mixed closure. -/
theorem block_compl (s : Set Index) : block sᶜ = (block s)ᗮ := by
  classical
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, hq, rfl⟩
      exact basis_mem_block_orthogonal hq
    · exact (block s).isClosed_orthogonal
  · intro x hx
    apply (mem_block_iff _ _).mpr
    intro q hq
    exact hx (basis q) (basis_mem_block (by simpa using hq))

/-- The closed span of a selected family of raw mixed packets. -/
def packetBlock (s : Set Index) : Submodule ℝ mixedClosure :=
  (Submodule.span ℝ (packet '' s)).topologicalClosure

instance packetBlock_hasOrthogonalProjection (s : Set Index) :
    (packetBlock s).HasOrthogonalProjection := by
  unfold packetBlock
  infer_instance

/-- At conductor `q`, Gram–Schmidt subtracts exactly the orthogonal projection onto the
earlier raw packet span in the original Pareto norm. -/
theorem gramSchmidt_eq_packet_residual (q : Index) :
    gramSchmidt ℝ packet q =
      packet q - (packetBlock (Set.Iio q)).starProjection (packet q) := by
  let K := packetBlock (Set.Iio q)
  have hspan : Submodule.span ℝ (gramSchmidt ℝ packet '' Set.Iio q) ≤ K := by
    rw [span_gramSchmidt_Iio]
    exact Submodule.le_topologicalClosure _
  have hm : packet q - gramSchmidt ℝ packet q ∈ K := by
    rw [gramSchmidt_def, sub_sub_cancel]
    apply K.sum_mem
    intro i hi
    have hi' : i < q := Finset.mem_Iio.mp hi
    have hline : (ℝ ∙ gramSchmidt ℝ packet i) ≤ K :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
        (hspan (Submodule.subset_span ⟨i, hi', rfl⟩)))
    exact hline ((ℝ ∙ gramSchmidt ℝ packet i).starProjection_apply_mem _)
  have ho : gramSchmidt ℝ packet q ∈ Kᗮ := by
    change gramSchmidt ℝ packet q ∈ (Submodule.span ℝ (packet '' Set.Iio q)).topologicalClosureᗮ
    rw [Submodule.orthogonal_closure]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      exact inner_eq_zero_symm.mp (gramSchmidt_inv_triangular ℝ packet hi)
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  have hp : K.starProjection (packet q) = packet q - gramSchmidt ℝ packet q :=
    Submodule.eq_starProjection_of_mem_orthogonal hm (by rwa [sub_sub_cancel])
  change gramSchmidt ℝ packet q = packet q - K.starProjection (packet q)
  rw [hp, sub_sub_cancel]

/-- The other raw packets after projection off the selected packet space. -/
def screenedComplement (s : Set Index) : Submodule ℝ mixedClosure :=
  (Submodule.span ℝ ((fun q => (packetBlock s)ᗮ.starProjection (packet q)) ''
    sᶜ)).topologicalClosure

/-- For an arbitrary arithmetic selection the screened complementary packets exhaust exactly
the orthogonal complement of the selected raw packet block. -/
theorem screenedComplement_eq_orthogonal (s : Set Index) :
    screenedComplement s = (packetBlock s)ᗮ := by
  classical
  let K := packetBlock s
  let Q := Kᗮ.starProjection
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, _, rfl⟩
      exact Kᗮ.starProjection_apply_mem _
    · exact K.isClosed_orthogonal
  · have hpre : (⊤ : Submodule ℝ mixedClosure) ≤
        (screenedComplement s).comap Q.toLinearMap := by
      rw [← packet_span_dense]
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro _ ⟨q, rfl⟩
        change Q (packet q) ∈ screenedComplement s
        by_cases hq : q ∈ s
        · have hmem : packet q ∈ K :=
            Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, hq, rfl⟩)
          change Kᗮ.starProjection (packet q) ∈ screenedComplement s
          rw [Submodule.starProjection_orthogonal_val,
            Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
          exact (screenedComplement s).zero_mem
        · exact Submodule.le_topologicalClosure _
            (Submodule.subset_span ⟨q, hq, rfl⟩)
      · have hc : IsClosed (screenedComplement s : Set mixedClosure) := isClosed_closure
        exact hc.preimage Q.continuous
    intro x hx
    have h : Kᗮ.starProjection x ∈ screenedComplement s :=
      hpre (show x ∈ (⊤ : Submodule ℝ mixedClosure) from trivial)
    rwa [Submodule.starProjection_eq_self_iff.mpr hx] at h

/-- Six is the first mixed conductor. -/
def six : Index := ⟨6, by decide, by decide⟩

/-- The first mode is the original conductor-six packet with unit norm. -/
theorem basis_six : basis six = ‖packet six‖⁻¹ • packet six := by
  have hempty : Finset.Iio six = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hlt : q < six := Finset.mem_Iio.mp hq
    have hv : q.val < 6 := hlt
    have hall (n : ℕ) (lo : 2 ≤ n) (hi : n ≤ 5) : IsPrimePow n := by
      interval_cases n
      · exact Nat.prime_two.isPrimePow
      · exact Nat.prime_three.isPrimePow
      · decide
      · exact (show Nat.Prime 5 by norm_num).isPrimePow
    exact q.property.2 (hall _ q.property.1 (by omega))
  have hfirst : gramSchmidt ℝ packet six = packet six := by
    rw [gramSchmidt_def, hempty]
    simp
  rw [basis_apply, gramSchmidtNormed, hfirst]
  rfl

/-- The first term of the mixed Parseval series for the parity packet. -/
theorem parity_six_coefficient_sq :
    (inner ℝ (basis six : ThresholdHilbert) (ramanujanPacketHilbert 2)) ^ 2 =
      (Real.log 2 - Real.pi / (2 * Real.sqrt 3)) ^ 2 / (Real.pi / Real.sqrt 3) := by
  rw [basis_six]
  change (inner ℝ (‖ramanujanPacketHilbert 6‖⁻¹ • ramanujanPacketHilbert 6)
    (ramanujanPacketHilbert 2)) ^ 2 = _
  rw [real_inner_smul_left, real_inner_comm (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 6),
    packet_two_six_inner_and_norm.1, mul_pow, inv_pow, packet_two_six_inner_and_norm.2]
  ring

/-- For an ambient datum the squared coefficients add to its mixed projection energy. -/
theorem projection_parseval (x : ThresholdHilbert) :
    (∑' q : Index, (inner ℝ (basis q : ThresholdHilbert) x) ^ 2) =
      ‖mixedClosure.starProjection x‖ ^ 2 := by
  let p := mixedClosure.orthogonalProjectionOnto x
  have hp (q : Index) : inner ℝ (basis q) p = inner ℝ (basis q : ThresholdHilbert) x := by
    have h := mixedClosure.sub_starProjection_mem_orthogonal x
      (basis q : ThresholdHilbert) (basis q).property
    rw [inner_sub_right, sub_eq_zero] at h
    exact h.symm
  calc
    _ = ∑' q : Index, inner ℝ p (basis q) * inner ℝ (basis q) p := by
      apply tsum_congr
      intro q
      rw [real_inner_comm (basis q) p, hp, pow_two]
    _ = ‖p‖ ^ 2 := (basis.tsum_inner_mul_inner p p).trans (real_inner_self_eq_norm_sq p)

open CoefficientStabilization in
/-- The sharp endpoint for the mixed Fourier coefficients of parity is equivalent to legality
of the ambient constant. -/
theorem parity_saturation_iff_one_mem :
    (∑' q : Index, (inner ℝ (basis q : ThresholdHilbert) (ramanujanPacketHilbert 2)) ^ 2) =
      Real.log 2 - (Real.log 2) ^ 2 ↔ hilbertOne ∈ closedSpace := by
  rw [projection_parseval, full_mixed_capture_eq_limitEnergy, ← limitEnergy_zero_iff_mem]
  constructor
  · intro h
    have he : (Real.log 2) ^ 2 / (1 - limitEnergy) = (Real.log 2) ^ 2 := by linarith
    have hm := (div_eq_iff one_sub_limitEnergy_pos.ne').mp he
    have hn : (Real.log 2) ^ 2 ≠ 0 := (sq_pos_of_pos (Real.log_pos (by norm_num))).ne'
    have heq : (1 : ℝ) = 1 - limitEnergy := by
      apply mul_left_cancel₀ hn
      simpa only [mul_one] using hm
    linarith
  · intro h
    simp [h]

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

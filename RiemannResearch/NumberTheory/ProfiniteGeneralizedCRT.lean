import RiemannResearch.NumberTheory.FiniteGeneralizedCRT
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Separation.Hausdorff

/-!
# Profinite CRT for an arbitrary family of positive moduli

The inverse limit is the closed subring of all compatible positive-modulus
residue tuples. The finite generalized CRT gives the finite intersection
property for any family of prescribed reductions. For the inverse-limit
description, see Gareth Wilkes, Profinite Groups and Group Cohomology,
Section 2.2, https://www.dpmms.cam.ac.uk/~grw46/LectureNotes.pdf.
-/

namespace RiemannResearch.NumberTheory.GeneralizedCRT

/-- The positive moduli indexing the full divisibility system. -/
abbrev PositiveModulus := {n : ℕ // n ≠ 0}

instance (n : PositiveModulus) : NeZero n.val := ⟨n.property⟩

/-- The inverse-limit subring of compatible residues at all positive moduli. -/
def profiniteRing : Subring ((n : PositiveModulus) → ZMod n.val) where
  carrier := {f | ∀ (m n : PositiveModulus) (h : m.val ∣ n.val),
    ZMod.castHom h (ZMod m.val) (f n) = f m}
  zero_mem' := fun m n h => map_zero (ZMod.castHom h (ZMod m.val))
  one_mem' := fun m n h => map_one (ZMod.castHom h (ZMod m.val))
  neg_mem' := by
    intro a ha m n h
    change ZMod.castHom h (ZMod m.val) (-(a n)) = -(a m)
    rw [map_neg, ha m n h]
  add_mem' := by
    intro a b ha hb m n h
    change ZMod.castHom h (ZMod m.val) (a n + b n) = a m + b m
    rw [map_add, ha m n h, hb m n h]
  mul_mem' := by
    intro a b ha hb m n h
    change ZMod.castHom h (ZMod m.val) (a n * b n) = a m * b m
    rw [map_mul, ha m n h, hb m n h]

/-- The profinite integers in the all-modulus inverse-limit model. -/
abbrev ProfiniteInt := ↥profiniteRing

/-- The canonical reduction of a profinite integer. -/
def reduce (n : PositiveModulus) : ProfiniteInt →+* ZMod n.val where
  toFun x := x.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem reduce_compatible (x : ProfiniteInt) {m n : PositiveModulus} (h : m.val ∣ n.val) :
    ZMod.castHom h (ZMod m.val) (reduce n x) = reduce m x :=
  x.property m n h

theorem continuous_reduce (n : PositiveModulus) : Continuous (reduce n) :=
  (continuous_apply n).comp continuous_subtype_val

private theorem isClosed_profiniteRing :
    IsClosed (profiniteRing : Set ((n : PositiveModulus) → ZMod n.val)) := by
  change IsClosed {f : (n : PositiveModulus) → ZMod n.val |
    ∀ (m n : PositiveModulus) (h : m.val ∣ n.val),
      ZMod.castHom h (ZMod m.val) (f n) = f m}
  simp_rw [Set.ofPred_forall]
  exact isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

instance : CompactSpace ProfiniteInt :=
  isCompact_iff_compactSpace.mp isClosed_profiniteRing.isCompact

/-- Pairwise gcd compatibility characterizes arbitrary families of prescribed
residues that can be realized by a single profinite integer. -/
theorem exists_profiniteInt_iff_pairwise {ι : Type*}
    (m : ι → PositiveModulus) (a : ι → ℤ) :
    (∃ x : ProfiniteInt, ∀ i, reduce (m i) x = (a i : ZMod (m i).val)) ↔
      ∀ i j, Int.ModEq ((m i).val.gcd (m j).val : ℤ) (a i) (a j) := by
  classical
  constructor
  · rintro ⟨x, hx⟩ i j
    let d : PositiveModulus :=
      ⟨(m i).val.gcd (m j).val,
        (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (m i).property)).ne'⟩
    have hi := reduce_compatible x (m := d) (n := m i) (Nat.gcd_dvd_left _ _)
    have hj := reduce_compatible x (m := d) (n := m j) (Nat.gcd_dvd_right _ _)
    rw [hx i, map_intCast] at hi
    rw [hx j, map_intCast] at hj
    exact (ZMod.intCast_eq_intCast_iff (a i) (a j) d.val).mp (hi.trans hj.symm)
  · intro ha
    let F (i : ι) : Set ProfiniteInt :=
      {x | reduce (m i) x = (a i : ZMod (m i).val)}
    have hclosed (i : ι) : IsClosed (F i) := isClosed_eq (continuous_reduce _) continuous_const
    have hfinite (s : Finset ι) :
        ((Set.univ : Set ProfiniteInt) ∩ ⋂ i ∈ s, F i).Nonempty := by
      obtain ⟨z, hz⟩ :=
        (exists_int_modEq_iff_pairwise s (fun i => (m i).val) a).mpr
          (fun i _ j _ => ha i j)
      refine ⟨(z : ProfiniteInt), Set.mem_univ _, Set.mem_iInter₂.mpr (fun i hi => ?_)⟩
      change reduce (m i) (z : ProfiniteInt) = _
      rw [map_intCast]
      exact (ZMod.intCast_eq_intCast_iff z (a i) (m i).val).mpr (hz i hi)
    obtain ⟨x, hx⟩ := isCompact_univ.inter_iInter_nonempty F hclosed hfinite
    exact ⟨x, Set.mem_iInter.mp hx.2⟩

/-- A family of moduli whose finite lcms are cofinal determines a profinite integer. -/
theorem profiniteInt_ext_of_lcm_cofinal {ι : Type*}
    (m : ι → PositiveModulus)
    (hcover : ∀ n : PositiveModulus, ∃ s : Finset ι, n.val ∣ s.lcm (fun i => (m i).val))
    {x y : ProfiniteInt} (hxy : ∀ i, reduce (m i) x = reduce (m i) y) : x = y := by
  apply Subtype.ext
  funext n
  obtain ⟨s, hs⟩ := hcover n
  let L : PositiveModulus :=
    ⟨s.lcm (fun i => (m i).val), Finset.lcm_ne_zero_iff.mpr (fun i _ => (m i).property)⟩
  let : NeZero L.val := ⟨L.property⟩
  have hL : reduce L x = reduce L y := by
    let a := (reduce L x).val
    let b := (reduce L y).val
    have ha : ((a : ℤ) : ZMod L.val) = reduce L x := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val _
    have hb : ((b : ℤ) : ZMod L.val) = reduce L y := by
      rw [Int.cast_natCast]
      exact ZMod.natCast_zmod_val _
    rw [← ha, ← hb]
    apply (ZMod.intCast_eq_intCast_iff (a : ℤ) (b : ℤ) L.val).mpr
    apply (int_modEq_lcm_iff s (fun i => (m i).val) (a : ℤ) (b : ℤ)).mpr
    intro i hi
    have hd : (m i).val ∣ L.val := Finset.dvd_lcm hi
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    have hax := congrArg (ZMod.castHom hd (ZMod (m i).val)) ha
    have hby := congrArg (ZMod.castHom hd (ZMod (m i).val)) hb
    rw [map_intCast, reduce_compatible] at hax hby
    exact hax.trans ((hxy i).trans hby.symm)
  change reduce n x = reduce n y
  rw [← reduce_compatible x (m := n) (n := L) hs,
    ← reduce_compatible y (m := n) (n := L) hs, hL]

end RiemannResearch.NumberTheory.GeneralizedCRT

/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Tactic.FinCases
import RiemannResearch.LinearAlgebra.RootSystem.D4SplitFock

/-!
# Faithfulness of the split D4 exterior-Fock representation

Explicit creation, annihilation, and vacuum projectors realize every matrix
unit of the 16-dimensional exterior Fock space in the Clifford action image.
The full action is therefore surjective. Equality of the two 256-dimensional
spaces then gives injectivity, removing the last hypothesis from the
split-D4 even-Clifford and half-spin decomposition.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra
open RiemannResearch.LinearAlgebra.CliffordEven

universe u
variable {K : Type u} [Field K]

theorem contractLeft_ιMulti_eq_zero_of_forall
    {U : Type*} [AddCommGroup U] [Module K U]
    (d : Module.Dual K U) :
    ∀ (n : ℕ) (v : Fin n → U),
      (∀ i, d (v i) = 0) →
      CliffordAlgebra.contractLeft d
        (ExteriorAlgebra.ιMulti K n v) = 0 := by
  intro n
  induction n with
  | zero =>
      intro v _h
      rw [ExteriorAlgebra.ιMulti_zero_apply,
        CliffordAlgebra.contractLeft_one]
  | succ n ih =>
      intro v h
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        CliffordAlgebra.contractLeft_ι_mul, h]
      have htail : ∀ i, d (Matrix.vecTail v i) = 0 :=
        fun i => h i.succ
      rw [ih (Matrix.vecTail v) htail]
      simp

theorem splitFock_annihilation_basis_eq_zero_of_not_mem
    (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∉ s) :
    CliffordAlgebra.contractLeft
        ((Pi.basisFun K (Fin 4)).dualBasis i)
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun K (Fin 4)) rfl]
  apply contractLeft_ιMulti_eq_zero_of_forall
  intro j
  change ((Pi.basisFun K (Fin 4)).dualBasis i)
    ((Pi.basisFun K (Fin 4)) ((s.orderEmbOfFin rfl) j)) = 0
  rw [Module.Basis.dualBasis_apply_self, if_neg]
  intro heq
  apply hi
  rw [← heq]
  apply Finset.orderEmbOfFin_mem

theorem splitFock_basis_singleton (i : Fin 4) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra {i} =
      ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) := by
  rw [ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun K (Fin 4)) (Finset.card_singleton i)]
  rw [show ExteriorAlgebra.ιMulti_family K 1
        (⇑(Pi.basisFun K (Fin 4)))
        (Set.powersetCard.ofCard (Finset.card_singleton i)) =
      ExteriorAlgebra.ιMulti K 1
        (fun j => (Pi.basisFun K (Fin 4))
          ((({i} : Finset (Fin 4)).orderEmbOfFin
            (Finset.card_singleton i)) j)) by rfl]
  rw [ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply]
  simp

noncomputable def splitFockEraseSign
    (i : Fin 4) (s : Finset (Fin 4)) : ℤˣ :=
  let si : Set.powersetCard (Fin 4) 1 :=
    Set.powersetCard.ofCard (Finset.card_singleton i)
  let se : Set.powersetCard (Fin 4) (s.erase i).card :=
    Set.powersetCard.ofCard rfl
  let hdis : Disjoint (si : Finset (Fin 4))
      (se : Finset (Fin 4)) := by
    change Disjoint ({i} : Finset (Fin 4)) (s.erase i)
    simp
  Equiv.Perm.sign (Set.powersetCard.permOfDisjoint hdis)

theorem splitFock_basis_singleton_mul_erase
    (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra {i} *
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra (s.erase i) =
      splitFockEraseSign i s •
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra s := by
  let si : Set.powersetCard (Fin 4) 1 :=
    Set.powersetCard.ofCard (Finset.card_singleton i)
  let se : Set.powersetCard (Fin 4) (s.erase i).card :=
    Set.powersetCard.ofCard rfl
  let hdis : Disjoint (si : Finset (Fin 4))
      (se : Finset (Fin 4)) := by
    change Disjoint ({i} : Finset (Fin 4)) (s.erase i)
    simp
  have h := ExteriorAlgebra.basis_mul_of_disjoint
    (Pi.basisFun K (Fin 4)) si se hdis
  simpa [si, se, splitFockEraseSign,
    Finset.disjUnion_eq_union, hi] using h

theorem splitFock_annihilation_basis_eq_of_mem
    (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s) :
    CliffordAlgebra.contractLeft
        ((Pi.basisFun K (Fin 4)).dualBasis i)
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) =
      splitFockEraseSign i s •
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra (s.erase i) := by
  have hmul := splitFock_basis_singleton_mul_erase
    (K := K) i s hi
  rw [splitFock_basis_singleton] at hmul
  have h := congrArg
    (CliffordAlgebra.contractLeft
      ((Pi.basisFun K (Fin 4)).dualBasis i)) hmul
  rw [CliffordAlgebra.contractLeft_ι_mul,
    Module.Basis.dualBasis_apply_self, if_pos rfl,
    splitFock_annihilation_basis_eq_zero_of_not_mem i
      (s.erase i) (by
        intro him
        exact (Finset.mem_erase.mp him).1 rfl)] at h
  have h' :
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra (s.erase i) =
        splitFockEraseSign i s •
          CliffordAlgebra.contractLeft
            ((Pi.basisFun K (Fin 4)).dualBasis i)
            ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) := by
    simpa only [one_smul, mul_zero, sub_zero, Units.smul_def,
      map_zsmul] using h
  let ε := splitFockEraseSign i s
  have heps : ε * ε = 1 := by
    rw [← pow_two]
    exact Int.units_sq ε
  change _ = ε • _
  change _ = ε • _ at h'
  calc
    CliffordAlgebra.contractLeft
        ((Pi.basisFun K (Fin 4)).dualBasis i)
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) =
      (1 : ℤˣ) •
        CliffordAlgebra.contractLeft
          ((Pi.basisFun K (Fin 4)).dualBasis i)
          ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) := by simp
    _ = (ε * ε) •
        CliffordAlgebra.contractLeft
          ((Pi.basisFun K (Fin 4)).dualBasis i)
          ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) := by
      rw [heps]
    _ = ε • (ε •
        CliffordAlgebra.contractLeft
          ((Pi.basisFun K (Fin 4)).dualBasis i)
          ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s)) := by
      rw [mul_smul]
    _ = ε •
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra (s.erase i) := by
      rw [← h']

theorem splitFock_creation_basis_eq_zero_of_mem
    (i : Fin 4) (s : Finset (Fin 4)) (hi : i ∈ s) :
    ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra s = 0 := by
  rw [← splitFock_basis_singleton i]
  apply ExteriorAlgebra.basis_mul_of_not_disjoint
      (Pi.basisFun K (Fin 4))
      (Set.powersetCard.ofCard (Finset.card_singleton i))
      (Set.powersetCard.ofCard rfl)
  simpa using hi

noncomputable def splitFockModeVacuumProjection (i : Fin 4) :
    Module.End K (SplitFockSpace K) :=
  exteriorAnnihilation ((Pi.basisFun K (Fin 4)).dualBasis i) *
    exteriorCreation ((Pi.basisFun K (Fin 4)) i)

theorem splitFockModeVacuumProjection_apply_basis
    (i : Fin 4) (s : Finset (Fin 4)) :
    splitFockModeVacuumProjection (K := K) i
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) =
      if i ∈ s then 0
      else (Pi.basisFun K (Fin 4)).ExteriorAlgebra s := by
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    simp only [splitFockModeVacuumProjection, Module.End.mul_apply,
      exteriorAnnihilation, exteriorCreation]
    change CliffordAlgebra.contractLeft
      ((Pi.basisFun K (Fin 4)).dualBasis i)
      (ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra s) = 0
    rw [splitFock_creation_basis_eq_zero_of_mem i s hi]
    exact map_zero _
  · rw [if_neg hi]
    simp only [splitFockModeVacuumProjection, Module.End.mul_apply,
      exteriorAnnihilation, exteriorCreation]
    change CliffordAlgebra.contractLeft
      ((Pi.basisFun K (Fin 4)).dualBasis i)
      (ExteriorAlgebra.ι K ((Pi.basisFun K (Fin 4)) i) *
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra s) =
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra s
    rw [CliffordAlgebra.contractLeft_ι_mul,
      Module.Basis.dualBasis_apply_self, if_pos rfl,
      splitFock_annihilation_basis_eq_zero_of_not_mem i s hi]
    simp

noncomputable def splitFockVacuumProjection :
    Module.End K (SplitFockSpace K) :=
  splitFockModeVacuumProjection (K := K) 0 *
    splitFockModeVacuumProjection (K := K) 1 *
    splitFockModeVacuumProjection (K := K) 2 *
    splitFockModeVacuumProjection (K := K) 3

theorem splitFockVacuumProjection_apply_basis
    (s : Finset (Fin 4)) :
    splitFockVacuumProjection (K := K)
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra s) =
      if s = ∅ then
        (Pi.basisFun K (Fin 4)).ExteriorAlgebra ∅
      else 0 := by
  by_cases hs : s = ∅
  · subst s
    simp [splitFockVacuumProjection, Module.End.mul_apply,
      splitFockModeVacuumProjection_apply_basis]
  · rw [if_neg hs]
    fin_cases s <;>
      simp_all [splitFockVacuumProjection, Module.End.mul_apply,
        splitFockModeVacuumProjection_apply_basis]

theorem splitFockVacuumProjection_eq_end :
    splitFockVacuumProjection (K := K) =
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end (∅, ∅) := by
  apply (Pi.basisFun K (Fin 4)).ExteriorAlgebra.ext
  intro s
  rw [splitFockVacuumProjection_apply_basis,
    Module.Basis.end_apply_apply]
  by_cases hs : s = ∅
  · subst s
    simp
  · simp [hs, Ne.symm hs]

theorem splitFock_annihilation_mem_range (i : Fin 4) :
    exteriorAnnihilation
        ((Pi.basisFun K (Fin 4)).dualBasis i) ∈
      (splitFockCliffordAction K).range := by
  rw [AlgHom.mem_range]
  refine ⟨CliffordAlgebra.ι (splitD4Form K)
    (((Pi.basisFun K (Fin 4)).dualBasis i), 0), ?_⟩
  change exteriorCliffordAction
      (CliffordAlgebra.ι
        (QuadraticForm.dualProd K (Fin 4 → K))
        (((Pi.basisFun K (Fin 4)).dualBasis i), 0)) =
    exteriorAnnihilation ((Pi.basisFun K (Fin 4)).dualBasis i)
  rw [exteriorCliffordAction_ι]
  apply LinearMap.ext
  intro z
  simp [exteriorFockGenerator_apply, exteriorAnnihilation]

theorem splitFock_creation_mem_range (v : Fin 4 → K) :
    exteriorCreation v ∈ (splitFockCliffordAction K).range := by
  rw [AlgHom.mem_range]
  refine ⟨CliffordAlgebra.ι (splitD4Form K) (0, v), ?_⟩
  change exteriorCliffordAction
      (CliffordAlgebra.ι
        (QuadraticForm.dualProd K (Fin 4 → K)) (0, v)) =
    exteriorCreation v
  rw [exteriorCliffordAction_ι]
  apply LinearMap.ext
  intro z
  simp [exteriorFockGenerator_apply, exteriorCreation]

theorem splitFockModeVacuumProjection_mem_range (i : Fin 4) :
    splitFockModeVacuumProjection (K := K) i ∈
      (splitFockCliffordAction K).range :=
  (splitFockCliffordAction K).range.mul_mem
    (splitFock_annihilation_mem_range i)
    (splitFock_creation_mem_range
      ((Pi.basisFun K (Fin 4)) i))

theorem splitFockVacuumProjection_mem_range :
    splitFockVacuumProjection (K := K) ∈
      (splitFockCliffordAction K).range :=
  (splitFockCliffordAction K).range.mul_mem
    ((splitFockCliffordAction K).range.mul_mem
      ((splitFockCliffordAction K).range.mul_mem
        (splitFockModeVacuumProjection_mem_range (K := K) 0)
        (splitFockModeVacuumProjection_mem_range (K := K) 1))
      (splitFockModeVacuumProjection_mem_range (K := K) 2))
    (splitFockModeVacuumProjection_mem_range (K := K) 3)

noncomputable def splitFockAnnihilationWord :
    List (Fin 4) → Module.End K (SplitFockSpace K)
  | [] => 1
  | i :: l => splitFockAnnihilationWord l *
      exteriorAnnihilation ((Pi.basisFun K (Fin 4)).dualBasis i)

noncomputable def splitFockAnnihilationSign :
    List (Fin 4) → Finset (Fin 4) → ℤˣ
  | [], _ => 1
  | i :: l, t =>
      splitFockEraseSign i t *
        splitFockAnnihilationSign l (t.erase i)

theorem splitFockAnnihilationWord_apply_basis_of_subset :
    ∀ (l : List (Fin 4)) (t : Finset (Fin 4)),
      l.Nodup →
      l.toFinset ⊆ t →
      splitFockAnnihilationWord (K := K) l
          ((Pi.basisFun K (Fin 4)).ExteriorAlgebra t) =
        splitFockAnnihilationSign l t •
          (Pi.basisFun K (Fin 4)).ExteriorAlgebra
            (t \ l.toFinset) := by
  intro l
  induction l with
  | nil =>
      intro t _hn _hs
      simp [splitFockAnnihilationWord,
        splitFockAnnihilationSign]
  | cons i l ih =>
      intro t hn hs
      have hi : i ∈ t := hs (by simp)
      have hil : i ∉ l := (List.nodup_cons.mp hn).1
      have hsub : l.toFinset ⊆ t.erase i := by
        intro j hj
        rw [Finset.mem_erase]
        constructor
        · intro hji
          apply hil
          simpa [hji] using hj
        · exact hs (by simp [hj])
      simp only [splitFockAnnihilationWord, Module.End.mul_apply,
        exteriorAnnihilation]
      rw [splitFock_annihilation_basis_eq_of_mem i t hi]
      rw [Units.smul_def, map_zsmul, ← Units.smul_def]
      rw [ih (t.erase i) (List.nodup_cons.mp hn).2 hsub]
      simp only [splitFockAnnihilationSign, mul_smul]
      have herase :
          t.erase i \ l.toFinset =
            t \ (i :: l).toFinset := by
        ext j
        simp only [List.toFinset_cons, Finset.mem_sdiff,
          Finset.mem_erase, Finset.mem_insert]
        tauto
      rw [herase]

theorem splitFockAnnihilationWord_apply_basis_of_not_subset :
    ∀ (l : List (Fin 4)) (t : Finset (Fin 4)),
      l.Nodup →
      ¬ l.toFinset ⊆ t →
      splitFockAnnihilationWord (K := K) l
          ((Pi.basisFun K (Fin 4)).ExteriorAlgebra t) = 0 := by
  intro l
  induction l with
  | nil =>
      intro t _hn hs
      exfalso
      apply hs
      simp
  | cons i l ih =>
      intro t hn hs
      simp only [splitFockAnnihilationWord, Module.End.mul_apply,
        exteriorAnnihilation]
      by_cases hi : i ∈ t
      · rw [splitFock_annihilation_basis_eq_of_mem i t hi]
        rw [Units.smul_def, map_zsmul, ← Units.smul_def]
        have hnot : ¬ l.toFinset ⊆ t.erase i := by
          intro hsub
          apply hs
          intro j hj
          rw [List.mem_toFinset, List.mem_cons] at hj
          rcases hj with rfl | hj
          · exact hi
          · exact (Finset.mem_erase.mp (hsub (by
              simpa using hj))).2
        rw [ih (t.erase i) (List.nodup_cons.mp hn).2 hnot]
        simp
      · rw [splitFock_annihilation_basis_eq_zero_of_not_mem i t hi]
        exact map_zero _

theorem splitFockAnnihilationWord_mem_range
    (l : List (Fin 4)) :
    splitFockAnnihilationWord (K := K) l ∈
      (splitFockCliffordAction K).range := by
  induction l with
  | nil =>
      exact (splitFockCliffordAction K).range.one_mem
  | cons i l ih =>
      exact (splitFockCliffordAction K).range.mul_mem ih
        (splitFock_annihilation_mem_range i)

noncomputable def splitFockVacuumRowRaw
    (s : Finset (Fin 4)) :
    Module.End K (SplitFockSpace K) :=
  splitFockVacuumProjection *
    splitFockAnnihilationWord (s.sort (· ≤ ·))

theorem splitFockVacuumRowRaw_apply_basis
    (s t : Finset (Fin 4)) :
    splitFockVacuumRowRaw (K := K) s
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra t) =
      if t = s then
        splitFockAnnihilationSign (s.sort (· ≤ ·)) s •
          (Pi.basisFun K (Fin 4)).ExteriorAlgebra ∅
      else 0 := by
  simp only [splitFockVacuumRowRaw, Module.End.mul_apply]
  by_cases hts : t = s
  · subst t
    rw [if_pos rfl]
    rw [splitFockAnnihilationWord_apply_basis_of_subset
      (s.sort (· ≤ ·)) s
      (Finset.sort_nodup s (· ≤ ·)) (by
        rw [Finset.sort_toFinset])]
    rw [Units.smul_def, map_zsmul, ← Units.smul_def]
    rw [splitFockVacuumProjection_apply_basis]
    simp [Finset.sort_toFinset]
  · rw [if_neg hts]
    by_cases hsub : s ⊆ t
    · rw [splitFockAnnihilationWord_apply_basis_of_subset
        (s.sort (· ≤ ·)) t
        (Finset.sort_nodup s (· ≤ ·)) (by
          simpa [Finset.sort_toFinset] using hsub)]
      rw [Units.smul_def, map_zsmul, ← Units.smul_def]
      rw [splitFockVacuumProjection_apply_basis]
      have hdiff : t \ s ≠ ∅ := by
        intro he
        apply hts
        have hback : t ⊆ s := by
          intro i hi
          by_contra his
          have him : i ∈ t \ s := by simp [hi, his]
          simp [he] at him
        exact (Finset.Subset.antisymm hsub hback).symm
      simp [Finset.sort_toFinset, hdiff]
    · rw [splitFockAnnihilationWord_apply_basis_of_not_subset
        (s.sort (· ≤ ·)) t
        (Finset.sort_nodup s (· ≤ ·)) (by
          simpa [Finset.sort_toFinset] using hsub)]
      exact map_zero _

noncomputable def splitFockVacuumRow
    (s : Finset (Fin 4)) :
    Module.End K (SplitFockSpace K) :=
  splitFockAnnihilationSign (s.sort (· ≤ ·)) s •
    splitFockVacuumRowRaw s

theorem splitFockVacuumRow_eq_end
    (s : Finset (Fin 4)) :
    splitFockVacuumRow (K := K) s =
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end (∅, s) := by
  apply (Pi.basisFun K (Fin 4)).ExteriorAlgebra.ext
  intro t
  rw [Module.Basis.end_apply_apply]
  simp only [splitFockVacuumRow]
  change splitFockAnnihilationSign (s.sort (· ≤ ·)) s •
      splitFockVacuumRowRaw (K := K) s
        ((Pi.basisFun K (Fin 4)).ExteriorAlgebra t) =
    (if s = t then
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra ∅ else 0)
  rw [splitFockVacuumRowRaw_apply_basis]
  by_cases hts : t = s
  · subst t
    rw [if_pos rfl, if_pos rfl, smul_smul]
    have heps :
        splitFockAnnihilationSign (s.sort (· ≤ ·)) s *
            splitFockAnnihilationSign (s.sort (· ≤ ·)) s = 1 := by
      rw [← pow_two]
      exact Int.units_sq
        (splitFockAnnihilationSign (s.sort (· ≤ ·)) s)
    rw [heps]
    simp
  · rw [if_neg hts, if_neg (Ne.symm hts)]
    simp

theorem splitFockVacuumRow_mem_range
    (s : Finset (Fin 4)) :
    splitFockVacuumRow (K := K) s ∈
      (splitFockCliffordAction K).range := by
  have hraw :=
    (splitFockCliffordAction K).range.mul_mem
      splitFockVacuumProjection_mem_range
      (splitFockAnnihilationWord_mem_range (s.sort (· ≤ ·)))
  change splitFockAnnihilationSign (s.sort (· ≤ ·)) s •
      splitFockVacuumRowRaw (K := K) s ∈ _
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul K]
  exact (splitFockCliffordAction K).range.smul_mem hraw
    ((splitFockAnnihilationSign
      (s.sort (· ≤ ·)) s : ℤ) : K)

theorem splitFock_basis_empty :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra ∅ = 1 := by
  rw [ExteriorAlgebra.basis_apply_ofCard
    (Pi.basisFun K (Fin 4)) rfl]
  exact ExteriorAlgebra.ιMulti_zero_apply _

theorem splitFock_mulLeft_mem_range
    (z : ExteriorAlgebra K (Fin 4 → K)) :
    LinearMap.mulLeft K z ∈ (splitFockCliffordAction K).range := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap r =>
      have h := (splitFockCliffordAction K).range.algebraMap_mem r
      change LinearMap.mulLeft K
        (algebraMap K (ExteriorAlgebra K (Fin 4 → K)) r) ∈ _
      convert h using 1
      apply LinearMap.ext
      intro x
      simp [LinearMap.mulLeft_apply, Algebra.smul_def]
  | ι v =>
      exact splitFock_creation_mem_range v
  | mul a b ha hb =>
      have h := (splitFockCliffordAction K).range.mul_mem ha hb
      convert h using 1
      apply LinearMap.ext
      intro x
      simp [LinearMap.mulLeft_apply]
  | add a b ha hb =>
      have h := (splitFockCliffordAction K).range.add_mem ha hb
      convert h using 1
      apply LinearMap.ext
      intro x
      simp [LinearMap.mulLeft_apply, add_mul]

noncomputable def splitFockVacuumColumn
    (r : Finset (Fin 4)) :
    Module.End K (SplitFockSpace K) :=
  LinearMap.mulLeft K
    ((Pi.basisFun K (Fin 4)).ExteriorAlgebra r) *
      splitFockVacuumProjection

theorem splitFockVacuumColumn_eq_end
    (r : Finset (Fin 4)) :
    splitFockVacuumColumn (K := K) r =
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end (r, ∅) := by
  apply (Pi.basisFun K (Fin 4)).ExteriorAlgebra.ext
  intro t
  rw [Module.Basis.end_apply_apply]
  simp only [splitFockVacuumColumn, Module.End.mul_apply,
    LinearMap.mulLeft_apply]
  rw [splitFockVacuumProjection_apply_basis]
  by_cases ht : t = ∅
  · subst t
    rw [if_pos rfl, if_pos rfl, splitFock_basis_empty, mul_one]
  · rw [if_neg ht, if_neg (Ne.symm ht), mul_zero]

theorem splitFockVacuumColumn_mem_range
    (r : Finset (Fin 4)) :
    splitFockVacuumColumn (K := K) r ∈
      (splitFockCliffordAction K).range :=
  (splitFockCliffordAction K).range.mul_mem
    (splitFock_mulLeft_mem_range
      ((Pi.basisFun K (Fin 4)).ExteriorAlgebra r))
    splitFockVacuumProjection_mem_range

noncomputable def splitFockMatrixUnit
    (r s : Finset (Fin 4)) :
    Module.End K (SplitFockSpace K) :=
  splitFockVacuumColumn r * splitFockVacuumRow s

theorem splitFockMatrixUnit_eq_end
    (r s : Finset (Fin 4)) :
    splitFockMatrixUnit (K := K) r s =
      (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end (r, s) := by
  rw [splitFockMatrixUnit, splitFockVacuumColumn_eq_end,
    splitFockVacuumRow_eq_end]
  apply (Pi.basisFun K (Fin 4)).ExteriorAlgebra.ext
  intro t
  simp only [Module.End.mul_apply, Module.Basis.end_apply_apply]
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl, if_pos rfl,
      Module.Basis.end_apply_apply, if_pos rfl]
  · simp [hst]

theorem splitFockMatrixUnit_mem_range
    (r s : Finset (Fin 4)) :
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end (r, s) ∈
      (splitFockCliffordAction K).range := by
  rw [← splitFockMatrixUnit_eq_end]
  exact (splitFockCliffordAction K).range.mul_mem
    (splitFockVacuumColumn_mem_range r)
    (splitFockVacuumRow_mem_range s)

theorem splitFockCliffordAction_surjective :
    Function.Surjective (splitFockCliffordAction K) := by
  change Function.Surjective
    (splitFockCliffordAction K).toLinearMap
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end.span_eq]
  apply Submodule.span_le.mpr
  rw [Set.range_subset_iff]
  intro rs
  change ∃ x, (splitFockCliffordAction K).toLinearMap x =
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end rs
  have h := splitFockMatrixUnit_mem_range
    (K := K) rs.1 rs.2
  rw [AlgHom.mem_range] at h
  exact h

noncomputable local instance splitFockFiniteConstructive :
    Module.Finite K (SplitFockSpace K) :=
  Module.Finite.of_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra

noncomputable local instance splitFockEndFiniteConstructive :
    Module.Finite K (Module.End K (SplitFockSpace K)) :=
  Module.Finite.of_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end

theorem splitFockEnd_finrank :
    Module.finrank K (Module.End K (SplitFockSpace K)) = 256 := by
  rw [Module.finrank_eq_card_basis
    (Pi.basisFun K (Fin 4)).ExteriorAlgebra.end]
  simp

variable [Invertible (2 : K)]

noncomputable local instance splitD4ExteriorFiniteConstructive :
    Module.Finite K
      (ExteriorAlgebra K (SplitD4Space K)) :=
  Module.Finite.of_basis (splitD4Basis K).ExteriorAlgebra

noncomputable local instance splitD4CliffordFiniteConstructive :
    Module.Finite K
      (CliffordAlgebra (splitD4Form K)) :=
  Module.Finite.equiv
    (CliffordAlgebra.equivExterior (splitD4Form K)).symm

theorem splitFockCliffordAction_injective :
    Function.Injective (splitFockCliffordAction K) := by
  change Function.Injective
    (splitFockCliffordAction K).toLinearMap
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank K
        (CliffordAlgebra (splitD4Form K)) =
      Module.finrank K
        (Module.End K (SplitFockSpace K)) by
      rw [splitD4Clifford_finrank, splitFockEnd_finrank])
    (f := (splitFockCliffordAction K).toLinearMap)).mpr
      splitFockCliffordAction_surjective


/-- The two concrete parity-block actions give the split even-Clifford
algebra equivalence without any remaining faithfulness hypothesis. -/
noncomputable def splitHalfSpinBlockEquiv :
    CliffordAlgebra.even (splitD4Form K) ≃ₐ[K]
      Module.End K (SplitHalfSpinPlus K) ×
        Module.End K (SplitHalfSpinMinus K) :=
  splitHalfSpinBlockEquiv_of_exteriorCliffordAction_injective K
    splitFockCliffordAction_injective

/-- The unconditional concrete split-D4 half-spin decomposition. -/
noncomputable def splitHalfSpinDecomposition :
    CliffordEven.HalfSpinDecomposition (splitD4Form K)
      (SplitHalfSpinPlus K) (SplitHalfSpinMinus K) :=
  splitHalfSpinDecomposition_of_exteriorCliffordAction_injective K
    splitFockCliffordAction_injective

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality

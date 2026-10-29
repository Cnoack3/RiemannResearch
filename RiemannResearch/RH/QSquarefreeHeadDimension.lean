/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.QSquarefreeHeadCompression
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-!
# Dimension and triangular dual basis of squarefree physical heads

Source: the user-provided triangular-constraint argument in
CRTOptimizerCoalescenceAndDualClosure20261028.md, section 4.
This module proves the full finite-head statement, including H = 0 and the
fixed physical coordinate at zero. The step heads are exactly biorthogonal
to the nonsquarefree constraint rows. No infinite-span density is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadDimension
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeFiniteDualClosure QSquarefreeHeadCompression
open UniqueFactorizationMonoid

def nonsquarefreeSites (H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter (fun n => ¬Squarefree n)

theorem nonsquarefreeSites_bounds {H : ℕ} (m : nonsquarefreeSites H) :
    2 ≤ (m : ℕ) ∧ (m : ℕ) ≤ H ∧ ¬Squarefree (m : ℕ) := by
  have hm := Finset.mem_filter.mp m.property
  have hb := Finset.mem_Icc.mp hm.1
  refine ⟨?_, hb.2, hm.2⟩
  by_contra h
  have he : (m : ℕ) = 1 := by omega
  exact hm.2 (he ▸ squarefree_one)

def headEval (H n : ℕ) : (Fin H → ℝ) →ₗ[ℝ] ℝ where
  toFun f := if hn : 0 < n ∧ n ≤ H then f ⟨n - 1, by omega⟩ else 0
  map_add' f g := by split_ifs <;> simp
  map_smul' c f := by split_ifs <;> simp

def constraintRow (H : ℕ) (m : nonsquarefreeSites H) :
    Module.Dual ℝ (Fin H → ℝ) :=
  (headEval H m - headEval H (m - 1)) -
    (headEval H (radical (m : ℕ)) - headEval H (radical (m : ℕ) - 1))

def stepHead (H : ℕ) (m : nonsquarefreeSites H) : Fin H → ℝ :=
  fun i => if (m : ℕ) ≤ i.val + 1 then 1 else 0

theorem headEval_step (H : ℕ) (m : nonsquarefreeSites H) (n : ℕ) (hnH : n ≤ H) :
    headEval H n (stepHead H m) = if (m : ℕ) ≤ n then 1 else 0 := by
  have hm := nonsquarefreeSites_bounds m
  by_cases hn : 0 < n
  · simp [headEval, stepHead, hn, hnH, Nat.sub_add_cancel hn]
  · have hn0 : n = 0 := by omega
    simp [headEval, hn0, show ¬ (m : ℕ) ≤ 0 by omega]

theorem stepHead_jump (H : ℕ) (m : nonsquarefreeSites H) (n : ℕ)
    (hn : 0 < n) (hnH : n ≤ H) :
    headEval H n (stepHead H m) - headEval H (n - 1) (stepHead H m) =
      if n = (m : ℕ) then 1 else 0 := by
  rw [headEval_step H m n hnH, headEval_step H m (n - 1) (by omega)]
  by_cases he : n = (m : ℕ)
  · subst n
    have hm := nonsquarefreeSites_bounds m
    simp [show ¬ (m : ℕ) ≤ (m : ℕ) - 1 by omega]
  · by_cases hlt : n < (m : ℕ)
    · simp [he, show ¬ (m : ℕ) ≤ n by omega,
        show ¬ (m : ℕ) ≤ n - 1 by omega]
    · simp [he, show (m : ℕ) ≤ n by omega, show (m : ℕ) ≤ n - 1 by omega]

theorem constraintRow_step (H : ℕ) (m n : nonsquarefreeSites H) :
    constraintRow H m (stepHead H n) = if m = n then 1 else 0 := by
  have hm := nonsquarefreeSites_bounds m
  have hn := nonsquarefreeSites_bounds n
  have hr : 0 < radical (m : ℕ) := Nat.radical_pos _
  have hrle : radical (m : ℕ) ≤ (m : ℕ) :=
    Nat.radical_le_self_iff.mpr (by omega)
  have hrne : radical (m : ℕ) ≠ (n : ℕ) := by
    intro he
    exact hn.2.2 (he ▸ squarefree_radical)
  change (headEval H m (stepHead H n) - headEval H (m - 1) (stepHead H n)) -
      (headEval H (radical (m : ℕ)) (stepHead H n) -
        headEval H (radical (m : ℕ) - 1) (stepHead H n)) = _
  rw [stepHead_jump H n m (by omega) hm.2.1,
    stepHead_jump H n (radical (m : ℕ)) hr (by omega), if_neg hrne, sub_zero]
  simp only [Subtype.val_inj]

theorem constraintRow_linearIndependent (H : ℕ) :
    LinearIndependent ℝ (constraintRow H) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have he := congrArg (fun l : Module.Dual ℝ (Fin H → ℝ) => l (stepHead H m)) hc
  simpa [LinearMap.sum_apply, constraintRow_step] using he

def constraintSpan (H : ℕ) : Submodule ℝ (Module.Dual ℝ (Fin H → ℝ)) :=
  Submodule.span ℝ (Set.range (constraintRow H))

def constraintBasis (H : ℕ) :
    Module.Basis (nonsquarefreeSites H) ℝ (constraintSpan H) :=
  Module.Basis.span (constraintRow_linearIndependent H)

theorem constraintSpan_dimension (H : ℕ) :
    Module.finrank ℝ (constraintSpan H) = (nonsquarefreeSites H).card := by
  simpa using Module.finrank_eq_card_basis (constraintBasis H)

def constraintMap (H : ℕ) : (Fin H → ℝ) →ₗ[ℝ] (nonsquarefreeSites H → ℝ) :=
  LinearMap.pi (constraintRow H)

theorem constraintMap_surjective (H : ℕ) : Function.Surjective (constraintMap H) := by
  classical
  intro b
  refine ⟨∑ m, b m • stepHead H m, ?_⟩
  funext n
  change constraintRow H n (∑ m, b m • stepHead H m) = b n
  simp [map_sum, constraintRow_step]

theorem constraintMap_rank (H : ℕ) :
    Module.finrank ℝ (constraintMap H).range = (nonsquarefreeSites H).card := by
  rw [LinearMap.range_eq_top.mpr (constraintMap_surjective H)]
  simp

theorem squarefree_nonsquarefree_count (H : ℕ) :
    (sites H).card + (nonsquarefreeSites H).card = H := by
  classical
  have hd : Disjoint (sites H) (nonsquarefreeSites H) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hn).2
  have hu : sites H ∪ nonsquarefreeSites H = Finset.Icc 1 H := by
    ext n
    simp only [sites, nonsquarefreeSites, Finset.mem_union, Finset.mem_filter]
    tauto
  rw [← Finset.card_union_of_disjoint hd, hu]
  simp

theorem constraintMap_kernel_dimension (H : ℕ) :
    Module.finrank ℝ (constraintMap H).ker = (sites H).card := by
  have hk := (constraintMap H).finrank_range_add_finrank_ker
  rw [constraintMap_rank] at hk
  have hc := squarefree_nonsquarefree_count H
  simp only [Module.finrank_pi, Fintype.card_fin] at hk
  omega

def legalHeads (H : ℕ) : Submodule ℝ (Fin H → ℝ) :=
  qSquarefreeCRTSpan.map (physicalMap H)

theorem headEval_physicalMap (H n : ℕ) (F : QHilbert) (hnH : n ≤ H) :
    headEval H n (physicalMap H F) = qSequence F n := by
  by_cases hn : 0 < n
  · change (if hn : 0 < n ∧ n ≤ H then
        physicalMap H F ⟨n - 1, by omega⟩ else 0) = qSequence F n
    rw [dif_pos ⟨hn, hnH⟩]
    change qSequence F (n - 1 + 1) = qSequence F n
    rw [Nat.sub_add_cancel hn]
  · have hn0 : n = 0 := by omega
    simp [headEval, hn0, qSequence_zero]

theorem legalHeads_eq_kernel (H : ℕ) : legalHeads H = (constraintMap H).ker := by
  ext f
  constructor
  · rintro ⟨F, hF, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext m
    have hm := nonsquarefreeSites_bounds m
    have hrle : radical (m : ℕ) ≤ (m : ℕ) :=
      Nat.radical_le_self_iff.mpr (by omega)
    change (headEval H m (physicalMap H F) - headEval H (m - 1) (physicalMap H F)) -
        (headEval H (radical (m : ℕ)) (physicalMap H F) -
          headEval H (radical (m : ℕ) - 1) (physicalMap H F)) = 0
    rw [headEval_physicalMap H m F hm.2.1,
      headEval_physicalMap H (m - 1) F (by omega),
      headEval_physicalMap H (radical (m : ℕ)) F (by omega),
      headEval_physicalMap H (radical (m : ℕ) - 1) F (by omega)]
    exact sub_eq_zero.mpr (legal_le_radicalCompatible hF m hm.1)
  · intro hf
    let v : ℕ → ℝ := fun n => headEval H n f
    have hv0 : v 0 = 0 := by simp [v, headEval]
    have hcompat : ∀ n, 2 ≤ n → n ≤ H →
        v n - v (n - 1) = v (radical n) - v (radical n - 1) := by
      intro n hn hnH
      by_cases hs : Squarefree n
      · have hr : radical n = n :=
          Nat.dvd_antisymm radical_dvd_self
            ((dvd_radical_iff hs.isRadical (by omega : n ≠ 0)).mpr (dvd_refl n))
        rw [hr]
      · let m : nonsquarefreeSites H :=
          ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hnH⟩, hs⟩⟩
        have he := congrFun (LinearMap.mem_ker.mp hf) m
        change (v n - v (n - 1)) - (v (radical n) - v (radical n - 1)) = 0 at he
        exact sub_eq_zero.mp he
    obtain ⟨F, hF, hhead⟩ := (exact_head_iff_radicalCompatible v H hv0).mpr hcompat
    refine ⟨F, hF, ?_⟩
    funext i
    have hi := hhead (i.val + 1) (by omega)
    simpa [physicalMap, v, headEval, show i.val + 1 ≤ H by omega] using hi

theorem legalHeads_dimension (H : ℕ) :
    Module.finrank ℝ (legalHeads H) = ((Finset.Icc 1 H).filter Squarefree).card := by
  rw [legalHeads_eq_kernel, constraintMap_kernel_dimension]
  rfl

theorem constraintSpan_iff_annihilates (H : ℕ) (l : Module.Dual ℝ (Fin H → ℝ)) :
    l ∈ constraintSpan H ↔ ∀ f ∈ legalHeads H, l f = 0 := by
  classical
  constructor
  · intro hl f hf
    have hf' : constraintMap H f = 0 :=
      LinearMap.mem_ker.mp ((legalHeads_eq_kernel H) ▸ hf)
    induction hl using Submodule.span_induction with
    | mem l hl =>
        obtain ⟨m, rfl⟩ := hl
        exact congrFun hf' m
    | zero => simp
    | add l k hl hk ihl ihk => simp [ihl, ihk]
    | smul c l hl ih => simp [ih]
  · intro hl
    have he : l = ∑ m, l (stepHead H m) • constraintRow H m := by
      apply LinearMap.ext
      intro f
      let g := ∑ m, constraintRow H m f • stepHead H m
      have hg : f - g ∈ legalHeads H := by
        rw [legalHeads_eq_kernel, LinearMap.mem_ker]
        funext n
        change constraintRow H n (f - g) = 0
        simp [g, map_sub, map_sum, constraintRow_step]
      have hh := hl (f - g) hg
      simp only [map_sub, g, map_sum, map_smul, smul_eq_mul] at hh
      simpa [LinearMap.sum_apply, mul_comm] using sub_eq_zero.mp hh
    rw [he]
    exact Submodule.sum_mem _ (fun m _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))

/-- Reinsert the fixed coordinate at zero. -/
def anchorMap (H : ℕ) : (Fin H → ℝ) →ₗ[ℝ] (Fin (H + 1) → ℝ) where
  toFun f := Fin.cases 0 f
  map_add' f g := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c f := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem anchorMap_injective (H : ℕ) : Function.Injective (anchorMap H) := by
  intro f g h
  funext i
  exact congrFun h i.succ

def anchoredLegalHeads (H : ℕ) : Submodule ℝ (Fin (H + 1) → ℝ) :=
  (legalHeads H).map (anchorMap H)

theorem anchoredLegalHeads_dimension (H : ℕ) :
    Module.finrank ℝ (anchoredLegalHeads H) =
      ((Finset.Icc 1 H).filter Squarefree).card := by
  have hi : Function.Injective ((anchorMap H).domRestrict (legalHeads H)) :=
    (anchorMap_injective H).comp Subtype.val_injective
  have he : anchoredLegalHeads H =
      ((anchorMap H).domRestrict (legalHeads H)).range := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.val, g.property, rfl⟩
  rw [he, LinearMap.finrank_range_of_inj hi, legalHeads_dimension]

theorem anchoredLegalHeads_iff (H : ℕ) (f : Fin (H + 1) → ℝ) :
    f ∈ anchoredLegalHeads H ↔
      ∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧ ∀ i, qSequence F i.val = f i := by
  constructor
  · rintro ⟨g, ⟨F, hF, rfl⟩, rfl⟩
    refine ⟨F, hF, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [anchorMap, qSequence_zero]
    · rfl
  · rintro ⟨F, hF, hf⟩
    refine ⟨physicalMap H F, ⟨F, hF, rfl⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [anchorMap, qSequence_zero] using hf 0
    · exact hf j.succ

def pointHead (H : ℕ) (m : nonsquarefreeSites H) : Fin H → ℝ :=
  fun i => if i.val + 1 = (m : ℕ) then 1 else 0

theorem headEval_point (H : ℕ) (m : nonsquarefreeSites H) (n : ℕ) (hnH : n ≤ H) :
    headEval H n (pointHead H m) = if n = (m : ℕ) then 1 else 0 := by
  have hm := nonsquarefreeSites_bounds m
  by_cases hn : 0 < n
  · simp [headEval, pointHead, hn, hnH, Nat.sub_add_cancel hn]
  · have hn0 : n = 0 := by omega
    simp [headEval, hn0, show 0 ≠ (m : ℕ) by omega]

theorem radical_lt_site {H : ℕ} (m : nonsquarefreeSites H) :
    radical (m : ℕ) < (m : ℕ) := by
  have hm := nonsquarefreeSites_bounds m
  have hle : radical (m : ℕ) ≤ (m : ℕ) := Nat.radical_le_self_iff.mpr (by omega)
  have hne : radical (m : ℕ) ≠ (m : ℕ) := by
    intro he
    exact hm.2.2 (he ▸ squarefree_radical)
  omega

/-- The row matrix in physical coordinates has a unit pivot at its final site. -/
theorem constraintRow_point_diagonal (H : ℕ) (m : nonsquarefreeSites H) :
    constraintRow H m (pointHead H m) = 1 := by
  have hm := nonsquarefreeSites_bounds m
  have hr := radical_lt_site m
  change (headEval H m (pointHead H m) - headEval H (m - 1) (pointHead H m)) -
    (headEval H (radical (m : ℕ)) (pointHead H m) -
      headEval H (radical (m : ℕ) - 1) (pointHead H m)) = 1
  rw [headEval_point H m m hm.2.1,
    headEval_point H m (m - 1) (by omega),
    headEval_point H m (radical (m : ℕ)) (by omega),
    headEval_point H m (radical (m : ℕ) - 1) (by omega)]
  simp [show (m : ℕ) - 1 ≠ (m : ℕ) by omega,
    show radical (m : ℕ) ≠ (m : ℕ) by omega,
    show radical (m : ℕ) - 1 ≠ (m : ℕ) by omega]

theorem constraintRow_point_above (H : ℕ) (m n : nonsquarefreeSites H)
    (hmn : (m : ℕ) < (n : ℕ)) : constraintRow H m (pointHead H n) = 0 := by
  have hm := nonsquarefreeSites_bounds m
  have hr := radical_lt_site m
  change (headEval H m (pointHead H n) - headEval H (m - 1) (pointHead H n)) -
    (headEval H (radical (m : ℕ)) (pointHead H n) -
      headEval H (radical (m : ℕ) - 1) (pointHead H n)) = 0
  rw [headEval_point H n m hm.2.1,
    headEval_point H n (m - 1) (by omega),
    headEval_point H n (radical (m : ℕ)) (by omega),
    headEval_point H n (radical (m : ℕ) - 1) (by omega)]
  simp [show (m : ℕ) ≠ (n : ℕ) by omega,
    show (m : ℕ) - 1 ≠ (n : ℕ) by omega,
    show radical (m : ℕ) ≠ (n : ℕ) by omega,
    show radical (m : ℕ) - 1 ≠ (n : ℕ) by omega]

/-- These finite rows are the existing four-site Hilbert annihilators. -/
theorem constraintRow_physicalMap (H : ℕ) (m : nonsquarefreeSites H) (F : QHilbert) :
    constraintRow H m (physicalMap H F) = inner ℝ (radicalWitness m) F := by
  have hm := nonsquarefreeSites_bounds m
  have hr := radical_lt_site m
  rw [radicalWitness_inner m hm.1]
  change (headEval H m (physicalMap H F) - headEval H (m - 1) (physicalMap H F)) -
      (headEval H (radical (m : ℕ)) (physicalMap H F) -
        headEval H (radical (m : ℕ) - 1) (physicalMap H F)) = _
  rw [headEval_physicalMap H m F hm.2.1,
    headEval_physicalMap H (m - 1) F (by omega),
    headEval_physicalMap H (radical (m : ℕ)) F (by omega),
    headEval_physicalMap H (radical (m : ℕ) - 1) F (by omega)]
  rfl

end RiemannResearch.RH.QSquarefreeHeadDimension

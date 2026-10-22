/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.Analysis.FiniteConstrainedProjection
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Independent squarefree physical-head coordinates

Source: user-provided head-compression proposal, 22 October 2026, and
QSquarefreeHeadRepairResearch20261022.md, Section 2. We use value differences
F(s)-F(1); the earlier memorandum used discrete jumps instead. The existing
radical-jump identity proves that both encode all feasible physical heads.
The interpolation proof reuses compensated residue directions. No complete
energy estimate uniform in the head length is assumed or proved here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeHeadCompression
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QResidueHeadSpace QSquarefreeLatticePackets SquarefreeRadicalDifference
open UniqueFactorizationMonoid
open Analysis.FiniteHilbertGram Analysis.FiniteConstrainedProjection

/-- Positive squarefree observation sites, including site one. -/
def sites (M : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter Squarefree

/-- The exact relation needed to recover nonsquarefree head values. -/
def RadicalCompatible (F : QHilbert) : Prop :=
  ∀ n, 2 ≤ n → qDifference F n = qDifference F (radical n)

theorem legal_radicalCompatible (F : QHilbert) (hF : F ∈ qSquarefreeCRTSpan) :
    RadicalCompatible F := by
  have hspan : qSquarefreeCRTSpan ≤
      Submodule.span ℝ (qResidue '' {d : ℕ | 2 ≤ d ∧ Squarefree d}) := by
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    exact Submodule.subset_span ⟨d.val, d.property, rfl⟩
  intro n hn
  exact span_difference_radical _ (fun d hd => ⟨hd.2, hd.1⟩) n hn F (hspan hF)

theorem one_radicalCompatible : RadicalCompatible qOne := by
  intro n hn
  rw [qDifference_qOne n hn,
    qDifference_qOne (radical n) (Nat.two_le_radical_iff.mpr hn)]

/-- Squarefree values determine the entire physical head for compatible vectors. -/
theorem head_eq_of_squarefree_eq (M : ℕ) (F G : QHilbert)
    (hF : RadicalCompatible F) (hG : RadicalCompatible G)
    (he : ∀ n ∈ sites M, qSequence F n = qSequence G n) :
    ∀ n, 0 < n → n ≤ M → qSequence F n = qSequence G n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnM
    by_cases hs : Squarefree n
    · exact he n (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hnM⟩, hs⟩)
    · have hn2 : 2 ≤ n := by
        by_contra h
        have hn1 : n = 1 := by omega
        exact hs (hn1 ▸ (by simp : Squarefree 1))
      have hr2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn2
      have hrle : radical n ≤ n := Nat.le_of_dvd hn radical_dvd_self
      have hrs : Squarefree (radical n) := squarefree_radical
      have hrlt : radical n < n := by
        by_contra h
        have hr : radical n = n := by omega
        exact hs (hr ▸ hrs)
      have hf := hF n hn2
      have hg := hG n hn2
      unfold qDifference at hf hg
      rw [ih (n - 1) (by omega) (by omega) (by omega),
        ih (radical n) hrlt (by omega) (by omega),
        ih (radical n - 1) (by omega) (by omega) (by omega)] at hf
      linarith

/-- F(1), followed by F(s)-F(1) at the other squarefree sites. -/
def observation (M : ℕ) (i : sites M) : QHilbert :=
  if (i : ℕ) = 1 then qSiteRiesz 1 else qSiteRiesz i - qSiteRiesz 1

theorem observation_inner (M : ℕ) (i : sites M) (F : QHilbert) :
    inner ℝ (observation M i) F =
      if (i : ℕ) = 1 then qSequence F 1 else qSequence F i - qSequence F 1 := by
  have hi : 0 < (i : ℕ) := (Finset.mem_Icc.mp (Finset.mem_filter.mp i.property).1).1
  unfold observation
  split_ifs <;> simp only [inner_sub_left, qSiteRiesz_inner _ hi,
    qSiteRiesz_inner 1 (by omega)]

/-- Compression loses no constraint for any two radical-compatible vectors. -/
theorem observations_iff_head (M : ℕ) (F G : QHilbert)
    (hF : RadicalCompatible F) (hG : RadicalCompatible G) :
    (∀ i : sites M, inner ℝ (observation M i) F = inner ℝ (observation M i) G) ↔
      ∀ n, 0 < n → n ≤ M → qSequence F n = qSequence G n := by
  constructor
  · intro he
    apply head_eq_of_squarefree_eq M F G hF hG
    intro n hn
    have hn1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hnM := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have h1mem : 1 ∈ sites M := by simp [sites]; omega
    have h1 := he ⟨1, h1mem⟩
    simp only [observation_inner] at h1
    change qSequence F 1 = qSequence G 1 at h1
    have hs := he ⟨n, hn⟩
    simp only [observation_inner] at hs
    split_ifs at hs with h
    · simpa only [h] using h1
    · linarith
  · intro he i
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp i.property).1
    rw [observation_inner, observation_inner, he i hi.1 hi.2,
      he 1 (by omega) (by omega)]

/-- The constant target has compressed source (1,0,...,0). -/
theorem observation_one (M : ℕ) (i : sites M) :
    inner ℝ (observation M i) qOne = if (i : ℕ) = 1 then 1 else 0 := by
  have hi : (i : ℕ) ≠ 0 := by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp i.property).1).1
    omega
  have h1 : qSequence qOne 1 = 1 := by
    rw [qSequence_qOne]; norm_num [qOneSequence]
  have hi1 : qSequence qOne i = 1 := by
    rw [qSequence_qOne]; simp [qOneSequence, hi]
  rw [observation_inner, h1, hi1]
  split_ifs <;> ring

/-- The existing compensated direction has diagonal value -1. -/
theorem compensated_diagonal (d r : ℕ) (hd : 0 < d) (hdr : d < r) :
    qSequence (compensatedResidue d r) d = -1 := by
  rw [compensatedResidue_sequence]
  simp only [residueFraction, Nat.mod_self, Nat.cast_zero, zero_div,
    Nat.mod_eq_of_lt hdr]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp
  ring

/-- Independent squarefree interpolation in a specified dictionary. The anchor
may be any conductor above M; legality is asserted separately. -/
theorem interpolate_squarefree (s : Finset ℕ) (M r : ℕ) (hr : r ∈ s)
    (hrM : M < r)
    (hsmall : ∀ d, 2 ≤ d → d ≤ M → Squarefree d → d ∈ s)
    (u : ℕ → ℝ) :
    ∃ F ∈ dictionary s, ∀ n ∈ sites M, qSequence F n = u n := by
  have hstep : ∀ N, N ≤ M → ∃ F ∈ dictionary s,
      ∀ n ∈ sites N, qSequence F n = u n := by
    intro N
    induction N with
    | zero =>
        intro hN
        exact ⟨0, Submodule.zero_mem _, by simp [sites]⟩
    | succ N ih =>
        intro hN
        obtain ⟨F, hF, hh⟩ := ih (by omega)
        by_cases hs : Squarefree (N + 1)
        · have hq : qResidue (N + 1) ∈ dictionary s := by
            by_cases he : N + 1 = 1
            · rw [he, qResidue_one]; exact Submodule.zero_mem _
            · exact Submodule.subset_span
                ⟨⟨N + 1, hsmall (N + 1) (by omega) hN hs⟩, rfl⟩
          have hv : compensatedResidue (N + 1) r ∈ dictionary s :=
            (dictionary s).sub_mem hq ((dictionary s).smul_mem _
              (Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩))
          refine ⟨F + (qSequence F (N + 1) - u (N + 1)) • compensatedResidue (N + 1) r,
            (dictionary s).add_mem hF ((dictionary s).smul_mem _ hv), ?_⟩
          intro n hn
          have hnN := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
          change qSequenceLinear (_ + _ • _) n = _
          simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          change qSequence F n + (qSequence F (N + 1) - u (N + 1)) *
            qSequence (compensatedResidue (N + 1) r) n = u n
          by_cases he : n = N + 1
          · subst n
            rw [compensated_diagonal (N + 1) r (by omega) (by omega)]
            ring
          · rw [compensatedResidue_head (N + 1) r n (by omega) (by omega)
                (by omega) (by omega), mul_zero, add_zero]
            exact hh n (Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hnN.1, by omega⟩, (Finset.mem_filter.mp hn).2⟩)
        · refine ⟨F, hF, ?_⟩
          intro n hn
          have hnN := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
          have hne : n ≠ N + 1 := by
            intro he; exact hs (he ▸ (Finset.mem_filter.mp hn).2)
          exact hh n (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hnN.1, by omega⟩, (Finset.mem_filter.mp hn).2⟩)
  exact hstep M le_rfl


/-- Every reduced source is attained; these coordinates are independent. -/
theorem interpolate_observations (s : Finset ℕ) (M r : ℕ) (hM : 0 < M)
    (hr : r ∈ s) (hrM : M < r)
    (hsmall : ∀ d, 2 ≤ d → d ≤ M → Squarefree d → d ∈ s)
    (b : sites M → ℝ) :
    ∃ c : s → ℝ, ∀ i : sites M,
      inner ℝ (observation M i)
        (Fintype.linearCombination ℝ (fun d : s => qResidue d) c) = b i := by
  have h1 : 1 ∈ sites M := by simp [sites]; omega
  let u : ℕ → ℝ := fun n => if n = 1 then b ⟨1, h1⟩ else
    if hn : n ∈ sites M then b ⟨n, hn⟩ + b ⟨1, h1⟩ else 0
  obtain ⟨F, hF, hh⟩ := interpolate_squarefree s M r hr hrM hsmall u
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hF
  refine ⟨c, ?_⟩
  intro i
  rw [Fintype.linearCombination_apply, hc, observation_inner]
  by_cases hi : (i : ℕ) = 1
  · rw [if_pos hi, hh 1 h1]
    have hei : i = ⟨1,h1⟩ := Subtype.ext hi
    simp [u, hei]
  · rw [if_neg hi, hh i i.property, hh 1 h1]
    simp [u, hi, i.property]

/-- Exact complete-Q projected reduced rows are independent. -/
theorem projected_observations_independent (s : Finset ℕ)
    (hs : ∀ d ∈ s, 1 < d) (M r : ℕ) (hM : 0 < M)
    (hr : r ∈ s) (hrM : M < r)
    (hsmall : ∀ d, 2 ≤ d → d ≤ M → Squarefree d → d ∈ s) :
    LinearIndependent ℝ (projectedRow
      (QCovarianceInvertibility.qResidue_linearIndependent
        (fun d : s => (d : ℕ)) (fun d => hs d d.property) Subtype.val_injective)
      (observation M)) := by
  classical
  have hu : ∀ i : sites M, ∃ c : s → ℝ, ∀ j : sites M,
      inner ℝ (observation M j)
        (Fintype.linearCombination ℝ (fun d : s => qResidue d) c) =
          if j = i then 1 else 0 := fun i =>
    interpolate_observations s M r hM hr hrM hsmall (fun j => if j = i then 1 else 0)
  choose c hc using hu
  exact projectedRow_independent_of_interpolants _ _ c hc

/-- Physical head values as a linear map. -/
def physicalMap (M : ℕ) : QHilbert →ₗ[ℝ] (Fin M → ℝ) where
  toFun F i := qSequence F (i.val + 1)
  map_add' F G := by
    funext i
    exact congrFun (qSequenceLinear.map_add F G) (i.val + 1)
  map_smul' a F := by
    funext i
    exact congrFun (qSequenceLinear.map_smul a F) (i.val + 1)

/-- The compressed observation map. -/
def reducedMap (M : ℕ) : QHilbert →ₗ[ℝ] (sites M → ℝ) where
  toFun F i := inner ℝ (observation M i) F
  map_add' F G := by funext i; exact inner_add_right _ _ _
  map_smul' a F := by funext i; exact inner_smul_right _ _ _

theorem dictionary_legal (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ Squarefree d) : dictionary s ≤ qSquarefreeCRTSpan := by
  apply Submodule.span_le.mpr
  rintro F ⟨d, rfl⟩
  exact Submodule.subset_span ⟨⟨d, hs d d.property⟩, rfl⟩

/-- The two observation maps have exactly the same coefficient kernel. -/
theorem observation_kernels (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ Squarefree d) (M : ℕ) :
    ((physicalMap M).comp (Fintype.linearCombination ℝ (fun d : s => qResidue d))).ker =
      ((reducedMap M).comp (Fintype.linearCombination ℝ (fun d : s => qResidue d))).ker := by
  ext c
  let F := Fintype.linearCombination ℝ (fun d : s => qResidue d) c
  have hF : F ∈ qSquarefreeCRTSpan := by
    apply dictionary_legal s hs
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩
  have he := observations_iff_head M F 0 (legal_radicalCompatible F hF)
    (legal_radicalCompatible 0 (Submodule.zero_mem _))
  have hzero : ∀ n, qSequence (0 : QHilbert) n = 0 :=
    fun n => congrFun (map_zero qSequenceLinear) n
  simp only [inner_zero_right, hzero] at he
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, funext_iff, Pi.zero_apply]
  change (∀ i : Fin M, qSequence F (i.val + 1) = 0) ↔
    ∀ i : sites M, inner ℝ (observation M i) F = 0
  rw [he]
  constructor
  · intro h n hn hnM
    have hi := h ⟨n - 1, by omega⟩
    simpa only [Nat.sub_add_cancel hn] using hi
  · intro h i
    exact h (i.val + 1) (by omega) (by omega)

/-- Exact physical-head rank: the number of positive squarefree sites. -/
theorem physical_rank (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ Squarefree d) (M r : ℕ) (hM : 0 < M)
    (hr : r ∈ s) (hrM : M < r)
    (hsmall : ∀ d, 2 ≤ d → d ≤ M → Squarefree d → d ∈ s) :
    Module.finrank ℝ
      ((physicalMap M).comp (Fintype.linearCombination ℝ (fun d : s => qResidue d))).range =
      (sites M).card := by
  let P := (physicalMap M).comp (Fintype.linearCombination ℝ (fun d : s => qResidue d))
  let C := (reducedMap M).comp (Fintype.linearCombination ℝ (fun d : s => qResidue d))
  have hsur : Function.Surjective C := by
    intro b
    obtain ⟨c, hc⟩ := interpolate_observations s M r hM hr hrM hsmall b
    exact ⟨c, funext hc⟩
  have hker : P.ker = C.ker := observation_kernels s hs M
  have hp := P.finrank_range_add_finrank_ker
  have hc := C.finrank_range_add_finrank_ker
  rw [hker] at hp
  have hrank : Module.finrank ℝ C.range = (sites M).card := by
    rw [LinearMap.range_eq_top.mpr hsur]
    simp
  change Module.finrank ℝ P.range = _
  omega


/-- A linear reconstruction of every compatible physical head from its
independent squarefree coordinates. In particular all physical Q weights
can be transported to compressed coordinates without being discarded. -/
theorem exists_physical_reconstruction (s : Finset ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ Squarefree d) (M r : ℕ) (hM : 0 < M)
    (hr : r ∈ s) (hrM : M < r)
    (hsmall : ∀ d, 2 ≤ d → d ≤ M → Squarefree d → d ∈ s) :
    ∃ R : Fin M → sites M → ℝ, ∀ F : QHilbert, RadicalCompatible F →
      ∀ i : Fin M, qSequence F (i.val + 1) =
        ∑ j, R i j * inner ℝ (observation M j) F := by
  classical
  have hu : ∀ j : sites M, ∃ c : s → ℝ, ∀ k : sites M,
      inner ℝ (observation M k)
        (Fintype.linearCombination ℝ (fun d : s => qResidue d) c) =
          if k = j then 1 else 0 := fun j =>
    interpolate_observations s M r hM hr hrM hsmall (fun k => if k = j then 1 else 0)
  choose c hc using hu
  let U : sites M → QHilbert := fun j =>
    Fintype.linearCombination ℝ (fun d : s => qResidue d) (c j)
  have hU : ∀ j, U j ∈ qSquarefreeCRTSpan := by
    intro j
    apply dictionary_legal s hs
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c j, rfl⟩
  refine ⟨fun i j => qSequence (U j) (i.val + 1), ?_⟩
  intro F hF i
  let z : sites M → ℝ := fun j => inner ℝ (observation M j) F
  let G : QHilbert := Fintype.linearCombination ℝ U z
  have hG : G ∈ qSquarefreeCRTSpan := by
    change Fintype.linearCombination ℝ U z ∈ qSquarefreeCRTSpan
    rw [Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hU j)
  have ho : ∀ k, inner ℝ (observation M k) G = inner ℝ (observation M k) F := by
    intro k
    change inner ℝ (observation M k) (Fintype.linearCombination ℝ U z) = _
    rw [Fintype.linearCombination_apply, inner_sum]
    simp only [inner_smul_right, U, hc]
    simp [z]
  have hh := (observations_iff_head M G F
    (legal_radicalCompatible G hG) hF).mp ho
  rw [← hh (i.val + 1) (by omega) (by omega)]
  change qSequenceLinear (Fintype.linearCombination ℝ U z) (i.val + 1) = _
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change z j * qSequence (U j) (i.val + 1) = _
  exact mul_comm _ _


end RiemannResearch.RH.QSquarefreeHeadCompression

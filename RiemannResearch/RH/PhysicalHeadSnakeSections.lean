import RiemannResearch.RH.CenteredMeanQuotients
import RiemannResearch.RH.ParetoCompactCutoffLimits
import RiemannResearch.RH.ParetoAffineHeadTower

/-!
# Physical head sections of the centered Pareto mean

A mean-one lift can agree with the ambient constant on a finite physical head.
For any such lift the entire squared norm of the centered snake boundary pairs
against the complementary physical tail of its fixed orthogonal representative.
A uniform bound on sections over all heads therefore kills the boundary.
The short exact stage rows below isolate the mean-zero, zero-head freedom in
each lift. Physical cutoffs are those of `ParetoCompactHead`.
-/

noncomputable section
open Filter CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.PhysicalHeadSections

open CoefficientStabilization

/-- Agreement on the first N positive physical coordinates. -/
def MatchesUnitHead (N : ℕ) (v : closedSpace) : Prop :=
  compactHead N (v : ThresholdHilbert) = compactHead N hilbertOne

private theorem one_sequence_at_positive (k : ℕ) (hk : 0 < k) :
    hilbertSequence hilbertOne k = 1 :=
  (congrFun hilbertOne_sequence k).trans (if_neg (Nat.ne_of_gt hk))

theorem matchesUnitHead_iff_sequence (N : ℕ) (v : closedSpace) :
    MatchesUnitHead N v ↔
      ∀ k : ℕ, 0 < k → k ≤ N → hilbertSequence (v : ThresholdHilbert) k = 1 := by
  constructor
  · intro h k hk hkN
    have he := congrArg (fun x : ThresholdHilbert => hilbertSequence x k) h
    rw [compactHead_sequence, compactHead_sequence, if_pos hkN, if_pos hkN] at he
    exact he.trans (one_sequence_at_positive k hk)
  · intro h
    apply hilbertSequence_injective
    funext k
    rw [compactHead_sequence, compactHead_sequence]
    by_cases hkN : k ≤ N
    · rw [if_pos hkN, if_pos hkN]
      cases k with
      | zero => simp
      | succ k =>
        exact (h (k + 1) (by omega) hkN).trans (one_sequence_at_positive (k + 1) (by omega)).symm
    · rw [if_neg hkN, if_neg hkN]

/-- A legal vector belongs to the stage when its first N entries equal its mean. -/
def headCompatible (N : ℕ) : Submodule ℝ closedSpace :=
  ((compactHeadLinear N).comp closedSpace.subtype -
    legalPacketMean.toLinearMap.smulRight (compactHead N hilbertOne)).ker

theorem mem_headCompatible_iff (N : ℕ) (v : closedSpace) :
    v ∈ headCompatible N ↔
      compactHead N (v : ThresholdHilbert) = legalPacketMean v • compactHead N hilbertOne :=
  sub_eq_zero

/-- Mean on the stage of head-compatible legal vectors. -/
def stageMean (N : ℕ) : headCompatible N →L[ℝ] ℝ :=
  legalPacketMean.comp (headCompatible N).subtypeL

/-- The stage kernel consists of mixed vectors whose physical head vanishes. -/
theorem mem_stageMean_ker_iff (N : ℕ) (v : headCompatible N) :
    v ∈ (stageMean N).ker ↔
      (v.val : ThresholdHilbert) ∈ mixedClosure ∧
        compactHead N (v.val : ThresholdHilbert) = 0 := by
  change legalPacketMean v.val = 0 ↔ _
  have hcompat := (mem_headCompatible_iff N v.val).mp v.property
  constructor
  · intro hm
    refine ⟨(mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr ⟨v.val.property, hm⟩, ?_⟩
    simpa only [hm, zero_smul] using hcompat
  · rintro ⟨hm, _⟩
    exact ((mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hm).2

/-- A candidate right inverse of the stage mean, given by scalar multiplication. -/
def stageSection (N : ℕ) (v : headCompatible N) : ℝ →L[ℝ] headCompatible N :=
  ContinuousLinearMap.toSpanSingleton ℝ v

private def stageRetraction (N : ℕ) (v : headCompatible N) (hv : stageMean N v = 1) :
    headCompatible N →L[ℝ] (stageMean N).ker :=
  (ContinuousLinearMap.id ℝ (headCompatible N) -
    (stageSection N v).comp (stageMean N)).codRestrict _ fun z => by
      change stageMean N (z - stageMean N z • v) = 0
      rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]

/-- The finite physical head sequence, with its mean-zero kernel. -/
def stageComplex (N : ℕ) : ShortComplex (TopModuleCat ℝ) :=
  ShortComplex.mk (TopModuleCat.ofHom (stageMean N).ker.subtypeL)
    (TopModuleCat.ofHom (stageMean N)) (by
      apply ConcreteCategory.hom_ext
      intro x
      change (stageMean N).ker at x
      exact x.property)

/-- Every mean-one head-compatible lift splits its stage row. -/
def stageSplitting (N : ℕ) (v : headCompatible N) (hv : stageMean N v = 1) :
    (stageComplex N).Splitting where
  r := TopModuleCat.ofHom (stageRetraction N v hv)
  s := TopModuleCat.ofHom (stageSection N v)
  f_r := by
    apply ConcreteCategory.hom_ext
    intro z
    change (stageMean N).ker at z
    apply Subtype.ext
    change (z : headCompatible N) - stageMean N (z : headCompatible N) • v =
      (z : headCompatible N)
    rw [show stageMean N (z : headCompatible N) = 0 from z.property, zero_smul, sub_zero]
  s_g := by
    apply ConcreteCategory.hom_ext
    intro t
    change ℝ at t
    change stageMean N (t • v) = t
    rw [map_smul, hv, smul_eq_mul, mul_one]
  id := by
    apply ConcreteCategory.hom_ext
    intro z
    change headCompatible N at z
    change (z - stageMean N z • v) + stageMean N z • v = z
    exact sub_add_cancel _ _

local instance : HasZeroObject (TopModuleCat.{0} ℝ) :=
  ⟨⟨_, (terminalIsTerminal (C := TopModuleCat.{0} ℝ)).isZero⟩⟩

theorem stage_shortExact_of_unitHead (N : ℕ) (v : closedSpace)
    (hv : legalPacketMean v = 1) (hh : MatchesUnitHead N v) :
    (stageComplex N).ShortExact := by
  have hm : v ∈ headCompatible N := (mem_headCompatible_iff N v).mpr
    (by rw [hv, one_smul]; exact hh)
  exact (stageSplitting N ⟨v, hm⟩ hv).shortExact

/-- The boundary paired with any centered mean-one lift on its physical tail. -/
theorem head_tail_boundary_pairing (N : ℕ) (v : closedSpace)
    (hv : legalPacketMean v = 1) (hh : MatchesUnitHead N v) :
    inner ℝ ((v : ThresholdHilbert) - hilbertOne)
      ((defect : ThresholdHilbert) - compactHead N (defect : ThresholdHilbert)) =
        ‖boundary‖ ^ 2 := by
  have hm : (v : ThresholdHilbert) - normalizedScreenedTwo ∈ mixedClosure := by
    have hr := (legalMixedRetraction v).property
    change (v : ThresholdHilbert) - legalPacketMean v • normalizedScreenedTwo ∈ mixedClosure at hr
    simpa only [hv, one_smul] using hr
  have ho : inner ℝ ((v : ThresholdHilbert) - normalizedScreenedTwo)
      (defect : ThresholdHilbert) = 0 :=
    screenedTwo_sub_one_mem_orthogonals.2 _ hm
  have hhead : compactHead N ((v : ThresholdHilbert) - hilbertOne) = 0 := by
    rw [compactHead_sub, show compactHead N (v : ThresholdHilbert) = _ from hh, sub_self]
  have horth : inner ℝ ((v : ThresholdHilbert) - hilbertOne)
      (compactHead N (defect : ThresholdHilbert)) = 0 := by
    rw [← compactHead_symmetric, hhead, inner_zero_left]
  have hs : (v : ThresholdHilbert) - hilbertOne =
      ((v : ThresholdHilbert) - normalizedScreenedTwo) + (defect : ThresholdHilbert) := by
    change (v : ThresholdHilbert) - hilbertOne =
      ((v : ThresholdHilbert) - normalizedScreenedTwo) + (normalizedScreenedTwo - hilbertOne)
    abel
  rw [inner_sub_right, horth, sub_zero, hs, inner_add_left, ho, zero_add,
    real_inner_self_eq_norm_sq]
  exact congrArg (fun t : ℝ => t ^ 2) boundary_norm.symm

/-- A finite-head lift pays for the fixed boundary through a shrinking tail. -/
theorem head_tail_boundary_bound (N : ℕ) (v : closedSpace)
    (hv : legalPacketMean v = 1) (hh : MatchesUnitHead N v) :
    ‖boundary‖ ^ 2 ≤ ‖(v : ThresholdHilbert) - hilbertOne‖ *
      ‖(defect : ThresholdHilbert) - compactHead N (defect : ThresholdHilbert)‖ := by
  rw [← head_tail_boundary_pairing N v hv hh]
  exact real_inner_le_norm _ _

/-- Any finite uniform norm budget over all exact physical heads kills the snake boundary. -/
theorem boundary_eq_zero_iff_bounded_head_sections :
    boundary = 0 ↔ ∃ B : ℝ, ∀ N : ℕ, ∃ v : closedSpace,
      legalPacketMean v = 1 ∧ MatchesUnitHead N v ∧ ‖v‖ ≤ B := by
  constructor
  · intro hb
    let e : closedSpace := ⟨hilbertOne, boundary_eq_zero_iff_one_mem.mp hb⟩
    refine ⟨‖e‖, fun _ => ⟨e, ?_, rfl, le_rfl⟩⟩
    change inner ℝ hilbertOne hilbertOne = 1
    rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  · rintro ⟨B, h⟩
    let d : ThresholdHilbert := defect
    have hle (N : ℕ) : ‖boundary‖ ^ 2 ≤ (B + ‖hilbertOne‖) * ‖d - compactHead N d‖ := by
      obtain ⟨v, hv, hh, hB⟩ := h N
      apply (head_tail_boundary_bound N v hv hh).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add hB le_rfl)
    have ht : Tendsto (fun N : ℕ => (B + ‖hilbertOne‖) * ‖d - compactHead N d‖) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (x := B + ‖hilbertOne‖)).mul (compactHead_tail_norm_tendsto_zero d)
    have hz : ‖boundary‖ ^ 2 ≤ 0 :=
      le_of_tendsto_of_tendsto' (tendsto_const_nhds (x := ‖boundary‖ ^ 2)) ht hle
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg boundary])

/-- The norm of a scalar section is exactly the norm of its lift at one. -/
theorem stageSection_norm (N : ℕ) (v : headCompatible N) :
    ‖stageSection N v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_toSpanSingleton _

/-- The squared cost above one is exactly the centered physical energy. -/
theorem unitMean_centered_norm_sq (v : closedSpace) (hv : legalPacketMean v = 1) :
    ‖(v : ThresholdHilbert) - hilbertOne‖ ^ 2 = ‖v‖ ^ 2 - 1 := by
  change inner ℝ (v : ThresholdHilbert) hilbertOne = 1 at hv
  rw [norm_sub_sq_real, hv, hilbertOne_norm_sq]
  change ‖v‖ ^ 2 - 2 * 1 + 1 = ‖v‖ ^ 2 - 1
  ring

/-- A nonzero boundary and an exact head force a nonzero omitted defect tail. -/
theorem defect_tail_norm_pos_of_unitHead (N : ℕ) (v : closedSpace)
    (hb : boundary ≠ 0) (hv : legalPacketMean v = 1) (hh : MatchesUnitHead N v) :
    0 < ‖(defect : ThresholdHilbert) - compactHead N (defect : ThresholdHilbert)‖ := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro hz
  have hbound := head_tail_boundary_bound N v hv hh
  rw [← hz, mul_zero] at hbound
  exact (not_lt_of_ge hbound) (sq_pos_of_pos (norm_pos_iff.mpr hb))

/-- Every section cost pays the inverse squared tail of the nonzero boundary representative. -/
theorem unitHead_section_cost_lower_bound (N : ℕ) (v : closedSpace)
    (hb : boundary ≠ 0) (hv : legalPacketMean v = 1) (hh : MatchesUnitHead N v) :
    1 + ‖boundary‖ ^ 4 / ‖(defect : ThresholdHilbert) -
      compactHead N (defect : ThresholdHilbert)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  let t := ‖(defect : ThresholdHilbert) - compactHead N (defect : ThresholdHilbert)‖
  have ht : 0 < t := defect_tail_norm_pos_of_unitHead N v hb hv hh
  have hprod : ‖boundary‖ ^ 4 ≤ (‖v‖ ^ 2 - 1) * t ^ 2 := calc
    ‖boundary‖ ^ 4 = (‖boundary‖ ^ 2) ^ 2 := by ring
    _ ≤ (‖(v : ThresholdHilbert) - hilbertOne‖ * t) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) (head_tail_boundary_bound N v hv hh) 2
    _ = (‖v‖ ^ 2 - 1) * t ^ 2 := by rw [mul_pow, unitMean_centered_norm_sq v hv]
  have hdiv := (div_le_iff₀ (sq_pos_of_pos ht)).mpr hprod
  change 1 + ‖boundary‖ ^ 4 / t ^ 2 ≤ ‖v‖ ^ 2
  linarith only [hdiv]

/-- An exact section on a larger physical head agrees on every smaller one. -/
theorem matchesUnitHead_mono {N K : ℕ} (hNK : N ≤ K) {v : closedSpace}
    (h : MatchesUnitHead K v) : MatchesUnitHead N v :=
  (matchesUnitHead_iff_sequence N v).mpr fun k hk hkN =>
    (matchesUnitHead_iff_sequence K v).mp h k hk (hkN.trans hNK)

/-- Bounded lifts along any cofinal family of physical stages suffice. -/
theorem boundary_eq_zero_iff_cofinal_bounded_head_sections :
    boundary = 0 ↔ ∃ B : ℝ, ∀ N : ℕ, ∃ K : ℕ, N ≤ K ∧ ∃ v : closedSpace,
      legalPacketMean v = 1 ∧ MatchesUnitHead K v ∧ ‖v‖ ≤ B := by
  rw [boundary_eq_zero_iff_bounded_head_sections]
  constructor
  · rintro ⟨B, h⟩
    exact ⟨B, fun N => ⟨N, le_rfl, h N⟩⟩
  · rintro ⟨B, h⟩
    refine ⟨B, fun N => ?_⟩
    obtain ⟨K, hNK, v, hv, hh, hB⟩ := h N
    exact ⟨v, hv, matchesUnitHead_mono hNK hh, hB⟩

/-- The canonical affine minimizer supplies a splitting at every finite stage. -/
theorem stage_shortExact (N : ℕ) : (stageComplex N).ShortExact := by
  have hw := (AffineHeadTower.patch_spec N).1
  let v : closedSpace := ⟨AffineHeadTower.patch N, hw.1⟩
  apply stage_shortExact_of_unitHead N v hw.2.1
  apply (matchesUnitHead_iff_sequence N v).mpr
  intro k hk hkN
  cases k with
  | zero => omega
  | succ i => simpa only [physicalEvaluationCLM_apply] using hw.2.2 i (by omega)

/-- The limit of the descending stages inside the legal Hilbert space. -/
theorem iInf_headCompatible_eq_legalConstants : (⨅ N : ℕ, headCompatible N) = legalConstants := by
  ext v
  rw [Submodule.mem_iInf]
  change (∀ N : ℕ, v ∈ headCompatible N) ↔
    (v : ThresholdHilbert) ∈ Submodule.span ℝ {hilbertOne}
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hv
    have hhead (N : ℕ) : compactHead N (v : ThresholdHilbert) =
        compactHead N (legalPacketMean v • hilbertOne) := by
      rw [compactHead_smul]
      exact (mem_headCompatible_iff N v).mp (hv N)
    have ht : Tendsto (fun N : ℕ => compactHead N (v : ThresholdHilbert)) atTop
        (𝓝 (legalPacketMean v • hilbertOne)) := by
      simp_rw [hhead]
      exact compactHead_tendsto _
    exact ⟨legalPacketMean v, (tendsto_nhds_unique (compactHead_tendsto _) ht).symm⟩
  · rintro ⟨t, ht⟩ N
    apply (mem_headCompatible_iff N v).mpr
    have hm : legalPacketMean v = t := by
      change inner ℝ (v : ThresholdHilbert) hilbertOne = t
      rw [← ht, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq, mul_one]
    rw [← ht, compactHead_smul, hm]

/-- Exactness of the centered snake tests surjectivity on the limit row. -/
theorem limit_mean_surjective_iff_boundary_zero :
    Function.Surjective constantMean ↔ boundary = 0 := by
  constructor
  · intro hs
    apply DFunLike.ext
    intro t
    change boundary t = 0
    obtain ⟨v, hv⟩ := hs t
    exact (exact_constantMean_boundary t).mpr ⟨v, hv⟩
  · intro hb t
    exact (exact_constantMean_boundary t).mp (by rw [hb]; rfl)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.PhysicalHeadSections

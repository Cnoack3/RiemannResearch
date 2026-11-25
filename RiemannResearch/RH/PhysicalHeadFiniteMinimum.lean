import RiemannResearch.RH.PhysicalHeadSectionGrowth
import RiemannResearch.RH.MertensWeightedEnergy
import RiemannResearch.RH.ParetoArithmeticRepair
import Mathlib.NumberTheory.Bertrand

/-! # Explicit mixed floor columns and the optimal finite section cost

A pair of large primes gives concrete finite mixed lifts of the floor columns.
Their physical head matrix has determinant one. In any mean-one legal translate,
the finite-window section norms have the closed minimum as their infimum.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadFiniteMinimum

open CoefficientStabilization AffineHeadTower PhysicalHeadSectionGrowth
open PhysicalHeadMixedInterpolation TwoSeedExactHeadEnergy
open RiemannResearch.RH.MertensWeightedEnergy

/-- Replace each divisor packet of the original residue by a negatively signed
fresh-prime mixed packet. -/
def shiftedResidue (p d : ℕ) : ThresholdHilbert :=
  ∑ a ∈ d.divisors.filter (fun a => 1 < a), -ramanujanPacketHilbert (p * a)

private theorem shiftedResidue_mem_window (p d B : ℕ) (hp : p.Prime) (hd : d < p)
    (hB : p * d ≤ B) : shiftedResidue p d ∈ mixedSpace (Finset.Icc 2 B) := by
  apply Submodule.sum_mem
  intro a ha
  obtain ⟨had, ha1⟩ := Finset.mem_filter.mp ha
  have had' := Nat.divisor_le had
  have hnot : ¬ p ∣ a := fun h => by
    have := Nat.le_of_dvd (by omega : 0 < a) h
    omega
  apply Submodule.neg_mem
  exact mixed_packet_mul_of_coprime_mem_window hp.one_lt ha1
    (hp.coprime_iff_not_dvd.mpr hnot) ((Nat.mul_le_mul_left p had').trans hB)

theorem shiftedResidue_head (p d n : ℕ) (hp : p.Prime) (hd : d < p)
    (hd0 : 0 < d) (hn : n < p) :
    hilbertSequence (shiftedResidue p d) n = residue d n := by
  rw [← anchoredEvaluationCLM_apply, shiftedResidue, map_sum]
  rw [← ramanujanPacket_divisor_sum_gt_one d n hd0]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨had, ha1⟩ := Finset.mem_filter.mp ha
  have had' := Nat.divisor_le had
  have hnot : ¬ p ∣ a := fun h => by
    have := Nat.le_of_dvd (by omega : 0 < a) h
    omega
  rw [map_neg, anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
    fresh_prime_packet_head p a n hp ha1 hnot hn, neg_neg]

def mixedFloorColumn (p T d : ℕ) : ThresholdHilbert :=
  (d : ℝ)⁻¹ • (shiftedResidue p T - shiftedResidue p d)

theorem mixedFloorColumn_mem_window (p T d : ℕ) (hp : p.Prime) (hT : T < p)
    (hdT : d ≤ T) : mixedFloorColumn p T d ∈ mixedSpace (Finset.Icc 2 (p*T)) := by
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · exact shiftedResidue_mem_window p T _ hp hT le_rfl
  · exact shiftedResidue_mem_window p d _ hp (hdT.trans_lt hT) (Nat.mul_le_mul_left p hdT)

theorem mixedFloorColumn_head (p T d n : ℕ) (hp : p.Prime) (hT : T < p)
    (hdT : d ≤ T) (hd : 0 < d) (hn : n < T) :
    hilbertSequence (mixedFloorColumn p T d) n = ((n / d : ℕ) : ℝ) := by
  rw [← anchoredEvaluationCLM_apply, mixedFloorColumn, map_smul, map_sub,
    anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply,
    shiftedResidue_head p T n hp hT (by omega) (hn.trans hT),
    shiftedResidue_head p d n hp (hdT.trans_lt hT) hd (hn.trans hT)]
  simp only [smul_eq_mul, residue, Nat.mod_eq_of_lt hn]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdiv : (n % d : ℕ) + d * (n / d) = n := Nat.mod_add_div n d
  have he : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hdiv
  field_simp [hd']
  linarith

/-- A fixed finite mixed window realizes the invertible floor synthesis of every head. -/
theorem explicit_floor_mixed_interpolation (N p T : ℕ) (hp : p.Prime) (hT : T < p)
    (hN : N < T) (a : Fin N → ℝ) :
    ∃ m ∈ mixedSpace (Finset.Icc 2 (p*T)), headRestriction N m = a := by
  let c := ((floorMatrix N)⁻¹).mulVec a
  let m := ∑ j : Fin N, c j • mixedFloorColumn p T (j.val+1)
  refine ⟨m, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (mixedFloorColumn_mem_window p T _ hp hT
      (by have := j.isLt; omega))
  · have hmat : (floorMatrix N).mulVec c = a := by
      dsimp [c]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        (by rw [floorMatrix_det]; exact isUnit_one), Matrix.one_mulVec]
    funext i
    rw [← congrFun hmat i]
    change headRestriction N (∑ j : Fin N, c j • mixedFloorColumn p T (j.val+1)) i = _
    rw [map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, headRestriction_apply]
    change (∑ j : Fin N, c j * hilbertSequence (mixedFloorColumn p T (j.val+1)) (i.val+1)) =
      ∑ j : Fin N, floorMatrix N i j * c j
    apply Finset.sum_congr rfl
    intro j _
    rw [mixedFloorColumn_head p T _ _ hp hT (by have := j.isLt; omega) (by omega)
      (by have := i.isLt; omega)]
    exact mul_comm _ _

/-- A uniform quadratic bound on the conductors needed for arbitrary head data.
This bounds the dictionary window, with no claim of a uniform Pareto norm. -/
theorem quadratic_window_mixed_head (N : ℕ) (a : Fin N → ℝ) :
    ∃ m ∈ mixedSpace (Finset.Icc 2 (2*(N+1)^2)), headRestriction N m = a := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N+1) (by omega)
  obtain ⟨m, hm, hh⟩ := explicit_floor_mixed_interpolation N p (N+1) hp hlt (by omega) a
  have hB : p*(N+1) ≤ 2*(N+1)^2 := by
    calc p*(N+1) ≤ (2*(N+1))*(N+1) := Nat.mul_le_mul_right (N+1) hle
         _ = 2*(N+1)^2 := by ring
  exact ⟨m, mixedSpace_mono (Finset.Icc_subset_Icc le_rfl hB) hm, hh⟩

/-- Norms attained by exactly head-compatible sections in any single finite mixed window. -/
def finiteSectionNorms (g : ThresholdHilbert) (N : ℕ) : Set ℝ :=
  {a | ∃ B : ℕ, ∃ m : ThresholdHilbert, m ∈ mixedSpace (Finset.Icc 2 B) ∧
    g + m ∈ fiber N ∧ ‖g + m‖ = a}

theorem exists_finite_section_near_minimum (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hmean : inner ℝ g hilbertOne = 1) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ finiteSectionNorms g N, a < kappa N + ε := by
  have hp := (patch_spec N).1
  have hmixed : patch N - g ∈ mixedClosure := by
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    exact ⟨closedSpace.sub_mem hp.1 hg, by rw [inner_sub_left, hp.2.1, hmean, sub_self]⟩
  obtain ⟨B, m, hm, hh, hdist⟩ := exists_finite_window_near_with_same_head g hmixed N hε
  obtain ⟨hmV, hm0⟩ := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero m).mp
    (mixedSpace_window_le_closure B hm)
  have hfeas : g + m ∈ fiber N := by
    refine ⟨closedSpace.add_mem hg hmV, by rw [inner_add_left, hmean, hm0, add_zero], ?_⟩
    intro i hi
    have he := congrArg (fun x => hilbertSequence x (i+1)) hh
    simp only [compactHead_sequence, if_pos (show i+1 ≤ N by omega)] at he
    rw [physicalEvaluationCLM_apply, he]
    simpa only [physicalEvaluationCLM_apply] using hp.2.2 i hi
  refine ⟨‖g + m‖, ⟨B, m, hm, hfeas, rfl⟩, ?_⟩
  calc
    ‖g + m‖ = ‖(g + m - patch N) + patch N‖ := by rw [sub_add_cancel]
    _ ≤ ‖g + m - patch N‖ + ‖patch N‖ := norm_add_le _ _
    _ < kappa N + ε := by
      rw [norm_sub_rev]
      change ‖patch N - (g + m)‖ + ‖patch N‖ < ‖patch N‖ + ε
      linarith

theorem kappa_isGLB_finiteSectionNorms (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hmean : inner ℝ g hilbertOne = 1) (N : ℕ) :
    IsGLB (finiteSectionNorms g N) (kappa N) := by
  refine ⟨?_, ?_⟩
  · rintro a ⟨B, m, _, hfeas, rfl⟩
    exact (kappa_isLeast N).2 ⟨g + m, hfeas, rfl⟩
  · intro b hb
    by_contra h
    have hpos : 0 < b - kappa N := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨a, ha, hlt⟩ := exists_finite_section_near_minimum g hg hmean N hpos
    have hba := hb ha
    linarith

/-- The finite infimum equals the norm of the canonical closed section, for every physical head. -/
theorem sInf_finiteSectionNorms (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hmean : inner ℝ g hilbertOne = 1) (N : ℕ) :
    sInf (finiteSectionNorms g N) = kappa N := by
  obtain ⟨a, ha, _⟩ := exists_finite_section_near_minimum g hg hmean N (by norm_num : (0 : ℝ) < 1)
  have h := kappa_isGLB_finiteSectionNorms g hg hmean N
  exact (isGLB_csInf ⟨a, ha⟩ ⟨_, h.1⟩).unique h

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadFiniteMinimum

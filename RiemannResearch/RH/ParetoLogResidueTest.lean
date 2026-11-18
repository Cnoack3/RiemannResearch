import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoInitialIntervalCriterion
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.ResidueConductorVariation
import RiemannResearch.RH.TailCapacityDilationCorrection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The constant log-residue test and the projected constant

Source: Christian Noack's question about taking the test vector to be the
constant in Section 2 of *The one-dimensional Pareto reduction*.
The raw log moments identify a unique member of the closed residue space.
Integer dilation gives a signed test for equality with the constant using
any nonempty physical initial interval.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The constant vector gives the logarithmic pairing for every raw residue. -/
theorem inner_rawResidueAtom_hilbertOne (k : ℕ) :
    inner ℝ (rawResidueAtom k) hilbertOne = Real.log ((k + 2 : ℕ) : ℝ) := by
  have hseq : hilbertSequence (rawResidueAtom k) = residue (k + 2) := by
    funext n
    rw [rawResidueAtom_sequence]
  rw [hilbert_inner_one, hseq, paretoMean_residue (k + 2) (by omega)]

/-- The constant is a test vector with exactly the logarithmic residue moments. -/
theorem residuePairing_hilbertOne (d : ℕ) (hd : 0 < d) :
    residuePairing hilbertOne d = Real.log (d : ℝ) := by
  by_cases h : d = 1
  · simp [h, residuePairing]
  · have hd' : 1 < d := by omega
    rw [residuePairing, if_pos hd', inner_rawResidueAtom_hilbertOne,
      show d - 2 + 2 = d by omega]

/-- The vectors with the log-residue moments of the constant are its translate
by the orthogonal complement of the entire residue space. -/
theorem logResidueMoments_iff_sub_mem_orthogonal (x : ThresholdHilbert) :
    (∀ k : ℕ, inner ℝ (rawResidueAtom k) x = Real.log ((k + 2 : ℕ) : ℝ)) ↔
      x - hilbertOne ∈ closedSpaceᗮ := by
  let S := Submodule.span ℝ (Set.range residueAtom)
  have hcl : closedSpace = (Sᗮ)ᗮ :=
    (Submodule.orthogonal_orthogonal_eq_closure S).symm
  constructor
  · intro hf
    have hz : x - hilbertOne ∈ Sᗮ := by
      apply (S.mem_orthogonal _).mpr
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        have hraw : inner ℝ (rawResidueAtom k) (x - hilbertOne) = 0 := by
          rw [inner_sub_right, hf k, inner_rawResidueAtom_hilbertOne, sub_self]
        rw [rawResidueAtom, real_inner_smul_left] at hraw
        exact (mul_eq_zero.mp hraw).resolve_left (by positivity)
      | zero => simp
      | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
      | smul c a _ ha => simp [real_inner_smul_left, ha]
    rw [hcl]
    intro y hy
    exact (real_inner_comm _ _).trans (hy _ hz)
  · intro hz k
    have hm : rawResidueAtom k ∈ closedSpace :=
      closedSpace.smul_mem _ (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨k, rfl⟩))
    have h := (closedSpace.mem_orthogonal _).mp hz _ hm
    rwa [inner_sub_right, inner_rawResidueAtom_hilbertOne, sub_eq_zero] at h

/-- On the legal space, log-residue matching characterizes the orthogonal
projection of the constant. -/
theorem legal_logResidueMoments_iff_eq_limitProjection {x : ThresholdHilbert}
    (hx : x ∈ closedSpace) :
    (∀ k : ℕ, inner ℝ (rawResidueAtom k) x = Real.log ((k + 2 : ℕ) : ℝ)) ↔
      x = limitProjection := by
  rw [logResidueMoments_iff_sub_mem_orthogonal]
  constructor
  · intro hz
    have hv : x - limitProjection ∈ closedSpace :=
      closedSpace.sub_mem hx (closedSpace.starProjection_apply_mem hilbertOne)
    have ho : x - limitProjection ∈ closedSpaceᗮ := by
      have hr := closedSpace.orthogonal.add_mem hz limitResidual_mem_orthogonal
      have he : x - hilbertOne + limitResidual = x - limitProjection := by
        unfold limitResidual
        abel
      rwa [he] at hr
    have hb : x - limitProjection ∈ closedSpace ⊓ closedSpaceᗮ := ⟨hv, ho⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hb
  · rintro rfl
    rw [show limitProjection - hilbertOne = -limitResidual by
      unfold limitResidual
      abel]
    exact closedSpace.orthogonal.neg_mem limitResidual_mem_orthogonal

/-- Uniqueness in the full Hilbert space is equivalent to target membership. -/
theorem logResidueMoments_unique_iff_one_mem :
    (∀ x : ThresholdHilbert,
      (∀ k : ℕ, inner ℝ (rawResidueAtom k) x = Real.log ((k + 2 : ℕ) : ℝ)) →
        x = hilbertOne) ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have hp : limitProjection ∈ closedSpace := closedSpace.starProjection_apply_mem hilbertOne
    have he := h limitProjection ((legal_logResidueMoments_iff_eq_limitProjection hp).mpr rfl)
    exact he ▸ hp
  · intro h x hx
    have ht := closedSpace_eq_top_iff_one_mem.mpr h
    have hv : x ∈ closedSpace := by simp [ht]
    exact ((legal_logResidueMoments_iff_eq_limitProjection hv).mp hx).trans
      ((Submodule.starProjection_eq_self_iff).mpr h)

/-- The complete signed residual mass on the first `m` sites. -/
theorem limitResidual_inner_compactHead_one (m : ℕ) :
    inner ℝ limitResidual (compactHead m hilbertOne) =
      limitEnergy -
        inner ℝ limitResidual (unscaledResidueDilation (m + 1) (by omega) limitResidual) := by
  rw [compactHead_one_eq_dilationDifference, inner_sub_right, limitResidual_inner_one]
  have hd : inner ℝ limitResidual (unscaledResidueDilation (m + 1) (by omega) hilbertOne) =
      inner ℝ limitResidual (unscaledResidueDilation (m + 1) (by omega) limitResidual) := by
    change inner ℝ limitResidual ((1 / ((m + 1 : ℕ) : ℝ)) •
        hilbertDilation (m + 1) (by omega) hilbertOne) =
      inner ℝ limitResidual ((1 / ((m + 1 : ℕ) : ℝ)) •
        hilbertDilation (m + 1) (by omega) limitResidual)
    rw [real_inner_smul_right, real_inner_smul_right, limitResidual_inner_dilation_one]
  rw [hd]

/-- Both bounds retain the same complete residual norm on every initial interval. -/
theorem limitResidual_compactHead_one_bounds (m : ℕ) :
    (1 - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * limitEnergy ≤
      inner ℝ limitResidual (compactHead m hilbertOne) ∧
      inner ℝ limitResidual (compactHead m hilbertOne) ≤
        (1 + 1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * limitEnergy := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) limitResidual
    (unscaledResidueDilation (m + 1) (by omega) limitResidual)
  rw [Real.norm_eq_abs, unscaledResidueDilation_norm] at hc
  have hb : |inner ℝ limitResidual
      (unscaledResidueDilation (m + 1) (by omega) limitResidual)| ≤
      (1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * limitEnergy := by
    refine hc.trans_eq ?_
    change ‖limitResidual‖ * ((1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * ‖limitResidual‖) =
      (1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) * ‖limitResidual‖ ^ 2
    ring
  rw [limitResidual_inner_compactHead_one]
  constructor <;> nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]

/-- Nonpositive residual mass on any one nonempty initial interval forces
membership of the constant in the residue closure. -/
theorem limitResidual_compactHead_one_nonpos_iff_one_mem (m : ℕ) (hm : 0 < m) :
    inner ℝ limitResidual (compactHead m hilbertOne) ≤ 0 ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    have hk : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < m + 1 by omega)
    have hs : 1 < Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hk
    have hf : 0 < 1 - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ) :=
      sub_pos.mpr ((div_lt_one (by linarith)).2 hs)
    have hb := (limitResidual_compactHead_one_bounds m).1.trans h
    have he : 0 ≤ limitEnergy := sq_nonneg _
    exact limitEnergy_zero_iff_mem.mp
      (le_antisymm ((nonpos_of_mul_nonpos_right hb hf)) he)
  · intro h
    rw [limitResidual_zero_iff_energy_zero.mpr (limitEnergy_zero_iff_mem.mpr h),
      inner_zero_left]

/-- Conditional RH reduction through the signed residual on a prescribed
nonempty physical initial interval. -/
theorem riemannHypothesis_of_nonpositive_compactHead_residual (m : ℕ) (hm : 0 < m)
    (h : inner ℝ limitResidual (compactHead m hilbertOne) ≤ 0) : RiemannHypothesis :=
  riemannHypothesis_of_firstCoordinate_zero
    (firstCoordinate_zero_iff_residual_zero.mpr
      (limitResidual_zero_iff_energy_zero.mpr
        (limitEnergy_zero_iff_mem.mpr
          ((limitResidual_compactHead_one_nonpos_iff_one_mem m hm).mp h))))

end RiemannResearch.RH.Pareto.CoefficientStabilization

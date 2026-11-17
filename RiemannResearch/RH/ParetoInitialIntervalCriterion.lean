import RiemannResearch.RH.TailCapacityDilationCorrection
import RiemannResearch.RH.ParetoCompactHead

/-!
# Initial intervals and floor-dilation differences
Source: Christian Noack's November 17, 2026 question about lifting initial-interval
indicators in the Nyman--Beurling residue closure. The finite case k=2 is developed
in PointTargetDilationSynthesis; this argument treats every target and every k>1.
The physical indicator of 1 through m is the difference of the constant and
its unscaled dilation by m+1. The strict contraction detects membership in
the full closed residue span, even for a single nonempty interval.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

private theorem dilation_preserves_closure (k : ℕ) (hk : 0 < k)
    {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    unscaledResidueDilation k hk x ∈ closedSpace :=
  closedSpace.smul_mem _ (closedSpace_dilation hx k hk)

/-- A strict floor-dilation difference detects membership for every target. -/
theorem dilationDifference_mem_iff (k : ℕ) (hk : 1 < k) (x : ThresholdHilbert) :
    x - unscaledResidueDilation k (by omega) x ∈ closedSpace ↔ x ∈ closedSpace := by
  let T := unscaledResidueDilation k (by omega)
  let p := closedSpace.starProjection x
  have hp : p ∈ closedSpace := closedSpace.starProjection_apply_mem x
  constructor
  · intro h
    let y := (x - T x) + T p
    have hy : y ∈ closedSpace := closedSpace.add_mem h (dilation_preserves_closure k (by omega) hp)
    have ho : inner ℝ (x - p) (p - y) = 0 := by
      rw [real_inner_comm]
      exact (closedSpace.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x)
        _ (closedSpace.sub_mem hp hy)
    have he : x - y = (x - p) + (p - y) := by abel
    have hmin : ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [he, norm_add_sq_real, ho]
      nlinarith only [sq_nonneg ‖p - y‖]
    have hres : x - y = T (x - p) := by
      dsimp only [y]
      rw [map_sub]
      abel
    rw [hres, unscaledResidueDilation_norm_sq] at hmin
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hi := (le_div_iff₀ (by linarith : (0:ℝ) < k)).mp hmin
    have hz : x = p := by
      by_contra hn
      have hpos : 0 < ‖x - p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
      nlinarith only [hi, mul_pos hpos (sub_pos.mpr hkR)]
    exact hz ▸ hp
  · intro hx
    exact closedSpace.sub_mem hx (dilation_preserves_closure k (by omega) hx)

/-- Exact physical coordinates, including the zero anchor. -/
theorem compactHead_one_eq_dilationDifference (m : ℕ) :
    compactHead m hilbertOne = hilbertOne - unscaledResidueDilation (m+1) (by omega) hilbertOne := by
  apply hilbertSequence_injective
  funext n
  rw [compactHead_sequence, show hilbertSequence (hilbertOne -
    unscaledResidueDilation (m+1) (by omega) hilbertOne) n =
    hilbertSequence hilbertOne n -
      hilbertSequence (unscaledResidueDilation (m+1) (by omega) hilbertOne) n from
      congrFun (hilbertSequenceLinear.map_sub _ _) n, unscaledResidueDilation_sequence]
  by_cases hn : n ≤ m
  · rw [if_pos hn, Nat.div_eq_of_lt (by omega), hilbertSequence_zero, sub_zero]
  · have hpos : n / (m+1) ≠ 0 := Nat.ne_of_gt (Nat.div_pos (by omega) (by omega))
    have hn0 : n ≠ 0 := by omega
    simp [hn, hilbertOne_sequence, zeroAnchor, hn0, hpos]

/-- One nonempty initial interval is equivalent to the full constant target. -/
theorem compactHead_one_mem_iff (m : ℕ) (hm : 0 < m) :
    compactHead m hilbertOne ∈ closedSpace ↔ hilbertOne ∈ closedSpace := by
  rw [compactHead_one_eq_dilationDifference]
  exact dilationDifference_mem_iff (m+1) (by omega) hilbertOne

end RiemannResearch.RH.Pareto.CoefficientStabilization

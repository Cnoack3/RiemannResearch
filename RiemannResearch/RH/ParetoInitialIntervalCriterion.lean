import RiemannResearch.Analysis.OrthogonalDistanceBound
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ResidueClosureDensity
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
The quantitative continuation gives an exact signed energy identity, two-sided
bounds on quotient distances, and a transfer for finite approximants.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

open RiemannResearch.Analysis.ExhaustiveWalk

private theorem dilation_preserves_closure (k : ℕ) (hk : 0 < k)
    {x : ThresholdHilbert} (hx : x ∈ closedSpace) :
    unscaledResidueDilation k hk x ∈ closedSpace :=
  closedSpace.smul_mem _ (closedSpace_dilation hx k hk)

/-- Exact quotient energy. The square projected back into the span and the signed
correlation both contribute, even though only forward dilation invariance is used. -/
theorem dilationDifference_infDist_sq (k : ℕ) (hk : 0 < k) (x y : ThresholdHilbert) :
    let r := y - closedSpace.starProjection y
    Metric.infDist (x - unscaledResidueDilation k hk y) (closedSpace : Set ThresholdHilbert) ^ 2 =
      Metric.infDist x (closedSpace : Set ThresholdHilbert) ^ 2 + ‖r‖ ^ 2 / (k : ℝ) -
        ‖closedSpace.starProjection (unscaledResidueDilation k hk r)‖ ^ 2 -
        2 * inner ℝ (x - closedSpace.starProjection x) (unscaledResidueDilation k hk r) := by
  dsimp only
  rw [closedSpace.infDist_sub_map_sq_of_invariant (unscaledResidueDilation k hk)
    (fun _ hz => dilation_preserves_closure k hk hz), unscaledResidueDilation_norm_sq]

/-- Two-target perturbation estimate for the full residue closure. -/
theorem abs_infDist_dilationDifference_sub_le (k : ℕ) (hk : 0 < k) (x y : ThresholdHilbert) :
    |Metric.infDist (x - unscaledResidueDilation k hk y) (closedSpace : Set ThresholdHilbert) -
      Metric.infDist x (closedSpace : Set ThresholdHilbert)| ≤
      (1 / Real.sqrt k) * Metric.infDist y (closedSpace : Set ThresholdHilbert) :=
  closedSpace.abs_infDist_sub_map_sub_le _ (fun _ hz => dilation_preserves_closure k hk hz)
    (fun z => (unscaledResidueDilation_norm k hk z).le) x y

/-- Both quotient-distance bounds hold for every positive dilation, including the endpoint. -/
theorem dilationDifference_infDist_bounds (k : ℕ) (hk : 0 < k) (x : ThresholdHilbert) :
    (1 - 1 / Real.sqrt k) * Metric.infDist x (closedSpace : Set ThresholdHilbert) ≤
        Metric.infDist (x - unscaledResidueDilation k hk x) (closedSpace : Set ThresholdHilbert) ∧
      Metric.infDist (x - unscaledResidueDilation k hk x) (closedSpace : Set ThresholdHilbert) ≤
        (1 + 1 / Real.sqrt k) * Metric.infDist x (closedSpace : Set ThresholdHilbert) := by
  have h := abs_le.mp (abs_infDist_dilationDifference_sub_le k hk x x)
  constructor <;> linarith only [h.1, h.2]

private theorem dilation_gap_pos (k : ℕ) (hk : 1 < k) : 0 < 1 - 1 / Real.sqrt (k : ℝ) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hs : 1 < Real.sqrt (k : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hkR
  exact sub_pos.mpr ((div_lt_one (by linarith)).2 hs)

private theorem mem_closedSpace_of_infDist_zero {x : ThresholdHilbert}
    (h : Metric.infDist x (closedSpace : Set ThresholdHilbert) = 0) : x ∈ closedSpace := by
  rw [closedSpace.infDist_eq_norm_sub_starProjection, norm_eq_zero, sub_eq_zero] at h
  exact h ▸ closedSpace.starProjection_apply_mem x

/-- A strict floor-dilation difference detects membership for every target. -/
theorem dilationDifference_mem_iff (k : ℕ) (hk : 1 < k) (x : ThresholdHilbert) :
    x - unscaledResidueDilation k (by omega) x ∈ closedSpace ↔ x ∈ closedSpace := by
  constructor
  · intro h
    have hl := (dilationDifference_infDist_bounds k (by omega) x).1
    rw [Metric.infDist_zero_of_mem h] at hl
    apply mem_closedSpace_of_infDist_zero
    apply le_antisymm _ Metric.infDist_nonneg
    by_contra! hp
    exact (not_lt_of_ge hl) (mul_pos (dilation_gap_pos k hk) hp)
  · intro hx
    exact closedSpace.sub_mem hx (dilation_preserves_closure k (by omega) hx)

/-- Exact physical coordinates, including the zero anchor. -/
theorem compactHead_one_eq_dilationDifference (m : ℕ) :
    compactHead m hilbertOne =
      hilbertOne - unscaledResidueDilation (m+1) (by omega) hilbertOne := by
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

/-- Initial intervals sandwich the global distance with explicit relative error. -/
theorem compactHead_one_infDist_bounds (m : ℕ) :
    (1 - 1 / Real.sqrt ((m : ℝ) + 1)) *
        Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) ≤
        Metric.infDist (compactHead m hilbertOne) (closedSpace : Set ThresholdHilbert) ∧
      Metric.infDist (compactHead m hilbertOne) (closedSpace : Set ThresholdHilbert) ≤
        (1 + 1 / Real.sqrt ((m : ℝ) + 1)) *
        Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) := by
  rw [compactHead_one_eq_dilationDifference]
  simpa only [Nat.cast_add, Nat.cast_one] using
    dilationDifference_infDist_bounds (m+1) (by omega) hilbertOne

/-- A trial in a finite residue span transfers its full Hilbert error on the
interval to the constant target. The denominator is positive at each nonempty head. -/
theorem one_infDist_le_of_compactHead_finiteTrial (m : ℕ) (hm : 0 < m) (n : ℕ)
    {q : ThresholdHilbert} (hq : q ∈ finiteSpace n) :
    Metric.infDist hilbertOne (closedSpace : Set ThresholdHilbert) ≤
      ‖compactHead m hilbertOne - q‖ / (1 - 1 / Real.sqrt ((m : ℝ) + 1)) := by
  have hc : 0 < 1 - 1 / Real.sqrt ((m : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using dilation_gap_pos (m + 1) (by omega)
  have hq' : q ∈ closedSpace :=
    (Submodule.le_topologicalClosure _) (walkSpan_le residueAtom id n hq)
  apply (le_div_iff₀ hc).2
  rw [mul_comm]
  exact (compactHead_one_infDist_bounds m).1.trans
    (by simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := compactHead m hilbertOne) hq'))

/-- For any fixed nonempty head, density is equivalent to vanishing of the
actual finite least-squares errors, with the whole physical tail included. -/
theorem closedSpace_eq_top_iff_compactHead_one_walkError_tendsto (m : ℕ) (hm : 0 < m) :
    closedSpace = ⊤ ↔ Filter.Tendsto (walkError residueAtom id (compactHead m hilbertOne))
      Filter.atTop (nhds 0) :=
  closedSpace_eq_top_iff_one_mem.trans ((compactHead_one_mem_iff m hm).symm.trans
    (walkError_tendsto_zero_iff residueAtom id Function.surjective_id _).symm)

/-- Head sizes may vary with the tolerance. The positive distance factor for
the singleton is a uniform lower bound over all nonempty initial intervals. -/
theorem closedSpace_eq_top_iff_arbitrarily_small_compactHead_one :
    closedSpace = ⊤ ↔ ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧
      Metric.infDist (compactHead m hilbertOne) (closedSpace : Set ThresholdHilbert) < ε := by
  constructor
  · intro ht ε hε
    have hm : compactHead 1 hilbertOne ∈ closedSpace := by rw [ht]; trivial
    exact ⟨1, by decide, (Metric.infDist_zero_of_mem hm).trans_lt hε⟩
  · intro h
    apply closedSpace_eq_top_iff_one_mem.mpr
    apply mem_closedSpace_of_infDist_zero
    apply le_antisymm _ Metric.infDist_nonneg
    by_contra! hpos
    have hc : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := by
      simpa only [Nat.cast_ofNat] using dilation_gap_pos 2 (by decide)
    obtain ⟨m, hm, hsmall⟩ := h _ (mul_pos hc hpos)
    have hmR : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (show 2 ≤ m + 1 by omega)
    have hden : 1 - 1 / Real.sqrt 2 ≤ 1 - 1 / Real.sqrt ((m : ℝ) + 1) :=
      sub_le_sub_left (one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt hmR)) _
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hden hpos.le).trans
      (compactHead_one_infDist_bounds m).1)) hsmall

end RiemannResearch.RH.Pareto.CoefficientStabilization

import RiemannResearch.Analysis.HilbertWeakNorm
import RiemannResearch.RH.RamanujanTailTightness
import RiemannResearch.RH.RamanujanPointwiseCriterion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Bounded pointwise Ramanujan families: weak and strong convergence

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
Eventual boundedness plus pointwise physical convergence determines every
continuous Hilbert observation. A matching one-sided norm bound upgrades
the actual family to strong convergence. The two laws keep their own norms.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanWeakConvergence
open Pareto ZetaTwoHilbert
open RamanujanTailTightness
open RiemannResearch.Analysis.SequenceHeadTail
open RiemannResearch.Analysis.HilbertWeakNorm

theorem innerWeak_of_bounded_coordinates {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert)
    (hpoint : ∀ n, Tendsto (fun i => F i n) l (𝓝 (x n)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ C) :
    InnerWeakTendsto F l x := by
  have hecoord (n : ℕ) :
      Tendsto (fun i => (F i - x : ThresholdHilbert) n) l (𝓝 0) := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, PiLp.sub_apply, sub_self] using
      (hpoint n).sub_const (x n)
  let D : ℝ := max (2 * C + 2 * ‖x‖ ^ 2) 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have heBound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ D := by
    filter_upwards [hbound] with i hi
    have hp := parallelogram_law_with_norm ℝ (F i) x
    have hm := le_max_left (2 * C + 2 * ‖x‖ ^ 2) 0
    dsimp [D]
    nlinarith [sq_nonneg ‖F i + x‖]
  intro v
  have hz : Tendsto (fun i => inner ℝ v (F i - x)) l (𝓝 0) := by
    apply NormedAddCommGroup.tendsto_nhds_zero.mpr
    intro ε hε
    have ht := (hilbertTailShift_energy_tendsto_zero v).eventually_lt_const
      (show 0 < ε ^ 2 / (4 * D) by positivity)
    obtain ⟨N, hN⟩ := ht.exists
    have hh : Tendsto (fun i => |headPair N v (F i - x : ThresholdHilbert)|)
        l (𝓝 0) := by
      simpa only [Real.norm_eq_abs, norm_zero] using
        (headPair_tendsto_zero (l := l) N v
          (fun i n => (F i - x : ThresholdHilbert) n) hecoord).norm
    have hh' : ∀ᶠ i in l, |headPair N v (F i - x : ThresholdHilbert)| < ε / 2 := by
      exact hh.eventually_lt_const (show 0 < ε / 2 by positivity)
    filter_upwards [heBound, hh'] with i hi hhi
    have htail : ‖hilbertTailShift (F i - x) N‖ ^ 2 ≤ D := by
      have he := hilbert_head_tail_energy (F i - x) N
      have hn := headSquare_nonneg N (F i - x : ThresholdHilbert)
      linarith
    have hcs := hilbert_tail_pairing_sq_le v (F i - x) N
    have hmul := mul_le_mul_of_nonneg_left htail (sq_nonneg ‖hilbertTailShift v N‖)
    have hsmall := (lt_div_iff₀ (show 0 < 4 * D by positivity)).mp hN
    have habs : |inner ℝ (hilbertTailShift v N) (hilbertTailShift (F i - x) N)| < ε / 2 := by
      apply (sq_lt_sq₀ (abs_nonneg _) (show 0 ≤ ε / 2 by positivity)).mp
      rw [sq_abs]
      nlinarith
    have hsplit : inner ℝ v (F i - x) =
        headPair N v (F i - x : ThresholdHilbert) +
        inner ℝ (hilbertTailShift v N) (hilbertTailShift (F i - x) N) := by
      simpa only [headPair, hilbertShellPairing, Nat.add_zero] using
        (hilbert_head_tail_pairing v (F i - x) N).symm
    rw [Real.norm_eq_abs, hsplit]
    exact (abs_add_le _ _).trans_lt (by linarith)
  have ht := hz.add_const (inner ℝ v x)
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using ht

theorem pareto_innerWeak_of_bounded_pointwise {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 (hilbertSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ C) :
    InnerWeakTendsto F l x :=
  innerWeak_of_bounded_coordinates (l := l) F x
    ((pareto_physical_pointwise_iff (l := l) F x).mp hpoint) C hbound

theorem q_innerWeak_of_bounded_pointwise {α : Type*} {l : Filter α}
    (F : α → QHilbert) (x : QHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k)))
    (C : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ C) :
    InnerWeakTendsto F l x :=
  innerWeak_of_bounded_coordinates (l := l) F x
    ((q_physical_pointwise_iff (l := l) F x).mp hpoint) C hbound

/-- Physical pointwise convergence and a one-sided norm limit bound force the full tails to vanish. -/
theorem pareto_tendsto_of_pointwise_and_norm_upper {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 (hilbertSequence x k)))
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖F i‖ ^ 2 < ‖x‖ ^ 2 + ε) :
    Tendsto F l (𝓝 x) := by
  have hb : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ ‖x‖ ^ 2 + 1 :=
    (hn 1 (by norm_num)).mono (fun i hi => hi.le)
  exact tendsto_of_innerWeak_and_norm_upper (l := l) F x
    (pareto_innerWeak_of_bounded_pointwise (l := l) F x hpoint _ hb) hn

theorem q_tendsto_of_pointwise_and_norm_upper {α : Type*} {l : Filter α}
    (F : α → QHilbert) (x : QHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k)))
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖F i‖ ^ 2 < ‖x‖ ^ 2 + ε) :
    Tendsto F l (𝓝 x) := by
  have hb : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ ‖x‖ ^ 2 + 1 :=
    (hn 1 (by norm_num)).mono (fun i hi => hi.le)
  exact tendsto_of_innerWeak_and_norm_upper (l := l) F x
    (q_innerWeak_of_bounded_pointwise (l := l) F x hpoint _ hb) hn

end RiemannResearch.RH.RamanujanWeakConvergence

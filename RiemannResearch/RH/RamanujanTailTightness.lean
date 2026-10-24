import RiemannResearch.Analysis.NonnegativeSeriesTightness
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import RiemannResearch.RH.ApproximateHeadResidualTail
import RiemannResearch.RH.RamanujanTrialConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual P/Q strong convergence and full physical-tail tightness

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
The criterion applies to arbitrary targets and filter-indexed families. It
distinguishes pointwise approximation from strong approximation by a precise
uniform condition on complete infinite tails. Tail subtraction retains its
signed pairing before any estimate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanTailTightness
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open RiemannResearch.Analysis.SequenceHeadTail
open RiemannResearch.Analysis.NonnegativeSeriesTightness
open RiemannResearch.Analysis.NonnegativeErrorConvergence

def EnergyTight {α : Type*} (F : α → ThresholdHilbert) (l : Filter α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ i in l, ‖hilbertTailShift (F i) N‖ ^ 2 < ε

theorem tailShift_sub (f g : ThresholdHilbert) (N : ℕ) :
    hilbertTailShift (f - g) N = hilbertTailShift f N - hilbertTailShift g N := by
  apply Subtype.ext
  funext n
  rfl

/-- Exact signed tail-energy identity, valid before any tightness bound. -/
theorem tail_sub_energy (f g : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift (f - g) N‖ ^ 2 =
      ‖hilbertTailShift f N‖ ^ 2 + ‖hilbertTailShift g N‖ ^ 2 -
        2 * inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) := by
  rw [tailShift_sub, norm_sub_sq_real] <;> ring

theorem tail_sub_energy_le (f g : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift (f - g) N‖ ^ 2 ≤
      2 * ‖hilbertTailShift f N‖ ^ 2 + 2 * ‖hilbertTailShift g N‖ ^ 2 := by
  rw [tailShift_sub]
  have h := parallelogram_law_with_norm ℝ (hilbertTailShift f N) (hilbertTailShift g N)
  nlinarith [sq_nonneg ‖hilbertTailShift f N + hilbertTailShift g N‖]

theorem tail_energy_antitone (f : ThresholdHilbert) :
    Antitone (fun N => ‖hilbertTailShift f N‖ ^ 2) := by
  intro N M hNM
  have hh : headSquare N f ≤ headSquare M f := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun n hn hnot => sq_nonneg (f n))
  change ‖hilbertTailShift f M‖ ^ 2 ≤ ‖hilbertTailShift f N‖ ^ 2
  rw [hilbertTailShift_norm_sq f M, hilbertTailShift_norm_sq f N]
  exact sub_le_sub_left hh _

theorem energyTight_sub_const {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) (hF : EnergyTight F l) :
    EnergyTight (fun i => F i - x) l := by
  intro ε hε
  obtain ⟨N, hN⟩ := hF (ε / 4) (by linarith)
  have hx := (hilbertTailShift_energy_tendsto_zero x).eventually_lt_const
    (show 0 < ε / 4 by linarith)
  obtain ⟨M, hM⟩ := hx.exists
  refine ⟨max N M, ?_⟩
  filter_upwards [hN] with i hi
  have hf := tail_energy_antitone (F i) (le_max_left N M)
  have hg := tail_energy_antitone x (le_max_right N M)
  have he := tail_sub_energy_le (F i) x (max N M)
  linarith

theorem energyTight_sub_const_iff {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) :
    EnergyTight (fun i => F i - x) l ↔ EnergyTight F l := by
  constructor
  · intro h
    simpa only [sub_neg_eq_add, sub_add_cancel] using
      energyTight_sub_const (fun i => F i - x) (-x) h
  · exact energyTight_sub_const F x

private theorem real_coordinate_square_iff {α : Type*} {l : Filter α}
    (f : α → ℝ) (x : ℝ) :
    Tendsto (fun i => (f i - x) ^ 2) l (𝓝 0) ↔ Tendsto f l (𝓝 x) := by
  constructor
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply (norm_zero_iff_square (fun i => f i - x)).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using h
  · intro h
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    have hs := (norm_zero_iff_square (fun i => f i - x)).mp hn
    simpa only [Real.norm_eq_abs, sq_abs] using hs

/-- Raw coordinates and complete tails characterize norm convergence on the shared l2 carrier. -/
theorem tendsto_iff_coordinates_tight {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) :
    Tendsto F l (𝓝 x) ↔
      (∀ n, Tendsto (fun i => F i n) l (𝓝 (x n))) ∧ EnergyTight F l := by
  let a : α → ℕ → ℝ := fun i n => ((F i - x : ThresholdHilbert) n) ^ 2
  have hs := tsum_tendsto_zero_iff (l := l) a (fun i n => sq_nonneg _)
    (fun i => hilbert_coordinate_square_summable (F i - x))
  have hc : (∀ n, Tendsto (fun i => a i n) l (𝓝 0)) ↔
      ∀ n, Tendsto (fun i => F i n) l (𝓝 (x n)) := by
    apply forall_congr'
    intro n
    exact real_coordinate_square_iff (fun i => F i n) (x n)
  have ht : UniformTails a l ↔ EnergyTight (fun i => F i - x) l := by
    simp only [UniformTails, EnergyTight, hilbert_norm_sq, hilbertTailShift, a]
  have hn : Tendsto F l (𝓝 x) ↔ Tendsto (fun i => ∑' n, a i n) l (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero, norm_zero_iff_square]
    simp only [hilbert_norm_sq, a]
  exact hn.trans (hs.trans (and_congr hc (ht.trans (energyTight_sub_const_iff F x))))

theorem pareto_physical_pointwise_iff {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) :
    (∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 (hilbertSequence x k))) ↔
      ∀ n, Tendsto (fun i => F i n) l (𝓝 (x n)) := by
  constructor
  · intro h n
    have hn : Real.sqrt (paretoWeight n) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    have ht := (h (n + 1) (by omega)).mul_const (Real.sqrt (paretoWeight n))
    simpa only [hilbertSequence_succ, div_mul_cancel₀ _ hn] using ht
  · intro h k hk
    have ht := (h (k - 1)).div_const (Real.sqrt (paretoWeight (k - 1)))
    have he : k - 1 + 1 = k := by omega
    simpa only [← hilbertSequence_succ, he] using ht

theorem q_physical_pointwise_iff {α : Type*} {l : Filter α}
    (F : α → QHilbert) (x : QHilbert) :
    (∀ k : ℕ, 0 < k → Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k))) ↔
      ∀ n, Tendsto (fun i => F i n) l (𝓝 (x n)) := by
  constructor
  · intro h n
    have hn : Real.sqrt (qWeight n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    have ht := (h (n + 1) (by omega)).mul_const (Real.sqrt (qWeight n))
    simpa only [qSequence_succ, div_mul_cancel₀ _ hn] using ht
  · intro h k hk
    have ht := (h (k - 1)).div_const (Real.sqrt (qWeight (k - 1)))
    have he : k - 1 + 1 = k := by omega
    simpa only [← qSequence_succ, he] using ht

/-- Actual physical-coordinate criterion in the Pareto law. -/
theorem pareto_tendsto_iff_pointwise_tight {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert) (x : ThresholdHilbert) :
    Tendsto F l (𝓝 x) ↔
      (∀ k : ℕ, 0 < k →
        Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 (hilbertSequence x k))) ∧
      EnergyTight F l :=
  (tendsto_iff_coordinates_tight F x).trans
    (and_congr (pareto_physical_pointwise_iff F x).symm Iff.rfl)

/-- Actual physical-coordinate criterion in the Q law, using its own tail energies. -/
theorem q_tendsto_iff_pointwise_tight {α : Type*} {l : Filter α}
    (F : α → QHilbert) (x : QHilbert) :
    Tendsto F l (𝓝 x) ↔
      (∀ k : ℕ, 0 < k →
        Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k))) ∧ EnergyTight F l :=
  (tendsto_iff_coordinates_tight F x).trans
    (and_congr (q_physical_pointwise_iff F x).symm Iff.rfl)

/-- For a given physically pointwise-convergent family, the two actual tail tests agree. -/
theorem tightness_pareto_iff_q_of_pointwise {α : Type*} {l : Filter α}
    (F : α → QHilbert) (x : QHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (F i) k) l (𝓝 (qSequence x k))) :
    EnergyTight (fun i => toPareto (F i)) l ↔ EnergyTight F l := by
  have hp := pareto_tendsto_iff_pointwise_tight (l := l) (fun i => toPareto (F i)) (toPareto x)
  have hq := q_tendsto_iff_pointwise_tight (l := l) F x
  have hpointP : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (toPareto (F i)) k) l
        (𝓝 (hilbertSequence (toPareto x) k)) := by
    simpa only [toPareto_sequence] using hpoint
  constructor
  · intro h
    exact (hq.mp ((tendsto_toPareto_iff F x).mp (hp.mpr ⟨hpointP, h⟩))).2
  · intro h
    exact (hp.mp ((tendsto_toPareto_iff F x).mpr (hq.mpr ⟨hpoint, h⟩))).2

end RiemannResearch.RH.RamanujanTailTightness

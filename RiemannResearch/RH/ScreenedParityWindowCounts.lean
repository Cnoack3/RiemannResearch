import RiemannResearch.RH.ScreenedParityPhysicalBounds
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Finset.Filter

/-! # Strict excursion counts of finite and limiting screened parity packets

For a fixed finite set of physical sites, every strict excursion of the limiting
packet eventually persists under finite mixed screening. Conversely an upper
count at the limit transfers eventually to finite screening after an arbitrary
strict decrease of the threshold. These implications retain the order of the
physical-window and conductor-cutoff quantifiers.

Source: the user-supplied Pareto quadratic-window handoff, finite sign transfer.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

private theorem eventually_all_sites {P : ℕ → ℕ → Prop} (S : Finset ℕ)
    (h : ∀ n ∈ S, ∀ᶠ L : ℕ in atTop, P L n) :
    ∀ᶠ L : ℕ in atTop, ∀ n ∈ S, P L n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih =>
    have hS := ih (fun n hn => h n (Finset.mem_insert_of_mem hn))
    filter_upwards [h k (Finset.mem_insert_self k S), hS] with L hL hSL
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact hL
    · exact hSL n hn

private theorem trial_site_tendsto (n : ℕ) :
    Tendsto (fun L => hilbertSequence (fixedTwoTrial L) n) atTop
      (𝓝 (hilbertSequence normalizedScreenedTwo n)) := by
  simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
    (anchoredEvaluationCLM n).continuous.continuousAt.tendsto.comp fixedTwoTrial_tendsto

/-- At a fixed threshold all strict negative excursions of the limit eventually
occur together at every sufficiently large finite mixed cutoff. -/
theorem screenedTwo_excursions_eventually_subset (S : Finset ℕ) (t : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      S.filter (fun n => hilbertSequence normalizedScreenedTwo n < t) ⊆
        S.filter (fun n => hilbertSequence (fixedTwoTrial L) n < t) := by
  classical
  let B := S.filter (fun n => hilbertSequence normalizedScreenedTwo n < t)
  have h := eventually_all_sites (P := fun L n => hilbertSequence (fixedTwoTrial L) n < t) B
    (fun n hn => (trial_site_tendsto n).eventually_lt_const (Finset.mem_filter.mp hn).2)
  filter_upwards [h] with L hL n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hL n hn⟩

/-- Cofinal finite counts at the original strict threshold bound the actual
packet on the same sites, with no convergence rate or change of threshold. -/
theorem screenedTwo_excursion_count_le_of_frequently (S : Finset ℕ) (t : ℝ) (B : ℕ)
    (h : ∃ᶠ L : ℕ in atTop,
      (S.filter (fun n => hilbertSequence (fixedTwoTrial L) n < t)).card ≤ B) :
    (S.filter (fun n => hilbertSequence normalizedScreenedTwo n < t)).card ≤ B := by
  obtain ⟨L, hL, hs⟩ := (h.and_eventually (screenedTwo_excursions_eventually_subset S t)).exists
  exact (Finset.card_le_card hs).trans hL

/-- Exact count criterion in finite data. The slack handles a limiting site
equal to the threshold, where a finite packet may approach from below. -/
theorem screenedTwo_excursion_count_le_iff_finite (S : Finset ℕ) (t : ℝ) (B : ℕ) :
    (S.filter (fun n => hilbertSequence normalizedScreenedTwo n < t)).card ≤ B ↔
      ∀ r : ℝ, r < t → ∃ᶠ L : ℕ in atTop,
        (S.filter (fun n => hilbertSequence (fixedTwoTrial L) n < r)).card ≤ B := by
  classical
  constructor
  · intro h r hr
    have hstay := eventually_all_sites
      (P := fun L n => t ≤ hilbertSequence normalizedScreenedTwo n →
        r < hilbertSequence (fixedTwoTrial L) n) S (by
        intro n _
        by_cases hn : t ≤ hilbertSequence normalizedScreenedTwo n
        · filter_upwards [(trial_site_tendsto n).eventually_const_lt (hr.trans_le hn)] with L hL
          exact fun _ => hL
        · exact Filter.Eventually.of_forall (fun _ h' => (hn h').elim))
    apply Filter.Eventually.frequently
    filter_upwards [hstay] with L hL
    refine (Finset.card_le_card ?_).trans h
    intro n hn
    obtain ⟨hnS, hnL⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnS, lt_of_not_ge (fun hx => (hL n hnS hx).not_gt hnL)⟩
  · intro h
    let D := S.filter (fun n => hilbertSequence normalizedScreenedTwo n < t)
    by_cases hD : D.Nonempty
    · let vals := D.image (fun n => hilbertSequence normalizedScreenedTwo n)
      have hv : vals.Nonempty := hD.image _
      let a := vals.max' hv
      have ha : a ∈ vals := Finset.max'_mem _ _
      obtain ⟨k, hk, hka⟩ := Finset.mem_image.mp ha
      have hat : a < t := hka ▸ (Finset.mem_filter.mp hk).2
      obtain ⟨r, har, hrt⟩ := exists_between hat
      have hs : D ⊆ S.filter (fun n => hilbertSequence normalizedScreenedTwo n < r) := by
        intro n hn
        have hval : hilbertSequence normalizedScreenedTwo n ∈ vals := Finset.mem_image_of_mem _ hn
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
          (Finset.le_max' _ _ hval).trans_lt har⟩
      exact (Finset.card_le_card hs).trans
        (screenedTwo_excursion_count_le_of_frequently S r B (h r hrt))
    · change D.card ≤ B
      simp [Finset.not_nonempty_iff_eq_empty.mp hD]

end RiemannResearch.RH.Pareto.PrimePowerSchur

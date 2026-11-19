import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.MontgomeryPositiveGapDensity
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Ordinate-fibre sampling, positive gaps and horizontal multiplicities

Goldston, Lee, Schettler and Suriajaya, *Pair correlation conjecture for the
zeros of the Riemann zeta-function I*, https://doi.org/10.1112/mtk.70127,
relate strictly positive vertical gaps, simplicity and critical-line density.
Here the multiplicities of actual ordinates determine the finite sampling
correction. A separate unnormalised vacancy test detects horizontal reflection
pairs even at a fixed height.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ZeroDPPCorrelation
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryFormFactor MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- Positive gaps of the sampled ordinates with both multiplicities restored. -/
def sampledPositiveGapMass (x : Site → Bool) (T u : ℝ) : ℝ :=
  (∑ c : Copies T, if x (liftCopy T c) = true then
    (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) *
    (∑ d : Copies T, if x (liftCopy T d) = true then
      (actualOrdinateMultiplicity T (copyOrdinate T d) : ℝ) *
      (let gap := Real.log T / (2 * Real.pi) * (copyOrdinate T d - copyOrdinate T c)
       if 0 < gap ∧ gap ≤ u then (1 : ℝ) else 0) else 0) else 0) /
    (T * Real.log T / (2 * Real.pi))

theorem sampledPositiveGapMass_eq_ae (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ T u : ℝ, sampledPositiveGapMass x T u = positiveGapMass T u := by
  filter_upwards [all_ordinate_pair_sums_ae q b hb hbπ hq] with x hx
  intro T u
  let w := fun a c : ℝ =>
    if 0 < Real.log T / (2 * Real.pi) * (c - a) ∧ Real.log T / (2 * Real.pi) * (c - a) ≤ u then (1 : ℝ) else 0
  exact congrArg (fun z : ℝ => z / (T * Real.log T / (2 * Real.pi))) (hx T w)

/-- Montgomery's ordinary positive-gap conjecture is equivalent to the
almost-sure microscopic limit of the multiplicity-weighted sampled process. -/
theorem positiveGapPCC_iff_sampled (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    PositiveGapPCC ↔ ∀ᵐ x ∂limitingLaw q, ∀ a b : ℝ, 0 < a → a ≤ b → ∀ η : ℝ, 0 < η →
      ∀ᶠ T : ℝ in atTop, ∀ u ∈ Set.Icc a b, |sampledPositiveGapMass x T u - sineGapMass u| ≤ η := by
  have he := sampledPositiveGapMass_eq_ae q b hb hbπ hq
  constructor
  · intro h
    filter_upwards [he] with x hx
    simpa only [hx, PositiveGapPCC] using h
  · intro h
    obtain ⟨x, hx, hP⟩ := (he.and h).exists
    simpa only [hx, PositiveGapPCC] using hP

/-- Collision exclusion and equal projections charge at least half a vacancy
to each copy in a repeated ordinate, for any frequency sequence. -/
theorem limitingKernel_le_half_of_collision (q : ℕ → ℝ) {i j : Site}
    (hne : i ≠ j) (hord : ordinate i = ordinate j) : limitingKernel q i i ≤ 1 / 2 := by
  have he : limitingKernel q i i = limitingKernel q j j := by
    simp only [limitingKernel, kernelOfSpace, ProjectionDPP.kernel, collision_projection_eq q hord]
  linarith [collision_vacancy_lower q hne hord]

/-- Expected missing labels among the off-critical copies only. -/
def offCriticalVacancy (q : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∑ c ∈ offCopies T, (1 - limitingKernel q (liftCopy T c) (liftCopy T c))

theorem offCount_le_twice_vacancy (q : ℕ → ℝ) (T : ℝ) :
    (offCount T : ℝ) ≤ 2 * offCriticalVacancy q T := by
  classical
  calc
    (offCount T : ℝ) = ∑ _c ∈ offCopies T, (1 : ℝ) := by simp [offCount]
    _ ≤ ∑ c ∈ offCopies T, 2 * (1 - limitingKernel q (liftCopy T c) (liftCopy T c)) := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨d, hne, hord⟩ := offCopies_has_companion T c hc
      have h := limitingKernel_le_half_of_collision q ((liftCopy T).injective.ne hne)
        (show ordinate (liftCopy T c) = ordinate (liftCopy T d) from hord)
      linarith
    _ = _ := by rw [offCriticalVacancy, Finset.mul_sum]

private theorem two_le_offCount_of_offline (T : ℝ) (ρ : ℂ) (hρ : ρ ∈ cutoff T)
    (hoff : ρ.re ≠ 1 / 2) : 2 ≤ offCount T := by
  classical
  let c : Copies T := ⟨⟨ρ, hρ⟩,⟨0, multiplicity_pos hρ⟩⟩
  let d : Copies T := ⟨⟨reflect ρ, reflect_mem hρ⟩,⟨0, multiplicity_pos (reflect_mem hρ)⟩⟩
  have hc : c ∈ offCopies T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoff⟩
  have hd : d ∈ offCopies T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change (reflect ρ).re ≠ 1 / 2
    rw [reflect_re]
    intro he
    exact hoff (by linarith)⟩
  have hne : c ≠ d := by
    intro he
    have hh := congrArg (fun a : Copies T => a.1.1.re) he
    change ρ.re = (reflect ρ).re at hh
    rw [reflect_re] at hh
    exact hoff (by linarith)
  have hs : ({c, d} : Finset (Copies T)) ⊆ offCopies T := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  simpa [offCount, hne] using Finset.card_le_card hs

/-- The absolute threshold one detects every off-line reflected pair. The
criterion permits arbitrary multiplicities on the critical line. -/
theorem offCriticalVacancy_lt_one_iff (q : ℕ → ℝ) (T : ℝ) :
    offCriticalVacancy q T < 1 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    by_contra hoff
    have htwo : (2 : ℝ) ≤ offCount T := by exact_mod_cast two_le_offCount_of_offline T ρ hρ hoff
    linarith [offCount_le_twice_vacancy q T]
  · intro h
    have he : offCopies T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      exact (Finset.mem_filter.mp hc).2 (h c.1.1 c.1.2)
    simp [offCriticalVacancy, he]

/-- RH is equivalent to the cofinal unnormalised off-critical vacancy
certificate, for any fixed dictionary. The estimate on that vacancy is open. -/
theorem riemannHypothesis_iff_cofinal_offCriticalVacancy (q : ℕ → ℝ) :
    RiemannHypothesis ↔ ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ offCriticalVacancy q T < 1 := by
  have hiff := cofinal_fejer_critical_line_iff_RH.symm.trans cofinal_fejer_critical_line_iff
  constructor
  · intro h H
    exact ⟨H, le_rfl, (offCriticalVacancy_lt_one_iff q H).mpr (hiff.mp h H)⟩
  · intro h
    apply hiff.mpr
    intro H ρ hρ
    obtain ⟨T, hHT, hv⟩ := h H
    obtain ⟨hz, hpos, ht⟩ := mem_cutoff.mp hρ
    exact (offCriticalVacancy_lt_one_iff q T).mp hv ρ (mem_cutoff.mpr ⟨hz, hpos, ht.trans hHT⟩)

/-- The number of exceptional copies is at most twice the total expected
number of deleted labels, independently of the Fourier dictionary. -/
theorem nonsimpleCritical_count_le_twice_cutoffVacancy (q : ℕ → ℝ) (T : ℝ) :
    (Ncount 0 T : ℝ) - simpleCriticalCount T ≤ 2 * cutoffVacancy q T := by
  classical
  let B := (Finset.univ : Finset (Copies T)) \ simpleCriticalCopies T
  have hcard : B.card + simpleCriticalCount T = Ncount 0 T := by
    rw [← card_copies, ← Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hcard' : (B.card : ℝ) + simpleCriticalCount T = Ncount 0 T := by exact_mod_cast hcard
  let loss := fun c : Copies T => 1 - limitingKernel q (liftCopy T c) (liftCopy T c)
  have hpos (c : Copies T) : 0 ≤ loss c :=
    sub_nonneg.mpr ((limitingLaw_isDPP q).diagonal_bounds (liftCopy T c)).2
  calc
    _ = ∑ _c ∈ B, (1 : ℝ) := by simp; linarith
    _ ≤ ∑ c ∈ B, 2 * loss c := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨d, hne, hord⟩ :=
        exceptional_has_companion T c (Finset.mem_sdiff.mp hc).2
      have h := limitingKernel_le_half_of_collision q ((liftCopy T).injective.ne hne)
        (show ordinate (liftCopy T c) = ordinate (liftCopy T d) from hord)
      dsimp only [loss]
      linarith
    _ ≤ ∑ c : Copies T, 2 * loss c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => by
        exact mul_nonneg (by norm_num) (hpos c))
    _ = _ := by rw [cutoffVacancy, Finset.mul_sum]

private theorem simpleCriticalCount_le_support (T : ℝ) :
    simpleCriticalCount T ≤ (actualOrdinateSupport T).card := by
  classical
  have hinj : Set.InjOn (copyOrdinate T) (simpleCriticalCopies T : Set (Copies T)) := by
    rintro ⟨ρ, a⟩ ha ⟨σ, b⟩ hb hab
    have hr := (Finset.mem_filter.mp ha).2
    have hs := (Finset.mem_filter.mp hb).2
    have hρσ : ρ = σ := by
      apply Subtype.ext
      exact Complex.ext (hr.1.trans hs.1.symm) hab
    subst σ
    have hm : zeroMult ρ.1 = 1 := hr.2
    have hi : a = b := by
      apply Fin.ext
      have ha' := a.isLt
      have hb' := b.isLt
      omega
    subst b
    rfl
  have hle : (simpleCriticalCopies T).image (copyOrdinate T) ⊆ actualOrdinateSupport T :=
    Finset.image_subset_image (Finset.subset_univ _)
  rw [simpleCriticalCount, ← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hle

/-- For the logarithmic dictionary, the vacancy and the exceptional copy
count agree within a factor two at every cutoff. -/
theorem logarithmic_cutoffVacancy_sandwich (T : ℝ) :
    cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T ≤ (Ncount 0 T : ℝ) - simpleCriticalCount T ∧
      (Ncount 0 T : ℝ) - simpleCriticalCount T ≤
        2 * cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T := by
  refine ⟨?_, nonsimpleCritical_count_le_twice_cutoffVacancy _ T⟩
  rw [logarithmic_cutoff_vacancy]
  exact sub_le_sub_left (by exact_mod_cast simpleCriticalCount_le_support T) _

/-- Vanishing relative vacancy is equivalent to density one of simple
critical zeros for this law. It requires no sine-kernel or moment assumption. -/
theorem logarithmic_relativeVacancy_tendsto_zero_iff :
    Tendsto (fun T : ℝ => cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T / (Ncount 0 T : ℝ))
      atTop (𝓝 0) ↔
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  let q := fun k : ℕ => Real.log ((k : ℝ) + 1)
  have hN : ∀ᶠ T : ℝ in atTop, 0 < (Ncount 0 T : ℝ) := by
    filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with T ht
    by_contra hn
    have he : (Ncount 0 T : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    simp [he] at ht
  have hD (T : ℝ) : 0 ≤ cutoffVacancy q T := Finset.sum_nonneg (fun c _ =>
    sub_nonneg.mpr ((limitingLaw_isDPP q).diagonal_bounds (liftCopy T c)).2)
  have hs : ∀ᶠ T : ℝ in atTop,
      cutoffVacancy q T / (Ncount 0 T : ℝ) ≤ 1 - simpleCriticalCount T / (Ncount 0 T : ℝ) ∧
      1 - simpleCriticalCount T / (Ncount 0 T : ℝ) ≤ 2 * (cutoffVacancy q T / (Ncount 0 T : ℝ)) := by
    filter_upwards [hN] with T ht
    have hh := logarithmic_cutoffVacancy_sandwich T
    have hl := div_le_div_of_nonneg_right hh.1 ht.le
    have hu := div_le_div_of_nonneg_right hh.2 ht.le
    simpa only [sub_div, div_self ht.ne', mul_div_assoc] using And.intro hl hu
  constructor
  · intro h
    have hupper := h.const_mul (2 : ℝ)
    rw [mul_zero] at hupper
    have hcomp := tendsto_of_tendsto_of_tendsto_of_le_of_le' h hupper
      (hs.mono fun _ ht => ht.1) (hs.mono fun _ ht => ht.2)
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := hconst.sub hcomp
    simpa using hh
  · intro h
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hupper := hconst.sub h
    rw [sub_self] at hupper
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Filter.Eventually.of_forall (fun T => div_nonneg (hD T) (Nat.cast_nonneg _)))
      (hs.mono fun _ ht => ht.1)

/-- The established positive-gap and short-window hypotheses imply negligible
relative deletions of the full logarithmic zero-label process. -/
theorem logarithmic_relativeVacancy_of_positiveGapPCC (h : PositiveGapPCC)
    (hm : ShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T / (Ncount 0 T : ℝ))
      atTop (𝓝 0) :=
  logarithmic_relativeVacancy_tendsto_zero_iff.mpr (density_one_of_positiveGapPCC h hm).1

end RiemannResearch.Analysis.ZeroDPPCorrelation

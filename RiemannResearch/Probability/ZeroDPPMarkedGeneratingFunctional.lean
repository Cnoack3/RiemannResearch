import RiemannResearch.Probability.ZeroOrdinatePrimeDPP
import RiemannResearch.Probability.ZeroOrdinateQuotientDPP
import RiemannResearch.Analysis.ZeroDPPHorizontalAnticoncentration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite generating functionals of marked actual zero ordinates

For a saturated frequency dictionary the generating functional of arbitrary
real or complex marks factors into one arithmetic mean per distinct ordinate.
Choosing Boolean marks gives exact joint hit or avoidance probabilities for
arbitrary subsets of the ordinate fibres. In particular the probability of
selecting only critical-line representatives is a product of critical-line
fractions. An absolute detection criterion also applies to incomplete, moving
frequency dictionaries.
-/

noncomputable section
open MeasureTheory Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate

/-- Selected real or complex mark in one finite ordinate fibre. -/
def fiberMark {𝕜 : Type*} [RCLike 𝕜] (τ : OrdinateSite) (w : ↥(ordinateLabels τ) → 𝕜)
    (x : Site → Bool) : 𝕜 :=
  ∑ i : ↥(ordinateLabels τ), if x i.val = true then w i else 0

private theorem representative_tuple_mass (q : ℕ → ℝ)
    (hlaw : limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1)))
    {m : ℕ} (e : Fin m ↪ OrdinateSite) (u : (k : Fin m) → ↥(ordinateLabels (e k))) :
    (limitingLaw q).real {x | ∀ k, x (u k).val = true} =
      ∏ k, ((ordinateLabels (e k)).card : ℝ)⁻¹ := by
  rw [hlaw]
  have he : Function.Injective (fun k => ordinate (u k).val) := by
    intro i j h
    apply e.injective
    exact Subtype.ext ((mem_ordinateLabels.mp (u i).property).symm.trans
      (h.trans (mem_ordinateLabels.mp (u j).property)))
  let f : Fin m ↪ Site := ⟨fun k => (u k).val, fun i j h => he (congrArg ordinate h)⟩
  have hπ : Real.log 2 ≤ 2 * Real.pi := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2), Real.pi_gt_three]
  have hp := inclusion_of_distinct_ordinates _ (Real.log 2) (Real.log_pos (by norm_num)) hπ
    logarithmic_containsHarmonics m f he
  have hf (k : Fin m) : ordinateFiber (f k) = ordinateLabels (e k) := by
    ext j
    simp only [mem_ordinateFiber, mem_ordinateLabels]
    rw [show ordinate (f k) = (e k).val from mem_ordinateLabels.mp (u k).property]
  simp only [hf] at hp
  have hfk (k : Fin m) : f k = (u k).val := rfl
  simpa only [hfk] using hp

/-- Exact mixed generating functional for arbitrary real or complex marks
of finitely many different actual ordinates. -/
theorem expected_product_fiberMarks {𝕜 : Type*} [RCLike 𝕜] (q : ℕ → ℝ)
    (hlaw : limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1)))
    {m : ℕ} (e : Fin m ↪ OrdinateSite) (w : (k : Fin m) → ↥(ordinateLabels (e k)) → 𝕜) :
    (∫ x, ∏ k, fiberMark (e k) (w k) x ∂limitingLaw q) =
      ∏ k, (algebraMap ℝ 𝕜 (((ordinateLabels (e k)).card : ℝ)⁻¹)) * ∑ i, w k i := by
  classical
  let μ := limitingLaw q
  let A := (k : Fin m) → ↥(ordinateLabels (e k))
  let E := fun u : A => {x : Site → Bool | ∀ k, x (u k).val = true}
  let v := fun u : A => ∏ k, w k (u k)
  let p := fun k : Fin m => ((ordinateLabels (e k)).card : ℝ)⁻¹
  have hm (u : A) : MeasurableSet (E u) := by
    simp only [E, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun k => (limitingLaw_isDPP q).measurable_occupancy (u k).val)
  have he (x : Site → Bool) : (∏ k, fiberMark (e k) (w k) x) =
      ∑ u : A, (E u).indicator (fun _ => v u) x := by
    unfold fiberMark
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hx : x ∈ E u
    · rw [Set.indicator_of_mem hx]
      have hall : ∀ k, x (u k).val = true := hx
      simp only [hall, if_true, v]
    · rw [Set.indicator_of_notMem hx]
      change ¬(∀ k, x (u k).val = true) at hx
      obtain ⟨k, hk⟩ := not_forall.mp hx
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
  have hterm (u : A) : μ.real (E u) • v u =
      ∏ k, algebraMap ℝ 𝕜 (p k) * w k (u k) := by
    have hp : μ.real (E u) = ∏ k, p k := representative_tuple_mass q hlaw e u
    simp only [hp, Algebra.smul_def, map_prod, v, Finset.prod_mul_distrib]
  have hInt (u : A) : (∫ x, (E u).indicator (fun _ => v u) x ∂limitingLaw q) =
      ∏ k, algebraMap ℝ 𝕜 (p k) * w k (u k) := by
    calc
      _ = μ.real (E u) • v u := integral_indicator_const (v u) (hm u)
      _ = _ := hterm u
  simp_rw [he]
  rw [integral_finsetSum _ (fun u _ => (integrable_const (v u)).indicator (hm u))]
  simp_rw [hInt]
  have hd := Fintype.prod_sum (κ := fun k : Fin m => ↥(ordinateLabels (e k)))
    (fun k j => algebraMap ℝ 𝕜 (p k) * w k j)
  calc
    _ = ∏ k, ∑ j : ↥(ordinateLabels (e k)), algebraMap ℝ 𝕜 (p k) * w k j := hd.symm
    _ = _ := by simp only [p, Finset.mul_sum]

/-- Explicit finite-dimensional generating functional of the pure-prime zero DPP. -/
theorem prime_expected_product_fiberMarks {𝕜 : Type*} [RCLike 𝕜] {m : ℕ}
    (e : Fin m ↪ OrdinateSite) (w : (k : Fin m) → ↥(ordinateLabels (e k)) → 𝕜) :
    (∫ x, ∏ k, fiberMark (e k) (w k) x ∂limitingLaw primeFrequencies) =
      ∏ k, (algebraMap ℝ 𝕜 (((ordinateLabels (e k)).card : ℝ)⁻¹)) * ∑ i, w k i :=
  expected_product_fiberMarks _ primeFrequencies_limitingLaw e w

set_option maxHeartbeats 800000 in
/-- Simultaneous allowed-representative probability for any finite choice
of distinct ordinates and any specified subsets of their labels. -/
theorem allowed_representatives_probability (q : ℕ → ℝ)
    (hlaw : limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1))) {m : ℕ}
    (e : Fin m ↪ OrdinateSite) (G : (k : Fin m) → Finset ↥(ordinateLabels (e k))) :
    (limitingLaw q).real {x | ∀ k, ∃ j ∈ G k, x j.val = true} =
      ∏ k, ((G k).card : ℝ) / (ordinateLabels (e k)).card := by
  classical
  let E := {x : Site → Bool | ∀ k, ∃ j ∈ G k, x j.val = true}
  let w := fun (k : Fin m) (j : ↥(ordinateLabels (e k))) => if j ∈ G k then (1 : ℝ) else 0
  have hm : MeasurableSet E := by
    have hE : E = ⋂ k : Fin m, ⋃ j : ↥(ordinateLabels (e k)),
        {x : Site → Bool | j ∈ G k} ∩ {x | x j.val = true} := by
      ext x
      simp [E]
    rw [hE]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iUnion (fun j =>
      (MeasurableSet.const _).inter ((limitingLaw_isDPP q).measurable_occupancy j.val)))
  have he : (fun x => ∏ k, fiberMark (e k) (w k) x) =ᵐ[limitingLaw q]
      E.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ordinate_injective_ae q] with x hx
    have hf (k : Fin m) : fiberMark (e k) (w k) x =
        if ∃ j ∈ G k, x j.val = true then (1 : ℝ) else 0 := by
      by_cases h : ∃ j ∈ G k, x j.val = true
      · obtain ⟨j, hj, hs⟩ := h
        rw [if_pos ⟨j, hj, hs⟩, fiberMark, Finset.sum_eq_single j]
        · simp [w, hs, hj]
        · intro i _ hij
          have hi : x i.val ≠ true := by
            intro hi
            exact hij (Subtype.ext (hx hi hs ((mem_ordinateLabels.mp i.property).trans
              (mem_ordinateLabels.mp j.property).symm)))
          simp [hi]
        · simp
      · rw [if_neg h, fiberMark]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : x j.val = true
        · have hnot : j ∉ G k := fun hG => h ⟨j, hG, hj⟩
          simp [w, hj, hnot]
        · simp [hj]
    by_cases hall : x ∈ E
    · rw [Set.indicator_of_mem hall]
      have hk : ∀ k, ∃ j ∈ G k, x j.val = true := hall
      simp [hf, hk]
    · rw [Set.indicator_of_notMem hall]
      change ¬(∀ k, ∃ j ∈ G k, x j.val = true) at hall
      obtain ⟨k, hk⟩ := not_forall.mp hall
      exact Finset.prod_eq_zero (Finset.mem_univ k) ((hf k).trans (if_neg hk))
  have h := expected_product_fiberMarks q hlaw e w
  rw [integral_congr_ae he, integral_indicator_const (1 : ℝ) hm, smul_eq_mul, mul_one] at h
  have hs (k : Fin m) : (∑ j, w k j) = ((G k).card : ℝ) := by
    have hfilter : Finset.univ.filter (fun j => j ∈ G k) = G k := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [w, Finset.sum_boole, hfilter]
  change (limitingLaw q).real E = _
  refine h.trans (Finset.prod_congr rfl ?_)
  intro k _
  change ((ordinateLabels (e k)).card : ℝ)⁻¹ * (∑ j, w k j) = _
  rw [hs, div_eq_mul_inv, mul_comm]

/-- Probability that every represented ordinate in a finite list selects
a critical-line zero, including its analytic multiplicity in the count. -/
theorem critical_representatives_probability (q : ℕ → ℝ)
    (hlaw : limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1))) {m : ℕ}
    (e : Fin m ↪ OrdinateSite) :
    (limitingLaw q).real {x | ∀ k, ∃ j : ↥(ordinateLabels (e k)),
      j.val.1.1.re = 1 / 2 ∧ x j.val = true} =
      ∏ k, ((Finset.univ.filter (fun j : ↥(ordinateLabels (e k)) =>
        j.val.1.1.re = 1 / 2)).card : ℝ) / (ordinateLabels (e k)).card := by
  classical
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    allowed_representatives_probability q hlaw e
      (fun k => Finset.univ.filter (fun j : ↥(ordinateLabels (e k)) => j.val.1.1.re = 1 / 2))

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

namespace RiemannResearch.Analysis.ZeroDPPHorizontal
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryFormFactor
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- The sampled configuration detects an off-critical zero up to T. -/
def offCriticalHit (T : ℝ) : Set (Site → Bool) :=
  {x | ∃ c : Copies T, c.1.1.re ≠ 1 / 2 ∧ x (liftCopy T c) = true}

/-- Every actual off-line zero gives a common positive chance of detection
at every higher cutoff, uniformly in the frequency dictionary. -/
theorem persistent_offCriticalHit {H : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff H) (hoff : ρ.re ≠ 1 / 2) :
    ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ, ρ.im ≤ T → ∀ q : ℕ → ℝ,
      p ≤ (limitingLaw q).real (offCriticalHit T) := by
  obtain ⟨p, hp, htail⟩ := persistent_tail_of_offline hρ hoff
  refine ⟨p, hp, fun T hT q => (htail T hT q 0).trans (measureReal_mono ?_)⟩
  intro x hx
  by_contra hn
  have he : horizontalStatistic q T (fun _ => 1) x = 0 := by
    unfold horizontalStatistic normalizedMark linearStatistic
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : c.1.1.re = 1 / 2
    · simp [hc]
    · have hnot : x (liftCopy T c) ≠ true := fun h => hn ⟨c, hc, h⟩
      simp [occupancyIndicator, hnot]
  change |ρ.re - 1 / 2| ≤ |horizontalStatistic q T (fun _ => 1) x - 0| at hx
  rw [he, sub_zero, abs_zero] at hx
  exact (not_le_of_gt (abs_pos.mpr (sub_ne_zero.mpr hoff))) hx

/-- RH is equivalent to arbitrarily small probabilities of detecting
any off-line label at arbitrarily high cutoffs, for every moving dictionary. -/
theorem riemannHypothesis_iff_cofinal_hit_small (q : ℝ → ℕ → ℝ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      (limitingLaw (q T)).real (offCriticalHit T) < ε := by
  have hcrit := cofinal_fejer_critical_line_iff_RH.symm.trans cofinal_fejer_critical_line_iff
  constructor
  · intro h ε hε H
    refine ⟨H, le_rfl, ?_⟩
    have he : offCriticalHit H = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨c, hc, _⟩
      exact hc ((hcrit.mp h) H c.1.1 c.1.2)
    simpa only [he, measureReal_empty] using hε
  · intro h
    apply hcrit.mpr
    intro H ρ hρ
    by_contra hoff
    obtain ⟨p, hp, hdet⟩ := persistent_offCriticalHit hρ hoff
    obtain ⟨T, hT, hlt⟩ := h p hp ρ.im
    exact (not_lt_of_ge (hdet T hT (q T))) hlt

end RiemannResearch.Analysis.ZeroDPPHorizontal

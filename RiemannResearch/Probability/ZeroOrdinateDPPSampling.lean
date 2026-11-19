import RiemannResearch.Probability.ZeroOrdinateFiberDPP
import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalPairTransfer
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Sampling actual zero labels by ordinate

The uniform fibre kernel yields exact finite inverse-inclusion identities,
as in Horvitz and Thompson (1952), https://doi.org/10.1080/01621459.1952.10483446.
For tests depending only on ordinates a stronger calculation holds for every
configuration choosing one label per fibre, before taking expectations.
The zero-gap part stays explicit when a test includes it.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate ActualZeroCollisionCertificate
open OrdinateCollisionCertificate

/-- A global label below the cutoff comes from an actual finite-height copy. -/
theorem liftCopy_surj_below (T : ℝ) (i : Site) (hi : ordinate i ≤ T) :
    ∃ c : Copies T, liftCopy T c = i := by
  exact ⟨⟨⟨i.1.1, mem_cutoff_iff_zeta.mpr ⟨i.1.property.1, i.1.property.2, hi⟩⟩, i.2⟩, rfl⟩

/-- No label in a cutoff has an equal-ordinate companion outside that cutoff. -/
theorem ordinateFiber_liftCopy (T : ℝ) (c : Copies T) :
    ordinateFiber (liftCopy T c) =
      (Finset.univ.filter (fun d : Copies T => copyOrdinate T d = copyOrdinate T c)).map
        (liftCopy T) := by
  ext i
  constructor
  · intro hi
    have hi' := mem_ordinateFiber.mp hi
    have hT := (mem_cutoff.mp c.1.property).2.2
    obtain ⟨d, rfl⟩ := liftCopy_surj_below T i (hi' ▸ hT)
    exact Finset.mem_map.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩, rfl⟩
  · intro hi
    obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hi
    exact mem_ordinateFiber.mpr (Finset.mem_filter.mp hd).2

theorem ordinateFiber_card_liftCopy (T : ℝ) (c : Copies T) :
    (ordinateFiber (liftCopy T c)).card = actualOrdinateMultiplicity T (copyOrdinate T c) := by
  rw [ordinateFiber_liftCopy, Finset.card_map]
  rfl

private theorem ordinateMultiplicity_pos_on_support (T τ : ℝ)
    (hτ : τ ∈ actualOrdinateSupport T) : 0 < actualOrdinateMultiplicity T τ := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hτ
  rw [← ordinateFiber_card_liftCopy]
  exact ordinateFiber_card_pos _

/-- Grouping a sum over copies by its ordinate retains the full multiplicity. -/
theorem sum_copies_by_ordinate (T : ℝ) (f : ℝ → ℝ) :
    (∑ c : Copies T, f (copyOrdinate T c)) =
      ∑ τ ∈ actualOrdinateSupport T, (actualOrdinateMultiplicity T τ : ℝ) * f τ := by
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Copies T)),
      copyOrdinate T c ∈ actualOrdinateSupport T :=
    fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have h := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Copies T)))
    (t := actualOrdinateSupport T) (g := copyOrdinate T) hmaps f
  simpa only [Finset.sum_const, nsmul_eq_mul, actualOrdinateMultiplicity, ordinateMultiplicity]
    using h.symm

/-- Sum of the coordinate vacancy probabilities at a finite height. -/
def cutoffVacancy (q : ℕ → ℝ) (T : ℝ) : ℝ :=
  ∑ c : Copies T, (1 - limitingKernel q (liftCopy T c) (liftCopy T c))

/-- Total expected deletions at height T equal the number of copies in excess
of one per distinct ordinate, for the log-integer dictionary. -/
theorem logarithmic_cutoff_vacancy (T : ℝ) :
    cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T =
      (Zeta23.Ncount 0 T : ℝ) - (actualOrdinateSupport T).card := by
  unfold cutoffVacancy
  simp only [logarithmic_limitingKernel, eq_self, if_true, ordinateFiber_card_liftCopy]
  rw [Finset.sum_sub_distrib,
    sum_copies_by_ordinate T (fun τ => (actualOrdinateMultiplicity T τ : ℝ)⁻¹)]
  have hsum : (∑ τ ∈ actualOrdinateSupport T, (actualOrdinateMultiplicity T τ : ℝ) *
      (actualOrdinateMultiplicity T τ : ℝ)⁻¹) = (actualOrdinateSupport T).card := by
    calc
      _ = ∑ _τ ∈ actualOrdinateSupport T, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro τ hτ
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
          (ordinateMultiplicity_pos_on_support T τ hτ).ne')
      _ = _ := by simp
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_copies]

/-- Signed off-fibre pair weights are recovered exactly in expectation by
inverse inclusion probabilities, even when the weights depend on the labels. -/
theorem expected_inverse_weighted_pair {ι : Type*} [Fintype ι]
    (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b)
    (e : ι ↪ Site) (w : ι → ι → ℝ)
    (hw : ∀ i j, ordinate (e i) = ordinate (e j) → w i j = 0) :
    (∫ x, pairStatistic (fun x : Site → Bool => {j | x j = true}) e
      (fun i j => ((ordinateFiber (e i)).card : ℝ) * (ordinateFiber (e j)).card * w i j) x
      ∂limitingLaw q) = pairMass w := by
  rw [(limitingLaw_isDPP q).expected_pairStatistic e _ (fun i => by simp [hw i i rfl])]
  unfold expectedPairMass pairMass
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : ordinate (e i) = ordinate (e j)
  · simp [hw i j he]
  · simp only [limitingKernel_of_harmonics q b hb hbπ hq, eq_self, if_true, if_neg he,
      if_neg (Ne.symm he), mul_zero, sub_zero]
    field_simp [Nat.cast_ne_zero.mpr (ordinateFiber_card_pos (e i)).ne',
      Nat.cast_ne_zero.mpr (ordinateFiber_card_pos (e j)).ne']

/-- For each realization taking one label per fibre, the reweighted sum of
any ordinate test agrees pointwise with the original multiplicity sum. -/
theorem sum_weighted_ordinate_of_transversal (x : Site → Bool)
    (hx : ∀ i : Site, ∃! j : Site, ordinate j = ordinate i ∧ x j = true)
    (T : ℝ) (f : ℝ → ℝ) :
    (∑ c : Copies T, if x (liftCopy T c) = true
      then (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) * f (copyOrdinate T c) else 0) =
      ∑ c : Copies T, f (copyOrdinate T c) := by
  let v := fun c : Copies T => if x (liftCopy T c) = true
    then (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) * f (copyOrdinate T c) else 0
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Copies T)),
      copyOrdinate T c ∈ actualOrdinateSupport T :=
    fun c hc => Finset.mem_image.mpr ⟨c, hc, rfl⟩
  rw [sum_copies_by_ordinate T f]
  change (∑ c, v c) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps v]
  apply Finset.sum_congr rfl
  intro τ hτ
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hτ
  obtain ⟨j, hj, honly⟩ := hx (liftCopy T c)
  obtain ⟨d, hd⟩ := liftCopy_surj_below T j (hj.1 ▸ (mem_cutoff.mp c.1.2).2.2)
  have hdord : copyOrdinate T d = copyOrdinate T c := by
    change ordinate (liftCopy T d) = ordinate (liftCopy T c)
    rw [hd, hj.1]
  rw [Finset.sum_eq_single d]
  · simp [v, hd, hj.2, hdord]
  · intro k hk hkd
    have hkord : ordinate (liftCopy T k) = ordinate (liftCopy T c) :=
      (Finset.mem_filter.mp hk).2
    have hnot : x (liftCopy T k) ≠ true := by
      intro hsel
      exact hkd ((liftCopy T).injective ((honly _ ⟨hkord, hsel⟩).trans hd.symm))
    simp [v, hnot]
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdord⟩)).elim

/-- Multiplicity weighting recovers every pair statistic of ordinates,
including its entire equal-ordinate contribution. This identity is simultaneous
in the height and the test on one probability-one event. -/
theorem all_ordinate_pair_sums_ae (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ (T : ℝ) (w : ℝ → ℝ → ℝ),
      (∑ c : Copies T, if x (liftCopy T c) = true then
        (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) *
        (∑ d : Copies T, if x (liftCopy T d) = true then
          (actualOrdinateMultiplicity T (copyOrdinate T d) : ℝ) *
            w (copyOrdinate T c) (copyOrdinate T d) else 0) else 0) =
        ∑ c : Copies T, ∑ d : Copies T, w (copyOrdinate T c) (copyOrdinate T d) := by
  filter_upwards [exactly_one_per_ordinate_ae q b hb hbπ hq] with x hx
  intro T w
  simp_rw [sum_weighted_ordinate_of_transversal x hx T (w _)]
  exact sum_weighted_ordinate_of_transversal x hx T
    (fun τ => ∑ d : Copies T, w τ (copyOrdinate T d))


/-- Forgetting the labels produces the sum over distinct actual ordinates.
The statement holds simultaneously for every cutoff and ordinate test. -/
theorem all_unweighted_ordinate_sums_ae (q : ℕ → ℝ) (b : ℝ)
    (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi) (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ (T : ℝ) (f : ℝ → ℝ),
      (∑ c : Copies T, if x (liftCopy T c) = true then f (copyOrdinate T c) else 0) =
        ∑ τ ∈ actualOrdinateSupport T, f τ := by
  filter_upwards [exactly_one_per_ordinate_ae q b hb hbπ hq] with x hx
  intro T f
  let g := fun τ => f τ / (actualOrdinateMultiplicity T τ : ℝ)
  have he := sum_weighted_ordinate_of_transversal x hx T g
  rw [sum_copies_by_ordinate] at he
  have hg (τ : ℝ) (hτ : τ ∈ actualOrdinateSupport T) :
      (actualOrdinateMultiplicity T τ : ℝ) * g τ = f τ := by
    dsimp [g]
    field_simp [Nat.cast_ne_zero.mpr (ordinateMultiplicity_pos_on_support T τ hτ).ne']
  calc
    _ = ∑ c : Copies T, if x (liftCopy T c) = true then
        (actualOrdinateMultiplicity T (copyOrdinate T c) : ℝ) * g (copyOrdinate T c) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hg _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩)]
    _ = _ := he.trans (Finset.sum_congr rfl (fun τ hτ => hg τ hτ))

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

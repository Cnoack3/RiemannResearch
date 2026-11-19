import RiemannResearch.Analysis.ZeroDPPProjectedDistinctSpacing
import RiemannResearch.Analysis.ZeroDPPTranslatedJensen
import RiemannResearch.Analysis.ActualZeroWindowVariance
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion

/-! Below the first ordinate, the corrected prime-DPP statistic is the translated
squared count of distinct heights plus the translated mean of the missing labels. -/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectedDistinctSpacing
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance OrdinateWindowVariance
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def distinctWindowCount (T h : ℝ) : ℝ → ℝ :=
  windowCount (actualOrdinateSupport T) id T h

private theorem nonneg_pulse (T h u t : ℝ) : 0 ≤ windowPulse T h u t := by
  unfold windowPulse pulse
  by_cases ht : t ∈ Ioc (max 0 (u-h)) (min T u) <;> simp [ht]

theorem distinctWindowCount_nonneg_le_actual (T h t : ℝ) :
    0 ≤ distinctWindowCount T h t ∧ distinctWindowCount T h t ≤ actualWindowCount T h t := by
  constructor
  · exact Finset.sum_nonneg fun u _ => nonneg_pulse T h u t
  · change (∑ u ∈ actualOrdinateSupport T, windowPulse T h u t) ≤
      ∑ i : Copies T, windowPulse T h (copyOrdinate T i) t
    rw [sum_copies_by_ordinate T (fun u => windowPulse T h u t)]
    apply Finset.sum_le_sum
    intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    have hm := ordinateFiber_card_pos (liftCopy T i)
    rw [ordinateFiber_card_liftCopy] at hm
    have hR : (1:ℝ) ≤ (actualOrdinateMultiplicity T (copyOrdinate T i):ℝ) := by exact_mod_cast hm
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hR (nonneg_pulse T h (copyOrdinate T i) t))

private theorem support_bounds (T h : ℝ) (hlo : ∀ i : Copies T, h ≤ copyOrdinate T i) :
    ∀ x ∈ actualOrdinateSupport T, h ≤ x ∧ x ≤ T := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨hlo i, (mem_cutoff.mp i.1.2).2.2⟩

/-- The disappearance of self-pairs in the distinct-point factorial count is
offset by returning every original occurrence diagonal. The extra term in the
physical moment is exactly the translated mean number of omitted labels. -/
theorem corrected_prime_physical_moment (T h : ℝ) (hh : 0 ≤ h)
    (hlo : ∀ i : Copies T, h ≤ copyOrdinate T i) :
    (Ncount 0 T : ℝ) * h +
      expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
        (fun i j => max (h - |copyOrdinate T i - copyOrdinate T j|) 0) =
    (∫ t, distinctWindowCount T h t ^ 2) +
      (∫ t, actualWindowCount T h t - distinctWindowCount T h t) := by
  classical
  let s := actualOrdinateSupport T
  let w := fun u v : ℝ => max (h - |u-v|) 0
  have hsup := support_bounds T h hlo
  have hz := integral_actualWindowCount T h hh hlo
  have hx : (∫ t, distinctWindowCount T h t) = (s.card:ℝ)*h :=
    integral_windowCount_of_supported s id T h hh hsup
  have hx2 : (∫ t, distinctWindowCount T h t ^ 2) = ∑ u ∈ s, ∑ v ∈ s, w u v :=
    integral_windowCount_sq_of_supported s id T h hsup
  have pair := prime_expectedPairMass_eq_distinct T w
  have split : ∑ u ∈ s, ∑ v ∈ s, w u v = (s.card:ℝ)*h + distinctPairTest T w := by
    unfold distinctPairTest
    change _ = _ + ∑ u ∈ s, ∑ v ∈ s, if u=v then 0 else w u v
    calc
      _ = ∑ u ∈ s, ∑ v ∈ s, ((if v=u then h else 0) + (if u=v then 0 else w u v)) := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        by_cases he : u=v
        · subst v; simp [w, max_eq_left hh]
        · simp [he, Ne.symm he]
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        congr 1
        calc
          _ = ∑ _u ∈ s, h := by
            apply Finset.sum_congr rfl
            intro u hu
            simp [hu]
          _ = _ := by simp
  change _ + expectedPairMass _ _ (fun i j => w (copyOrdinate T i) (copyOrdinate T j)) = _
  have hiZ : Integrable (actualWindowCount T h) := windowCount_integrable ..
  have hiX : Integrable (distinctWindowCount T h) := windowCount_integrable ..
  rw [pair, hx2, integral_sub hiZ hiX,
    hz, hx, split]
  ring
/-- Actual finite configurations at a supported positive height. The Jensen correction
uses precisely the fraction of omitted distinct labels in a translated window. -/
theorem actual_prime_physical_jensen {T h : ℝ} (hT : 0 < T) (hh : 0 ≤ h)
    (hlo : ∀ i : Copies T, h ≤ copyOrdinate T i) :
    let m := h * ((Ncount 0 T : ℝ) - (actualOrdinateSupport T).card) / T
    m^2 - m ≤ actualPhysicalTriangleEnergy T h -
      ((Ncount 0 T : ℝ) * h +
        expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
          (fun i j => max (h - |copyOrdinate T i - copyOrdinate T j|) 0)) / T := by
  dsimp only
  let m := h * ((Ncount 0 T : ℝ) - (actualOrdinateSupport T).card) / T
  have hmean : (∫ t, actualWindowCount T h t - distinctWindowCount T h t) = T*m := by
    have hiZ : Integrable (actualWindowCount T h) := windowCount_integrable ..
    have hiX : Integrable (distinctWindowCount T h) := windowCount_integrable ..
    rw [integral_sub hiZ hiX,
      integral_actualWindowCount T h hh hlo]
    have hx : (∫ t, distinctWindowCount T h t) = ((actualOrdinateSupport T).card:ℝ)*h :=
      integral_windowCount_of_supported _ id T h hh (support_bounds T h hlo)
    rw [hx]; dsimp [m]; field_simp <;> ring
  have hj := DPPLargeWidth.finite_window_restored_loss_ge
    (Finset.univ : Finset (Copies T)) (actualOrdinateSupport T) (copyOrdinate T) id hT.le
    (fun t => (distinctWindowCount_nonneg_le_actual T h t).2) hmean
  change T * (m^2-m) ≤ (∫ t, actualWindowCount T h t ^ 2) -
    ((∫ t, distinctWindowCount T h t ^ 2) +
     (∫ t, actualWindowCount T h t - distinctWindowCount T h t)) at hj
  rw [← corrected_prime_physical_moment T h hh hlo, integral_actualWindowCount_sq T h hlo] at hj
  unfold actualPhysicalTriangleEnergy
  rw [← sub_div]
  apply (le_div_iff₀ hT).2
  simpa only [mul_comm T (m^2-m)] using hj

end RiemannResearch.Analysis.ProjectedDistinctSpacing

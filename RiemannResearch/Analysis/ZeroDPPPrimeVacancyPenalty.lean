import RiemannResearch.Analysis.ZeroDPPDistinctWindowMoment
import RiemannResearch.Analysis.ZeroDPPProjectionBridge
import RiemannResearch.Analysis.ZeroDPPLargeWidth

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectedDistinctSpacing
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open MontgomeryPositiveGap ZeroDPPCorrelation ZeroDPPProjectionBridge ZeroDPPCollisionLoss
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

def primeMissingDensity (T : ℝ) : ℝ :=
  ((Ncount 0 T : ℝ) - (actualOrdinateSupport T).card) / (T*Real.log T/(2*Real.pi))

private def physicalWeight (T r u v : ℝ) : ℝ :=
  max (r/(Real.log T/(2*Real.pi)) - |u-v|) 0 / T

private theorem physical_integral {T a b : ℝ} (ht : 1 < T) (hab : a ≤ b) (u v : ℝ) :
    (∫ r in a..b, physicalWeight T r u v) = unfoldedProbe T a b u v := by
  let L := Real.log T/(2*Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos ht) (by positivity)
  have he (r : ℝ) : physicalWeight T r u v = max (r-|L*(u-v)|) 0 / (T*L) := by
    unfold physicalWeight
    change max (r/L-|u-v|) 0 / T = _
    rw [abs_mul, abs_of_pos hL, show r/L-|u-v| = (r-L*|u-v|)/L by field_simp]
    rcases le_total (r-L*|u-v|) 0 with ha | ha
    · rw [max_eq_right ha, max_eq_right (div_nonpos_of_nonpos_of_nonneg ha hL.le)]
      simp
    · rw [max_eq_left ha, max_eq_left (div_nonneg ha hL.le)]
      ring
  simp_rw [he]
  rw [intervalIntegral.integral_div]
  change integratedTriangle a b (L*(u-v)) / (T*L) = _
  rw [integratedTriangle_eq_widthProbe hab, unfoldedProbe]
  dsimp [L]; ring

private def physicalProjection (T r : ℝ) : ℝ :=
  (∑ i : Copies T, physicalWeight T r (copyOrdinate T i) (copyOrdinate T i)) +
    distinctPairTest T (physicalWeight T r)

private theorem weight_continuous (T u v : ℝ) : Continuous (fun r => physicalWeight T r u v) := by
  unfold physicalWeight; fun_prop

private theorem off_weight_continuous (T u v : ℝ) :
    Continuous (fun r => if u=v then 0 else physicalWeight T r u v) := by
  by_cases h : u = v
  · simpa only [h, ↓reduceIte] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · simpa only [h, if_false] using weight_continuous T u v

private theorem off_sum_continuous (T : ℝ) :
    Continuous (fun r => distinctPairTest T (physicalWeight T r)) := by
  unfold distinctPairTest
  exact continuous_finsetSum _ fun u _ =>
    continuous_finsetSum _ fun v _ => off_weight_continuous T u v

private theorem physical_projection_integral {T a b : ℝ} (hT : 1 < T) (hab : a ≤ b) :
    (∫ r in a..b, physicalProjection T r) = restoredPrimeMoment T a b := by
  classical
  let ord := copyOrdinate T
  have hd : Continuous (fun r => ∑ i : Copies T, physicalWeight T r (ord i) (ord i)) :=
    continuous_finsetSum _ fun i _ => weight_continuous T (ord i) (ord i)
  unfold physicalProjection restoredPrimeMoment
  rw [prime_expectedPairMass_eq_distinct]
  rw [intervalIntegral.integral_add (hd.intervalIntegrable _ _)
    ((off_sum_continuous T).intervalIntegrable _ _)]
  congr 1
  · rw [intervalIntegral.integral_finsetSum (f := fun i r => physicalWeight T r (ord i) (ord i))
      (fun i _ => (weight_continuous T (ord i) (ord i)).intervalIntegrable a b)]
    exact Finset.sum_congr rfl fun i _ => physical_integral hT hab _ _
  · unfold distinctPairTest
    let f := fun (u v r : ℝ) => if u=v then 0 else physicalWeight T r u v
    rw [intervalIntegral.integral_finsetSum
      (f := fun u r => ∑ v ∈ actualOrdinateSupport T, f u v r)
      (fun u _ => (continuous_finsetSum _ fun v _ => off_weight_continuous T u v).intervalIntegrable
        a b)]
    apply Finset.sum_congr rfl
    intro u _
    rw [intervalIntegral.integral_finsetSum (f := fun v r => f u v r)
      (fun v _ => (off_weight_continuous T u v).intervalIntegrable
        a b)]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hg : u=v
    · simp [f, hg]
    · simpa only [f,hg,if_false] using physical_integral hT hab u v

private theorem unscale_projection {T r : ℝ} (hT : 1 < T) (hr : 0 ≤ r) :
    physicalProjection T r =
      ((Ncount 0 T : ℝ) * (r / (Real.log T / (2*Real.pi))) +
        expectedPairMass (limitingKernel primeFrequencies) (liftCopy T)
        (fun i j => max (r / (Real.log T / (2*Real.pi)) -
            |copyOrdinate T i - copyOrdinate T j|) 0)) / T := by
  classical
  let h := r/(Real.log T/(2*Real.pi))
  have hh : 0 ≤ h := div_nonneg hr (div_nonneg (Real.log_pos hT).le (by positivity))
  have he := prime_expectedPairMass_eq_distinct T (fun u v => max (h-|u-v|) 0)
  unfold physicalProjection
  rw [he, add_div]
  congr 1
  · change (∑ i : Copies T, max (h - |copyOrdinate T i - copyOrdinate T i|) 0 /T) = _
    simp only [sub_self, abs_zero, sub_zero, max_eq_left hh, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, card_copies]
    ring
  · unfold distinctPairTest
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : u=v <;> simp [hv, physicalWeight,h]

theorem prime_missing_density_penalty (k : ℕ) (hk : 0 < k) :
    ∀ᶠ T : ℝ in atTop, (k:ℝ)^2 * (primeMissingDensity T)^2 -
      ((k:ℝ)+1)*primeMissingDensity T ≤
      (∫ r in (k:ℝ)..((k:ℝ)+1), unfoldedWindowEnergy T r) -
        restoredPrimeMoment T (k:ℝ) ((k:ℝ)+1) := by
  have hk' : 0 ≤ (k:ℝ) := by exact_mod_cast hk.le
  filter_upwards [eventually_gt_atTop (1:ℝ), eventually_supported_width ((k:ℝ)+1)]
    with T hT hfloor
  have hTp := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  have hcard : (actualOrdinateSupport T).card ≤ Ncount 0 T := by
    rw [← card_copies T]
    exact (Finset.card_image_le).trans_eq Finset.card_univ
  have hd : 0 ≤ primeMissingDensity T := by
    unfold primeMissingDensity
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hcard)) (by positivity)
  rw [← physical_projection_integral hT (show (k:ℝ)≤(k:ℝ)+1 by linarith)]
  apply DPPLargeWidth.integrated_restored_loss_ge _ _ hk' hd (unfoldedWindowEnergy T)
    (physicalProjection T) (unfoldedWindowEnergy_mono T hT).intervalIntegrable
  · have hcont : Continuous (physicalProjection T) :=
      (continuous_finsetSum _ fun i _ =>
        weight_continuous T (copyOrdinate T i) (copyOrdinate T i)).add
        (off_sum_continuous T)
    exact hcont.intervalIntegrable _ _
  · intro r hr
    have hr0 := hk'.trans hr.1
    obtain ⟨hh, hlow⟩ := hfloor r hr0 hr.2
    rw [unscale_projection hT hr0]
    have hJ := actual_prime_physical_jensen hTp hh hlow
    dsimp only at hJ
    have e : r * primeMissingDensity T =
        (r / (Real.log T / (2*Real.pi))) *
          ((Ncount 0 T:ℝ) - (actualOrdinateSupport T).card) / T := by
      unfold primeMissingDensity
      field_simp [Real.pi_ne_zero, hL.ne', hTp.ne']
    rw [e]; exact hJ
end RiemannResearch.Analysis.ProjectedDistinctSpacing

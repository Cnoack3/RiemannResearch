import RiemannResearch.Analysis.SquarefreeXiCompanion
import RiemannResearch.Analysis.ReciprocalLogDerivOrder
import RiemannResearch.Analysis.MicroscopicPositiveGapProjection

/-!
# Recovering ordinate multiplicity from simple representatives

The squarefree xi companion removes the pole of the zeta logarithmic derivative
at each distinct complex zero. Its limiting value records the original analytic
multiplicity times the companion derivative. Summing reciprocal slopes in a
horizontal fibre recovers its full occurrence count. At finite height the
positive-gap correction vanishes exactly when every participating fibre is a
singleton.
-/

noncomputable section

open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.OrdinateSlopeCorrection

open SquarefreeXiCompanion ReciprocalLogDerivOrder ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MicroscopicPositiveGapProjection ZeroDPPCollisionLoss

/-- Multiplication by the companion cancels the pole. The remaining value
remembers the original multiplicity of zeta at this location. -/
theorem companion_mul_logDeriv_limit (ρ : LiCriterion.NontrivialZero) :
    Tendsto (fun s => companion s * logDeriv riemannZeta s) (𝓝[≠] ρ.val)
      (𝓝 (deriv companion ρ.val * (zeroMult ρ.val : ℂ))) := by
  have hz : companion ρ.val = 0 := (companion_zero_iff _).mpr ⟨ρ, rfl⟩
  have h₁ : ρ.val ≠ 1 := by
    intro he
    have hh := ρ.property.2.2
    rw [he] at hh
    simp at hh
  have hc := (companion_entire ρ.val).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field] at hc
  simp only [hz, sub_zero] at hc
  apply (hc.mul (zeta_logDeriv_residue h₁)).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s - ρ.val ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
  change (companion s / (s - ρ.val)) * ((s - ρ.val) * logDeriv riemannZeta s) = _
  rw [← mul_assoc, div_mul_cancel₀ _ hne]

/-- Group all complex locations with the given ordinate before reading their
inverse slopes. The formula also holds at ordinates outside the support. -/
theorem ordinateMultiplicity_eq_inverseSlopeSum (T u : ℝ) :
    (actualOrdinateMultiplicity T u : ℝ) =
      ∑ ρ ∈ (cutoff T).filter (fun ρ => ρ.im = u), slopeWeight ρ := by
  classical
  let F := (Finset.univ : Finset (Copies T)).filter (fun i => copyOrdinate T i = u)
  calc
    (actualOrdinateMultiplicity T u : ℝ) = ∑ i ∈ F, (1 : ℝ) := by
      change (F.card : ℝ) = _
      simp
    _ = ∑ i : Copies T, if copyOrdinate T i = u then 1 else 0 := by
      simp only [F, Finset.sum_filter]
    _ = slopeSum T (fun ρ => if ρ.im = u then 1 else 0) :=
      (slopeSum_eq_copies T (fun ρ => if ρ.im = u then 1 else 0)).symm
    _ = _ := by
      simp only [slopeSum, Finset.sum_filter, mul_ite, mul_one, mul_zero]

private theorem one_le_ordinateMultiplicity {T u : ℝ} (hu : u ∈ actualOrdinateSupport T) :
    1 ≤ actualOrdinateMultiplicity T u := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  change 0 < (Finset.univ.filter (fun j : Copies T => copyOrdinate T j = copyOrdinate T i)).card
  exact Finset.card_pos.mpr ⟨i, by simp⟩

/-- Only fibres that are endpoints of a strictly positive counted gap enter
the criterion. A repeated ordinate isolated from the window contributes zero. -/
theorem correction_eq_zero_iff_singleton_endpoints {T : ℝ} (hT : 1 < T) (q : ℝ) :
    multiplicityCorrection T q = 0 ↔
      ∀ u ∈ actualOrdinateSupport T, ∀ v ∈ actualOrdinateSupport T,
        gapIndicator T q u v = 1 →
        actualOrdinateMultiplicity T u = 1 ∧ actualOrdinateMultiplicity T v = 1 := by
  classical
  let M := actualOrdinateMultiplicity T
  let e (u v : ℝ) := ((M u : ℝ) * M v - 1) * gapIndicator T q u v
  let S := actualOrdinateSupport T
  have hM {u : ℝ} (hu : u ∈ S) : (1 : ℝ) ≤ M u := by
    exact_mod_cast one_le_ordinateMultiplicity hu
  have he {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) : 0 ≤ e u v := by
    apply mul_nonneg
    · have h := mul_le_mul (hM hu) (hM hv) zero_le_one (zero_le_one.trans (hM hu))
      simpa using sub_nonneg.mpr h
    · dsimp only [gapIndicator]
      split_ifs <;> norm_num
  have hn : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  change (∑ u ∈ S, ∑ v ∈ S, e u v) / normalizer T = 0 ↔ _
  rw [div_eq_zero_iff, or_iff_left hn.ne']
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun u hu => Finset.sum_nonneg (fun v hv => he hu hv))]
  constructor
  · intro h u hu v hv hw
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => he hu hv)).mp (h u hu) v hv
    dsimp [e] at hz
    rw [hw, mul_one] at hz
    have heq : M u * M v = 1 := by
      exact_mod_cast (sub_eq_zero.mp hz)
    have h₁ : M u ≤ M u * M v := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M u) (one_le_ordinateMultiplicity hv)
    have h₂ : M v ≤ M u * M v := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (M v) (one_le_ordinateMultiplicity hu)
    have h₃ : 1 ≤ M u := one_le_ordinateMultiplicity hu
    have h₄ : 1 ≤ M v := one_le_ordinateMultiplicity hv
    change M u = 1 ∧ M v = 1
    omega
  · intro h u hu
    apply Finset.sum_eq_zero (fun v hv => ?_)
    by_cases hw : gapIndicator T q u v = 1
    · obtain ⟨hm, hn⟩ := h u hu v hv hw
      simp [e, M, hm, hn]
    · have hz : gapIndicator T q u v = 0 := by
        dsimp only [gapIndicator] at hw ⊢
        split_ifs at hw ⊢ <;> simp_all
      simp [e, hz]

end RiemannResearch.Analysis.OrdinateSlopeCorrection

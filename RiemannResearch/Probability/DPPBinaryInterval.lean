import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-!
# Extracting a unit interval from the exclusion of five alternating values

On a set of full measure, an integrable binary function of mass one has zeros
in both tails. Excluding the ordered pattern zero, one, zero, one, zero
then forces every point of that set strictly between two ones to be a one.
The infimum and supremum of the ones give the endpoints.
-/

open Filter MeasureTheory Set

namespace RiemannResearch.DPPSpectral

private theorem zero_in_long_interval {f : ℝ → ℝ} (hf : Integrable f)
    (hmass : (∫ x, f x) = 1) {D : Set ℝ} (hD : ∀ᵐ x ∂volume, x ∈ D)
    (hbin : ∀ x ∈ D, f x = 0 ∨ f x = 1) (a b : ℝ) (hlen : 1 < b-a) :
    ∃ x ∈ D, x ∈ Ioo a b ∧ f x = 0 := by
  classical
  by_contra h
  have hint : Integrable ((Ioo a b).indicator (1 : ℝ → ℝ)) := by
    apply (integrable_indicator_iff measurableSet_Ioo).mpr
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hle : (∫ x, (Ioo a b).indicator (1 : ℝ → ℝ) x) ≤ ∫ x, f x := by
    apply integral_mono_ae hint hf
    filter_upwards [hD] with x hx
    rcases hbin x hx with hv | hv
    · have hn : x ∉ Ioo a b := fun hi => h ⟨x, hx, hi, hv⟩
      simp [hn, hv]
    · by_cases hi : x ∈ Ioo a b <;> simp [hi, hv]
  rw [hmass, integral_indicator_one measurableSet_Ioo, Real.volume_real_Ioo_of_le (by linarith)] at hle
  linarith

/-- Conull ordered geometry converts the five-point obstruction to a
unit-interval spectrum. No measurability of the chosen set of good points
is required. -/
theorem exists_unit_interval_of_no_five {f : ℝ → ℝ} (hf : Integrable f)
    (hmass : (∫ x, f x) = 1) {D : Set ℝ} (hD : ∀ᵐ x ∂volume, x ∈ D)
    (hbin : ∀ x ∈ D, f x = 0 ∨ f x = 1)
    (hp : ∀ a b c d e : ℝ, a ∈ D → b ∈ D → c ∈ D → d ∈ D → e ∈ D →
      a < b → b < c → c < d → d < e →
      f a = 0 → f b = 1 → f c = 0 → f d = 1 → f e = 0 → False) :
    ∃ a : ℝ, f =ᵐ[volume] (Ioo a (a+1)).indicator (1 : ℝ → ℝ) := by
  classical
  let U := {x : ℝ | x ∈ D ∧ f x = 1}
  have hU : U.Nonempty := by
    by_contra hn
    have hz : f =ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [hD] with x hx
      exact (hbin x hx).resolve_right fun h1 => hn ⟨x, hx, h1⟩
    have hm := integral_congr_ae hz
    simp [hmass] at hm
  have leftZero (y : ℝ) : ∃ x ∈ D, x < y ∧ f x = 0 := by
    obtain ⟨x,hx,hxy,h0⟩ := zero_in_long_interval hf hmass hD hbin (y-2) y (by linarith)
    exact ⟨x,hx,hxy.2,h0⟩
  have rightZero (y : ℝ) : ∃ x ∈ D, y < x ∧ f x = 0 := by
    obtain ⟨x,hx,hxy,h0⟩ := zero_in_long_interval hf hmass hD hbin y (y+2) (by linarith)
    exact ⟨x,hx,hxy.1,h0⟩
  have between {b c d : ℝ} (hb : b ∈ U) (hc : c ∈ D) (hd : d ∈ U)
      (hbc : b < c) (hcd : c < d) : f c = 1 := by
    obtain ⟨a, ha, hab, ha0⟩ := leftZero b
    obtain ⟨e, he, hde, he0⟩ := rightZero d
    exact (hbin c hc).resolve_left
      (hp a b c d e ha hb.1 hc hd.1 he hab hbc hcd hde ha0 hb.2 · hd.2 he0)
  obtain ⟨p,hpU⟩ := hU
  obtain ⟨a,ha,hap,ha0⟩ := leftZero p
  obtain ⟨b,hb,hpb,hb0⟩ := rightZero p
  have hlow : BddBelow U := by
    refine ⟨a, fun x hx => le_of_not_gt ?_⟩
    intro hxa
    linarith only [ha0, between hx ha hpU hxa hap]
  have hupp : BddAbove U := by
    refine ⟨b, fun x hx => le_of_not_gt ?_⟩
    intro hbx
    linarith only [hb0, between hpU hb hx hpb hbx]
  have heq : f =ᵐ[volume] (Ioo (sInf U) (sSup U)).indicator (1 : ℝ → ℝ) := by
    filter_upwards [hD, volume.ae_ne (sInf U), volume.ae_ne (sSup U)]
      with x hx hlo hhi
    by_cases hi : x ∈ Ioo (sInf U) (sSup U)
    · obtain ⟨u,hu,hux⟩ := exists_lt_of_csInf_lt ⟨p,hpU⟩ hi.1
      obtain ⟨v,hv,hxv⟩ := exists_lt_of_lt_csSup ⟨p,hpU⟩ hi.2
      simp [hi, between hu hx hv hux hxv]
    · have hf0 : f x = 0 := (hbin x hx).resolve_right fun hx1 => by
        have hxU : x ∈ U := ⟨hx,hx1⟩
        exact hi ⟨lt_of_le_of_ne (csInf_le hlow hxU) (Ne.symm hlo),
          lt_of_le_of_ne (le_csSup hupp hxU) hhi⟩
      simp [hi, hf0]
  have hlength := integral_congr_ae heq
  rw [hmass, integral_indicator_one measurableSet_Ioo,
    Real.volume_real_Ioo_of_le ((csInf_le hlow hpU).trans (le_csSup hupp hpU))]
    at hlength
  have htop : sSup U = sInf U + 1 := by linarith
  exact ⟨sInf U, htop ▸ heq⟩

end RiemannResearch.DPPSpectral

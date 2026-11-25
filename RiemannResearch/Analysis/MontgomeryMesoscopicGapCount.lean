import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.Analysis.DyadicZeroWassersteinLaws
import RiemannResearch.Analysis.MontgomeryWindowPairCorrelation
import RiemannResearch.Analysis.ActualZeroBandCount
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Actual positive-gap mass on growing physical windows

For a physical width tending to infinity but occupying a vanishing fraction
of the cutoff, the one-point counting law controls each interior row.
The boundary rows are charged to their actual occurrence count using the
unconditional band bound.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate DyadicZeroWasserstein

/-- Unfolding factor converting physical heights into mean-spacing units. -/
def unfoldingScale (T : ℝ) : ℝ := Real.log T / (2 * Real.pi)
/-- Positive neighbors in the clipped physical window starting at this occurrence,
normalized by the expected leading count. -/
def mesoscopicRow (T H : ℝ) (i : Copies T) : ℝ :=
  (Ncount (copyOrdinate T i) (min T (copyOrdinate T i + H)) : ℝ) / (H * unfoldingScale T)

private theorem pos_scale {T : ℝ} (hT : 1 < T) : 0 < unfoldingScale T :=
  div_pos (Real.log_pos hT) (by positivity)

private theorem row_identity {T H : ℝ} (hT : 1 < T) (hH : 0 < H) :
    positiveGapMass T (H * unfoldingScale T) / (H * unfoldingScale T) =
      (∑ i : Copies T, mesoscopicRow T H i) / unfoldedCutoff T := by
  let D := unfoldedCutoff T
  have ht := zero_lt_one.trans hT
  have hscaled : H / T * unfoldedCutoff T = H * unfoldingScale T := by
    unfold unfoldedCutoff unfoldingScale
    field_simp [ht.ne', Real.pi_ne_zero]
  rw [← hscaled, positiveGapMass_scaled_eq_height_rows hT (div_nonneg hH.le ht.le), Finset.sum_div,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  let t := copyOrdinate T i
  have ht₀ : 0 ≤ t := (mem_cutoff.mp i.1.property).2.1.le
  have htT : t ≤ T := (mem_cutoff.mp i.1.property).2.2
  have hcut : min 1 (t / T + H / T) * T = min T (t+H) := by
    rw [min_mul_of_nonneg _ _ ht.le, one_mul, add_mul, div_mul_cancel₀ _ ht.ne', div_mul_cancel₀ _ ht.ne']
  change (scaledHeightCount T (min 1 (t / T + H / T)) - scaledHeightCount T (t / T)) /
    (H / T * unfoldedCutoff T) = mesoscopicRow T H i / unfoldedCutoff T
  have hs := Ncount_add (a := 0) (b := t) (c := min T (t+H)) ht₀
    (le_min htT (le_add_of_nonneg_right hH.le))
  rw [scaledHeightCount, scaledHeightCount, hcut, div_mul_cancel₀ _ ht.ne', hs, Nat.cast_add, hscaled]
  dsimp only [mesoscopicRow,t]
  ring

private theorem eventually_all_rows_bounded (H : ℝ → ℝ) (hH : Tendsto H atTop atTop)
    (hHT : Tendsto (fun T => H T / T) atTop (𝓝 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, 0 ≤ mesoscopicRow T (H T) i ∧
      mesoscopicRow T (H T) i ≤ B := by
  obtain ⟨C,hC,hband⟩ := ActualZeroBandCount.exists_band_count_bound
  refine ⟨8 * Real.pi * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (9 : ℝ), hH.eventually_ge_atTop 9,
    hHT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with T hT hH₉ hHT₁
  intro i
  let t := copyOrdinate T i
  have ht := (zero_lt_one.trans (show 1 < T by linarith))
  have hH₀ : 0 < H T := by linarith
  have hL : 0 < unfoldingScale T := pos_scale (by linarith)
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hs : 0 ≤ t := (mem_cutoff.mp i.1.property).2.1.le
  have hsT : t ≤ T := (mem_cutoff.mp i.1.property).2.2
  have hH₁' : H T < T := by simpa only [one_mul] using (div_lt_iff₀ ht).mp hHT₁
  have hH₁ := hH₁'.le
  have hb := hband (t+H T) (H T) (by linarith) hH₀.le (by linarith)
  rw [add_sub_cancel_right] at hb
  have hn : (Ncount t (min T (t+H T)) : ℝ) ≤ Ncount t (t+H T) := by
    exact_mod_cast Ncount_mono le_rfl (min_le_right _ _)
  have hl : Real.log (t+H T) ≤ 2 * Real.log T := by
    have hsq : t+H T ≤ T*T := by nlinarith only [hsT,hH₁,mul_nonneg (show 0 ≤ T-2 by linarith) ht.le]
    simpa only [Real.log_mul ht.ne' ht.ne', two_mul] using Real.log_le_log (by linarith : 0 < t + H T) hsq
  have ha := mul_le_mul_of_nonneg_left hl (mul_nonneg hC.le (show 0 ≤ H T + 1 by linarith))
  refine ⟨div_nonneg (Nat.cast_nonneg _) (mul_nonneg hH₀.le hL.le), (div_le_iff₀ (mul_pos hH₀ hL)).mpr ?_⟩
  change (Ncount t (min T (t+H T)) : ℝ) ≤ 8 * Real.pi * C * (H T * unfoldingScale T)
  calc
    _ ≤ C*(H T+1)*(2*Real.log T) := hn.trans (hb.trans ha)
    _ ≤ C*(2*H T)*(2*Real.log T) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC.le) (by positivity)
    _ = _ := by unfold unfoldingScale; field_simp [Real.pi_ne_zero]; ring

/-- On every interior height strip the normalized actual row tends uniformly
to one. Physical width H goes to infinity and H/T goes to zero. -/
theorem eventually_mesoscopic_interior_rows {H : ℝ → ℝ} (hRvM : CumulativeRvM)
    (hH : Tendsto H atTop atTop) (hHT : Tendsto (fun T => H T / T) atTop (𝓝 0))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, δ * T ≤ copyOrdinate T i →
      copyOrdinate T i ≤ (1-δ)*T → |mesoscopicRow T (H T) i - 1| ≤ ε := by
  obtain ⟨C,hC,he⟩ := hRvM
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp he
  let K := |Real.log δ| + |Real.log (2*Real.pi)|
  have hlim₁ : Tendsto (fun T : ℝ => K / Real.log T) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul K
  have hlim₂ : Tendsto (fun T : ℝ => 4*Real.pi*C / H T) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hH).const_mul (4*Real.pi*C)
  have hu := (hlim₁.add hlim₂).eventually (gt_mem_nhds (by simpa using hε : 0 + 0 < ε))
  filter_upwards [eventually_gt_atTop (1 : ℝ), (tendsto_id.const_mul_atTop hδ).eventually_ge_atTop t₀,
    hH.eventually_gt_atTop 0, hHT.eventually (gt_mem_nhds hδ), hu] with T hT hlow hpos hsmall hfinal
  intro i hleft hright
  let t := copyOrdinate T i
  let u := t + H T
  have ht := zero_lt_one.trans hT
  have hlog := Real.log_pos hT
  have htpos : 0 < t := (mul_pos hδ ht).trans_le hleft
  have htu : t < u := by dsimp only [u]; linarith
  have hUT : u ≤ T := by
    dsimp only [u]
    have hh := (div_lt_iff₀ ht).mp hsmall
    nlinarith only [hh, hright]
  have ha := ht₀ t (hlow.trans hleft)
  have hb := ht₀ u ((hlow.trans hleft).trans htu.le)
  have hCbound (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) (he : |countError s| ≤ C*Real.log s) :
      |countError s| ≤ C*Real.log T :=
    he.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hs hsT) hC)
  have het := abs_le.mp (hCbound t htpos (htu.le.trans hUT) ha)
  have heu := abs_le.mp (hCbound u (htpos.trans htu) hUT hb)
  obtain ⟨s,hs,hd⟩ := exists_hasDerivAt_eq_slope countMain slope htu
    (fun v hv => (countMain_deriv (htpos.trans_le hv.1)).continuousAt.continuousWithinAt)
    (fun v hv => countMain_deriv (htpos.trans hv.1))
  have hm : countMain u - countMain t = H T * slope s := by
    have hdiff : u-t = H T := by dsimp [u]; ring
    rw [hdiff] at hd
    linarith only [(eq_div_iff hpos.ne').mp hd]
  have hspos := htpos.trans hs.1
  have hp2 : 0 < 2*Real.pi := by positivity
  have hlower := Real.log_le_log (mul_pos hδ ht) (hleft.trans hs.1.le)
  rw [Real.log_mul hδ.ne' ht.ne'] at hlower
  have hupper := Real.log_le_log hspos (hs.2.le.trans hUT)
  have hslope : |Real.log (s/(2*Real.pi)) - Real.log T| ≤ K := by
    rw [Real.log_div hspos.ne' hp2.ne']
    dsimp only [K]
    exact abs_le.mpr ⟨by linarith only [hlower,neg_abs_le (Real.log δ),le_abs_self (Real.log (2*Real.pi))],
      by linarith only [hupper,neg_abs_le (Real.log (2*Real.pi)),abs_nonneg (Real.log δ)]⟩
  have hnum := Ncount_add (a := 0) (b := t) (c := u) htpos.le htu.le
  have hnum' : (Ncount t u : ℝ) = (Ncount 0 u : ℝ) - (Ncount 0 t : ℝ) := by
    rw [hnum, Nat.cast_add]; ring
  have hid : (Ncount t u : ℝ) - H T * unfoldingScale T =
      countError u - countError t + (H T / (2*Real.pi)) * (Real.log (s/(2*Real.pi)) - Real.log T) := by
    rw [hnum']
    unfold countError unfoldingScale
    unfold DyadicZeroWasserstein.slope at hm
    linarith only [hm, show H T / (2*Real.pi) * (Real.log (s/(2*Real.pi)) - Real.log T) =
      H T * (Real.log (s/(2*Real.pi))/(2*Real.pi)) - H T*(Real.log T/(2*Real.pi)) by ring]
  have hden := mul_pos hpos (pos_scale hT)
  have htarget : |(Ncount t u : ℝ) - H T * unfoldingScale T| ≤
      2*C*Real.log T + H T / (2*Real.pi) * K := by
    rw [hid]
    have hterm := mul_le_mul_of_nonneg_left hslope (div_nonneg hpos.le hp2.le)
    have herr : |countError u - countError t| ≤ 2*C*Real.log T := by
      exact abs_le.mpr ⟨by linarith only [heu.1,het.2], by linarith only [heu.2,het.1]⟩
    exact (abs_add_le _ _).trans (add_le_add herr (by simpa only [abs_mul,abs_of_pos (div_pos hpos hp2)] using hterm))
  change |(Ncount t (min T u) : ℝ) / (H T*unfoldingScale T) - 1| ≤ ε
  rw [min_eq_right hUT, ← div_self hden.ne', ← sub_div, abs_div, abs_of_pos hden]
  apply (div_le_div_of_nonneg_right htarget hden.le).trans
  have hid' : (2*C*Real.log T + H T/(2*Real.pi)*K) / (H T*unfoldingScale T) =
      K/Real.log T + 4*Real.pi*C/H T := by
    unfold unfoldingScale
    field_simp [hpos.ne', hlog.ne', Real.pi_ne_zero]
    ring
  rw [hid']
  exact hfinal.le

/-- A uniformly bounded actual-occurrence statistic whose interior values
tend uniformly to one has normalized real mean tending to one. The two
discarded boundary strips are charged to the measured cumulative counts. -/
theorem ordinateRowMean_tendsto_of_interior {f : (T : ℝ) → Copies T → ℝ}
    (hglobal : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, |f T i-1| ≤ B+1)
    (hinterior : ∀ {δ ε : ℝ}, 0 < δ → 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ i : Copies T,
      δ*T ≤ copyOrdinate T i → copyOrdinate T i ≤ (1-δ)*T → |f T i-1| ≤ ε) :
    Tendsto (fun T : ℝ => (∑ i : Copies T, f T i)/unfoldedCutoff T) atTop (𝓝 1) := by
  classical
  obtain ⟨B,hB,hbound⟩ := hglobal
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := min (1/4 : ℝ) (η / (16 * (B+1)))
  let ε := min (1/4 : ℝ) (η / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hδ₄ : δ ≤ 1/4 := min_le_left _ _
  have hδB : 16 * (B+1) * δ ≤ η := by
    have h := (le_div_iff₀ (show 0 < 16*(B+1) by positivity)).mp
      (show δ ≤ η/(16*(B+1)) from min_le_right _ _)
    linarith only [h]
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hη (by norm_num))
  have hεη : ε ≤ η/8 := min_le_right _ _
  have hN := scaledHeightCount_tendsto (show 0 ≤ (1 : ℝ) by norm_num)
  have hedge := ((scaledHeightCount_tendsto hδ.le).add hN).sub
    (scaledHeightCount_tendsto (show 0 ≤ 1-δ by linarith))
  have hed := hedge.eventually (gt_mem_nhds (show δ+1-(1-δ) < 3*δ by linarith))
  have hclose := Metric.tendsto_nhds.mp hN ε hε
  filter_upwards [hed,hclose,hinterior hδ hε,hbound,eventually_gt_atTop (1:ℝ)] with T he hc hi hb hT
  let D := unfoldedCutoff T
  let N := (Ncount 0 T : ℝ)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hN' : scaledHeightCount T 1 = N / D := by simp [scaledHeightCount,N,D]
  rw [Real.dist_eq,hN'] at hc
  change scaledHeightCount T δ + scaledHeightCount T 1 - scaledHeightCount T (1-δ) < 3*δ at he
  rw [hN'] at he
  have hε₄ : ε ≤ 1/4 := min_le_left _ _
  have hN₂ : N/D ≤ 2 := by linarith only [(abs_lt.mp hc).2, hε₄]
  let t := copyOrdinate T
  let l := fun i : Copies T => if t i ≤ δ*T then (1 : ℝ) else 0
  let r := fun i : Copies T => if (1-δ)*T < t i then (1 : ℝ) else 0
  have ht0 := zero_lt_one.trans hT
  have hdlo : δ*T ≤ T := by nlinarith only [hδ₄, mul_nonneg (show 0 ≤ 1-δ by linarith) ht0.le]
  have hdhi : (1-δ)*T ≤ T := by nlinarith only [mul_nonneg hδ.le ht0.le]
  have hl : (∑ i : Copies T, l i) = (Ncount 0 (δ*T) : ℝ) := (cumulative_copy_steps hdlo).symm
  have hr : (∑ i : Copies T, r i) = N - (Ncount 0 ((1-δ)*T) : ℝ) := by
    rw [cumulative_copy_steps hdhi]
    have ho : N = ∑ _i : Copies T, (1 : ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul,mul_one,N]
    rw [ho, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change (if (1-δ)*T < t i then (1 : ℝ) else 0) = 1 - (if t i ≤ (1-δ)*T then 1 else 0)
    by_cases h : t i ≤ (1-δ)*T <;> simp [h,lt_iff_not_ge]
  have hsingle (i : Copies T) :
      |f T i - 1| ≤ ε + (B+1)*(l i + r i) := by
    have hall := hb i
    by_cases h₁ : t i ≤ δ*T <;> by_cases h₂ : (1-δ)*T < t i
    · simp [l,r,h₁,h₂]; linarith only [hall,hε,hB]
    · simp [l,r,h₁,h₂]; linarith only [hall,hε]
    · simp [l,r,h₁,h₂]; linarith only [hall,hε]
    · simpa only [l,r,if_neg h₁,if_neg h₂,zero_add,mul_zero,add_zero] using
        hi i (le_of_not_ge h₁) (le_of_not_gt h₂)
  have hS : |(∑ i : Copies T, f T i) - N| ≤
      N*ε + (B+1)*((Ncount 0 (δ*T) : ℝ) + N - (Ncount 0 ((1-δ)*T) : ℝ)) := by
    have ho : (∑ _i : Copies T, (1 : ℝ)) = N := by
      simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul,mul_one,N]
    have hnum : (∑ i : Copies T, f T i) - N =
        ∑ i : Copies T, (f T i - 1) := by
      rw [Finset.sum_sub_distrib, ho]
    rw [hnum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum fun i _ => hsingle i).trans_eq
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hl, hr]
    simp only [Finset.sum_const,Finset.card_univ,card_copies,nsmul_eq_mul,N]
    ring
  have heD : ((Ncount 0 (δ*T) : ℝ)+ N - (Ncount 0 ((1-δ)*T) : ℝ))/ D ≤ 3*δ := by
    rw [sub_div,add_div]
    exact he.le
  have hnormalized :
      |(∑ i : Copies T, f T i)/D - N/D| ≤ 2*ε + (B+1)*(3*δ) := by
    rw [← sub_div, abs_div,abs_of_pos hD]
    apply (div_le_div_of_nonneg_right hS hD.le).trans
    calc
      _ = N/D * ε + (B+1)*(((Ncount 0 (δ*T) : ℝ)+ N - (Ncount 0 ((1-δ)*T) : ℝ))/D) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hN₂ hε.le)
        (mul_le_mul_of_nonneg_left heD (by linarith))
  rw [Real.dist_eq]
  apply (abs_sub_le _ (N/D) _).trans_lt
  nlinarith only [hnormalized,hc,hδB,hεη,hη]

/-- The exact sum over all interior and boundary rows gives the mesoscopic
limit at physical widths tending to infinity with H/T tending to zero. -/
theorem positiveGapMass_mesoscopic_tendsto_of_cumulativeRvM
    (hRvM : CumulativeRvM) {H : ℝ → ℝ} (hH : Tendsto H atTop atTop)
    (hHT : Tendsto (fun T => H T / T) atTop (𝓝 0)) :
    Tendsto (fun T => positiveGapMass T (H T * unfoldingScale T) /
      (H T * unfoldingScale T)) atTop (𝓝 1) := by
  obtain ⟨B,hB,hbounds⟩ := eventually_all_rows_bounded H hH hHT
  have hglobal : ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, |mesoscopicRow T (H T) i-1| ≤ B+1 := by
    filter_upwards [hbounds] with T ht i
    exact abs_le.mpr ⟨by linarith only [(ht i).1,hB],by linarith only [(ht i).2]⟩
  have h := ordinateRowMean_tendsto_of_interior ⟨B,hB,hglobal⟩
    (fun hδ hε => eventually_mesoscopic_interior_rows hRvM hH hHT hδ hε)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),hH.eventually_gt_atTop 0] with T hT hHT
  exact (row_identity hT hHT).symm

/-- The full count of strictly positive gaps is the sum of actual counting
increments starting at each zero occurrence. -/
theorem positiveGapMass_eq_ordinate_window_counts {T H : ℝ} (hT : 1 < T) (hH : 0 < H) :
    positiveGapMass T (H * unfoldingScale T) =
      (∑ i : Copies T, (Ncount (copyOrdinate T i)
        (min T (copyOrdinate T i + H)) : ℝ)) / unfoldedCutoff T := by
  have hr := row_identity hT hH
  unfold mesoscopicRow at hr
  rw [← Finset.sum_div] at hr
  apply (div_left_inj' (mul_pos hH (pos_scale hT)).ne').mp
  exact hr.trans (by ring)

/-- The occurrence-sampled count residual at unfolded width R. -/
def centeredOrdinateWindowCount (T R : ℝ) : ℝ :=
  (∑ i : Copies T, ((Ncount (copyOrdinate T i)
    (min T (copyOrdinate T i + R / unfoldingScale T)) : ℝ) - R)) / unfoldedCutoff T

/-- The complete signed residual subtracts R for each actual occurrence. -/
theorem centeredOrdinateWindowCount_eq {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    centeredOrdinateWindowCount T R =
      positiveGapMass T R - R * ((Ncount 0 T : ℝ) / unfoldedCutoff T) := by
  have hp := positiveGapMass_eq_ordinate_window_counts hT (div_pos hR (pos_scale hT))
  rw [div_mul_cancel₀ _ (pos_scale hT).ne'] at hp
  rw [centeredOrdinateWindowCount, Finset.sum_sub_distrib, sub_div, ← hp,
    Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
  ring

/-- Fixed-width PCC asks for the signed correction in the occurrence-sampled
count, including the sine hole. The mesoscopic unit-density law supplies
only the leading term on growing unfolded widths. -/
theorem positiveGapPCC_iff_centeredOrdinateWindowCounts :
    PositiveGapPCC ↔ ∀ R : ℝ, 0 < R →
      Tendsto (fun T => centeredOrdinateWindowCount T R) atTop (𝓝 (sineGapMass R - R)) := by
  constructor
  · intro h R hR
    have hp : Tendsto (fun T => positiveGapMass T R) atTop (𝓝 (sineGapMass R)) := by
      apply Metric.tendsto_nhds.mpr
      intro η hη
      filter_upwards [h R R hR le_rfl (η/2) (by linarith)] with T hT
      simpa only [Real.dist_eq] using
        (hT R ⟨le_rfl,le_rfl⟩).trans_lt (by linarith : η/2 < η)
    have hlim := hp.sub (tendsto_count_div_mainTerm.const_mul R)
    simp only [mul_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (centeredOrdinateWindowCount_eq hT hR).symm
  · intro h
    apply positiveGapPCC_of_pointwise
    intro R hR
    have hlim := (h R hR).add (tendsto_count_div_mainTerm.const_mul R)
    simp only [mul_one,sub_add_cancel] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    rw [centeredOrdinateWindowCount_eq hT hR, unfoldedCutoff, sub_add_cancel]

/-- Unfolded widths growing faster than log T and strictly slower than the
full cutoff have asymptotically one positive pair per unit width and per zero. -/
theorem positiveGapMass_mesoscopic_tendsto {R : ℝ → ℝ}
    (hgrowth : Tendsto (fun T : ℝ => R T / Real.log T) atTop atTop)
    (hsmall : Tendsto (fun T : ℝ => R T / unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T => positiveGapMass T (R T) / R T) atTop (𝓝 1) := by
  let H := fun T => R T / unfoldingScale T
  have hH : Tendsto H atTop atTop := by
    apply (hgrowth.const_mul_atTop (show 0 < 2*Real.pi by positivity)).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    dsimp only [H,unfoldingScale]
    field_simp [Real.pi_ne_zero, (Real.log_pos hT).ne']
    <;> ring
  have hHT : Tendsto (fun T => H T / T) atTop (𝓝 0) := by
    apply hsmall.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    dsimp only [H, unfoldingScale, unfoldedCutoff]
    field_simp [Real.pi_ne_zero, (Real.log_pos hT).ne', (zero_lt_one.trans hT).ne']
    <;> ring
  apply (positiveGapMass_mesoscopic_tendsto_of_cumulativeRvM actual_cumulativeRvM hH hHT).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have he : H T * unfoldingScale T = R T := div_mul_cancel₀ _ (pos_scale hT).ne'
  simp only [he]

end RiemannResearch.Analysis.MontgomeryPositiveGap

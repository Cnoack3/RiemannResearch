import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import RiemannResearch.Analysis.ActualDistinctOrdinateGram
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Unconditional lower bounds for actual fixed-width microscopic gaps

Partition the scaled ordinate interval into cells of width R and keep every
strictly ordered pair of distinct heights in the same cell. The exact integer
occupancy inequality in each cell leads to the Montgomery–Taylor lower bound
k κ - k(k+1)/(2R) for the actual strictly positive pair count. This holds at
each fixed microscopic width R>0, without a simplicity or critical-line
assumption. No sine-model convergence enters the estimate.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

private theorem twice_strict_pairs (A : Finset ℝ) :
    2*(∑ x ∈ A, ∑ y ∈ A, if x < y then (1:ℝ) else 0) =
      (A.card:ℝ)^2 - A.card := by
  classical
  let p := fun x y : ℝ => if x < y then (1:ℝ) else 0
  have hs : (∑ x ∈ A, ∑ y ∈ A, p y x) = ∑ x ∈ A, ∑ y ∈ A, p x y := Finset.sum_comm
  have hrow (x : ℝ) (hx : x ∈ A) :
      (∑ y ∈ A, (p x y + p y x)) = (A.card:ℝ)-1 := by
    calc
      _ = ∑ y ∈ A, ((1:ℝ) - if y=x then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        rcases lt_trichotomy x y with h|h|h
        · simp only [p,if_pos h,if_neg h.not_gt,if_neg h.ne',sub_zero,add_zero]
        · simp [p,h]
        · simp only [p,if_neg h.not_gt,if_pos h,if_neg h.ne,sub_zero,zero_add]
      _ = _ := by simp [Finset.sum_sub_distrib,hx]
  calc
    _ = (∑ x ∈ A, ∑ y ∈ A, p x y) + ∑ x ∈ A, ∑ y ∈ A, p y x := by rw [hs]; ring
    _ = ∑ x ∈ A, ∑ y ∈ A, (p x y+p y x) := by simp only [Finset.sum_add_distrib]
    _ = ∑ _x ∈ A, ((A.card:ℝ)-1) := Finset.sum_congr rfl hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- A nonnegative statistic of distinct heights is dominated by its sum
over all actual analytic multiplicity copies. -/
theorem sum_distinct_ordinates_le_copies (T : ℝ) (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ f x) :
    (∑ γ ∈ distinctOrdinates T, f γ) ≤ ∑ i : Copies T, f (copyOrdinate T i) := by
  classical
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Copies T)), copyOrdinate T j ∈ distinctOrdinates T :=
    fun j _ => copyOrdinate_mem_distinct T j
  have hsum := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Copies T)))
    (t := distinctOrdinates T) (g := copyOrdinate T) hmaps f
  rw [← hsum]
  apply Finset.sum_le_sum
  intro γ hγ
  simp only [Finset.sum_const,nsmul_eq_mul]
  change f γ ≤ (ordinateMultiplicity T γ : ℝ)*f γ
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (show (1:ℝ) ≤ ordinateMultiplicity T γ by exact_mod_cast ordinateMultiplicity_pos hγ) (hf γ)

private theorem cell_packing_bound (S : Finset ℝ) (key : ℝ → ℕ) (B k : ℕ)
    (hkey : ∀ x ∈ S, key x < B) (f : ℝ → ℝ → ℝ) (hf : ∀ x y, 0 ≤ f x y)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, key x = key y → x < y → 1 ≤ f x y) :
    (k:ℝ)*S.card - (B:ℝ)*((k:ℝ)*(k+1)/2) ≤ ∑ x ∈ S, ∑ y ∈ S, f x y := by
  classical
  let A := fun j : ℕ => S.filter fun x => key x=j
  have hm : ∀ x ∈ S, key x ∈ Finset.range B := fun x hx => Finset.mem_range.mpr (hkey x hx)
  have hcount : (∑ j ∈ Finset.range B, ((A j).card:ℝ)) = S.card := by
    simpa only [A,Finset.sum_const,nsmul_eq_mul,mul_one] using
      (Finset.sum_fiberwise_of_maps_to hm (fun _ : ℝ => (1:ℝ)))
  have hc (j : ℕ) : (k:ℝ)*((A j).card:ℝ) - (k:ℝ)*(k+1)/2 ≤
      ∑ x ∈ A j, ∑ y ∈ A j, f x y := by
    let n := (A j).card
    have hnn : 0 ≤ ((n:ℝ)-k)*((n:ℝ)-k-1) := by
      by_cases h : n ≤ k
      · have hc : (n:ℝ) ≤ k := by exact_mod_cast h
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hc) (by linarith)
      · have hc : (k:ℝ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
        exact mul_nonneg (by linarith) (by linarith)
    have hp : (∑ x ∈ A j, ∑ y ∈ A j, if x<y then (1:ℝ) else 0) ≤
        ∑ x ∈ A j, ∑ y ∈ A j, f x y := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨hxS,hxk⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyS,hyk⟩ := Finset.mem_filter.mp hy
      split_ifs with hxy
      · exact hpair x hxS y hyS (hxk.trans hyk.symm) hxy
      · exact hf x y
    have hd := twice_strict_pairs (A j)
    dsimp only [n] at hnn
    nlinarith only [hnn,hd,hp]
  have hs : (∑ j ∈ Finset.range B, ∑ x ∈ A j, ∑ y ∈ A j, f x y) ≤
      ∑ x ∈ S, ∑ y ∈ S, f x y := by
    rw [← Finset.sum_fiberwise_of_maps_to hm (fun x => ∑ y ∈ S, f x y)]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro x _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun y _ _ => hf x y)
  have htot := (Finset.sum_le_sum (s := Finset.range B) (fun j _ => hc j)).trans hs
  simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,hcount,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul] using htot

/-- Exact-width finite packing bound. The right endpoint is accounted for
by the floor plus one in the number of cells. All actual multiplicities may
increase the positive-gap score on the right. -/
theorem microscopic_gap_packing_bound {T R : ℝ} (hT : 1 < T) (hR : 0 < R) (k : ℕ) :
    (k:ℝ)*(distinctOrdinates T).card -
      ((⌊unfoldedCutoff T/R⌋₊:ℝ)+1)*((k:ℝ)*(k+1)/2) ≤
      unfoldedCutoff T * positiveGapMass T R := by
  classical
  let S := distinctOrdinates T
  let L := Real.log T /(2*Real.pi)
  let D := unfoldedCutoff T
  let key := fun x : ℝ => ⌊L*x/R⌋₊
  let B := ⌊D/R⌋₊+1
  let f := fun x y : ℝ => if 0 < L*(y-x) ∧ L*(y-x) ≤ R then (1:ℝ) else 0
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hDT : L*T=D := by dsimp [L,D,unfoldedCutoff]; ring
  have hx (x : ℝ) (h : x ∈ S) : 0 < x ∧ x ≤ T := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    exact (mem_cutoff.mp hz).2
  have hkey (x : ℝ) (h : x ∈ S) : key x < B := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hx x h).2 hL.le).trans_eq hDT) hR.le
  have hpos (x y : ℝ) : 0 ≤ f x y := by dsimp [f]; split <;> norm_num
  have hpair (x : ℝ) (hxS : x ∈ S) (y : ℝ) (_ : y ∈ S) (hxy : key x=key y) (hlt : x<y) :
      1 ≤ f x y := by
    have hx' : (key x:ℝ) ≤ L*x/R :=
      Nat.floor_le (div_nonneg (mul_nonneg hL.le (hx x hxS).1.le) hR.le)
    have hy' : L*y/R < (key y:ℝ)+1 := Nat.lt_floor_add_one _
    rw [← hxy] at hy'
    have hh : L*(y-x)/R ≤ 1 := by
      rw [mul_sub,sub_div]
      linarith only [hx',hy']
    have hb := (div_le_iff₀ hR).mp hh
    simp only [f,if_pos (show 0 < L*(y-x) ∧ L*(y-x) ≤ R from
      ⟨mul_pos hL (sub_pos.mpr hlt),by simpa only [one_mul] using hb⟩),le_rfl]
  have hp := cell_packing_bound S key B k hkey f hpos hpair
  have hs : (∑ x ∈ S, ∑ y ∈ S, f x y) ≤
      ∑ i : Copies T, ∑ j : Copies T, f (copyOrdinate T i) (copyOrdinate T j) := by
    calc _ ≤ ∑ x ∈ S, ∑ j : Copies T, f x (copyOrdinate T j) :=
           Finset.sum_le_sum fun x _ => sum_distinct_ordinates_le_copies T (f x) (hpos x)
         _ ≤ _ := sum_distinct_ordinates_le_copies T (fun x => ∑ j : Copies T, f x (copyOrdinate T j))
           (fun x => Finset.sum_nonneg (fun j _ => hpos x (copyOrdinate T j)))
  change _ ≤ D * ((∑ i : Copies T, ∑ j : Copies T, f (copyOrdinate T i) (copyOrdinate T j))/D)
  rw [mul_comm D,div_mul_cancel₀ _ hD.ne']
  simpa only [B,Nat.cast_add,Nat.cast_one] using hp.trans hs

/-- The inverse normalization of the actual zero counts tends to zero. -/
theorem unfoldedCutoff_inv_tendsto_zero :
    Tendsto (fun T : ℝ => (unfoldedCutoff T)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).mul
    (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop)
  have hmain : Tendsto (fun T : ℝ => (2 * Real.pi) * (T⁻¹ * (Real.log T)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using h.const_mul (2 * Real.pi)
  apply hmain.congr'
  apply Eventually.of_forall
  intro T
  change (2 * Real.pi) * (T⁻¹ * (Real.log T)⁻¹) = (T * Real.log T / (2 * Real.pi))⁻¹
  rw [inv_div, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Any cumulative distinct-ordinate lower fraction gives a quantitative
unconditional-in-that-fraction bound at each fixed positive gap width. -/
theorem eventually_microscopic_gap_uniform_lower {κ : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) (k : ℕ)
    {z : ℝ} (hz : z < (k:ℝ)*κ) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 < R → z - (k:ℝ)*(k+1)/(2*R) < positiveGapMass T R := by
  let b := (k:ℝ)*(k+1)/2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let η := ((k:ℝ)*κ-z)/(k+1)/2
  have hgap : 0 < (k:ℝ)*κ-z := sub_pos.mpr hz
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : ((k:ℝ)+1)*η=((k:ℝ)*κ-z)/2 := by
    dsimp [η]
    field_simp [show (k:ℝ)+1 ≠ 0 by positivity]
  have htarget : z < (k:ℝ)*(κ-η) := by linarith only [hηeq,hη,hgap]
  obtain ⟨t,hfrac⟩ := hκ η hη
  have hi := unfoldedCutoff_inv_tendsto_zero
  have hl := (tendsto_count_div_mainTerm.const_mul ((k:ℝ)*(κ-η))).sub (hi.const_mul b)
  have htop : z < (k:ℝ)*(κ-η)*1-b*0 := by simpa using htarget
  filter_upwards [eventually_ge_atTop t,eventually_gt_atTop (1:ℝ),
    hl.eventually (lt_mem_nhds htop)] with T ht hT hs R hR
  let D := unfoldedCutoff T
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hcard := hfrac T ht
  have hfl : (⌊D/R⌋₊:ℝ) ≤ D/R := Nat.floor_le (div_nonneg hD.le hR.le)
  have hpa := microscopic_gap_packing_bound hT hR k
  change (k:ℝ)*(distinctOrdinates T).card - ((⌊D/R⌋₊:ℝ)+1)*b ≤ D*positiveGapMass T R at hpa
  change z < (k:ℝ)*(κ-η)*((Ncount 0 T:ℝ)/D) - b*D⁻¹ at hs
  have hshift : (k:ℝ)*(k+1)/(2*R)=b/R := by dsimp [b]; ring
  rw [hshift]
  apply (sub_lt_sub_right hs (b/R)).trans_le
  have hc := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg k : 0 ≤ (k:ℝ))
  have hf := mul_le_mul_of_nonneg_right (add_le_add_right hfl 1) hb
  have hbound : (k:ℝ)*((κ-η)*(Ncount 0 T:ℝ)) - (D/R+1)*b ≤ D*positiveGapMass T R := by
    linarith only [hc,hf,hpa]
  calc _ = ((k:ℝ)*((κ-η)*(Ncount 0 T:ℝ)) - (D/R+1)*b)/D := by
             field_simp [hD.ne',hR.ne'] <;> ring
       _ ≤ _ := (div_le_iff₀ hD).mpr (by simpa only [mul_comm D] using hbound)

/-- Specialization of the simultaneous packing bound to any fixed
positive microscopic width. -/
theorem eventually_microscopic_gap_ge_of_distinct_fraction {κ : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) {R : ℝ} (hR : 0 < R) (k : ℕ)
    {z : ℝ} (hz : z < (k : ℝ) * κ - (k : ℝ) * (k + 1) / (2 * R)) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T R := by
  have hs := eventually_microscopic_gap_uniform_lower hκ k (z := z+(k:ℝ)*(k+1)/(2*R))
    (by linarith only [hz])
  filter_upwards [hs] with T hT
  simpa only [add_sub_cancel_right] using hT R hR

/-- Actual microscopic strict-positive gaps at any fixed width satisfy the
Montgomery–Taylor packing lower bound, with all analytic multiplicities and
all off-critical zeros included in the observed statistic. -/
theorem eventually_microscopic_gap_ge_montgomeryTaylor {R : ℝ} (hR : 0 < R) (k : ℕ)
    {z : ℝ} (hz : z < (k : ℝ) * ThmD.HD 1 - (k : ℝ) * (k + 1) / (2 * R)) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T R :=
  eventually_microscopic_gap_ge_of_distinct_fraction
    montgomeryTaylor_distinctCriticalProportion.distinct_ordinates hR k hz

/-- Optimizing the integer occupancy bound gives a uniform formula in the
chosen fixed width. The fractional-part remainder is nonnegative. -/
theorem eventually_microscopic_gap_affine_of_distinct_fraction {κ R z : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) (hκ₀ : 0 ≤ κ) (hR : 0 < R)
    (hz : z < κ ^ 2 * R / 2 - κ / 2) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T R := by
  let k := ⌊κ*R⌋₊
  let δ := κ*R - (k:ℝ)
  have hδ₀ : 0 ≤ δ := sub_nonneg.mpr (Nat.floor_le (mul_nonneg hκ₀ hR.le))
  have hδ₁ : δ ≤ 1 := by
    dsimp [δ,k]
    linarith only [Nat.lt_floor_add_one (κ*R)]
  have hrest : 0 ≤ δ*(1-δ)/(2*R) :=
    div_nonneg (mul_nonneg hδ₀ (sub_nonneg.mpr hδ₁)) (by positivity)
  have he : (k:ℝ)*κ - (k:ℝ)*(k+1)/(2*R) =
      κ^2*R/2 - κ/2 + δ*(1-δ)/(2*R) := by
    dsimp only [δ]
    field_simp [hR.ne']
    ring
  apply eventually_microscopic_gap_ge_of_distinct_fraction hκ hR k
  rw [he]
  exact hz.trans_le (le_add_of_nonneg_right hrest)

/-- A directed rational lower bound for the Montgomery–Taylor constant,
using a sine Taylor remainder also at half the angle to upper-bound the
cosine by the exact double-angle formula. -/
theorem montgomeryTaylor_fraction_ge_305_div_457 : (305/457 : ℝ) ≤ ThmD.HD 1 := by
  let x := (Real.sqrt 2)⁻¹
  let y := x/2
  have hx : 0 < x := by dsimp [x]; positivity
  have hx₂ : x^2 = 1/2 := by
    dsimp [x]
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hx1 : x ≤ 1 := by nlinarith only [hx₂,sq_nonneg (x-1)]
  have hy : 0 < y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by dsimp [y]; linarith only [hx1]
  have hy₂ : y^2 = 1/8 := by dsimp [y]; nlinarith only [hx₂]
  have hs (v q : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hsq : v^2=q) :
      v*(1-q/6-q^2/100) ≤ Real.sin v := by
    have h := (abs_le.mp (Real.sin_bound (x := v) (by simpa only [abs_of_pos hv] using hv1))).1
    rw [abs_of_pos hv,show v^3=v*q by rw [← hsq]; ring,
      show v^5=v*q^2 by rw [← hsq]; ring] at h
    linarith only [h]
  have hsinx : (914/1000:ℝ)*x ≤ Real.sin x := by
    nlinarith only [hs x (1/2) hx hx1 hx₂,hx.le]
  have hsiny : (979/1000:ℝ)*y ≤ Real.sin y := by
    nlinarith only [hs y (1/8) hy hy1 hy₂,hy.le]
  have hsiny₂ := sq_le_sq₀ (show 0 ≤ (979/1000:ℝ)*y by positivity)
    ((show 0 ≤ (979/1000:ℝ)*y by positivity).trans hsiny) |>.mpr hsiny
  have hcos : Real.cos x ≤ 761/1000 := by
    have hd := Real.cos_two_mul y
    rw [show 2*y=x by dsimp [y]; ring] at hd
    nlinarith only [hd,Real.sin_sq_add_cos_sq y,hsiny₂,hy₂]
  have hsinpos : 0 < Real.sin x :=
    (mul_pos (by norm_num : (0:ℝ)<914/1000) hx).trans_le hsinx
  have hrat : x*(Real.cos x / Real.sin x) ≤ 761/914 := by
    rw [← mul_div_assoc,div_le_iff₀ hsinpos]
    nlinarith only [mul_le_mul_of_nonneg_left hcos hx.le,hsinx]
  rw [ThmD.HD_one]
  change 305/457 ≤ 3/2 - x*(Real.cos x/Real.sin x)
  linarith only [hrat]

/-- At the fixed unfolded width 3/2 the normalized actual strict positive-gap
count is eventually larger than every real number below 1/1371. -/
theorem eventually_microscopic_gap_three_halves {z : ℝ} (hz : z < 1 / 1371) :
    ∀ᶠ T : ℝ in atTop, z < positiveGapMass T (3/2) := by
  apply eventually_microscopic_gap_ge_montgomeryTaylor (by norm_num : (0:ℝ) < 3/2) 1
  norm_num
  linarith only [hz,montgomeryTaylor_fraction_ge_305_div_457]

/-- At the fixed unfolded width two the normalized actual strict positive-gap
count eventually exceeds one sixth. -/
theorem eventually_microscopic_gap_two_gt_one_sixth :
    ∀ᶠ T : ℝ in atTop, 1/6 < positiveGapMass T 2 := by
  apply eventually_microscopic_gap_ge_montgomeryTaylor (by norm_num : (0:ℝ) < 2) 1
  norm_num
  linarith only [montgomeryTaylor_fraction_ge_305_div_457]

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_microscopic_gap_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_microscopic_gap_three_halves

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_microscopic_gap_two_gt_one_sixth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_microscopic_gap_two_gt_one_sixth

end RiemannResearch.Analysis.MontgomeryPositiveGap

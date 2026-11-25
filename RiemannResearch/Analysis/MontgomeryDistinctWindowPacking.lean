import RiemannResearch.Analysis.MontgomeryMovingGapPacking
import RiemannResearch.Analysis.ZeroDPPWindowLattice

/-! # Distinct-height window occupancy and the actual positive-gap primitive

The complete strict-positive-gap triangle of the actual zero copies splits
into a linear integer-occupancy bound, a nonnegative lattice remainder for
the distinct ordinates, and the nonnegative contribution from their analytic
multiplicities. Equal-ordinate pairs cancel exactly.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open OrdinateWindowVariance OrdinateCollisionCertificate

private def distinctTriangleKernel (h x y : ℝ) : ℝ :=
  if x=y then 0 else max (h-|x-y|) 0

/-- The excess triangular weight of noncoincident copies over the weight of
one representative of each distinct height. -/
def multiplicityOffDiagonalTriangleExcess (T h : ℝ) : ℝ :=
  (∑ i : Copies T, ∑ j : Copies T, distinctTriangleKernel h (copyOrdinate T i) (copyOrdinate T j)) -
    ∑ x ∈ distinctOrdinates T, ∑ y ∈ distinctOrdinates T, distinctTriangleKernel h x y

theorem multiplicityOffDiagonalTriangleExcess_nonneg (T h : ℝ) :
    0 ≤ multiplicityOffDiagonalTriangleExcess T h := by
  have hp (x y : ℝ) : 0 ≤ distinctTriangleKernel h x y := by
    unfold distinctTriangleKernel
    split <;> simp
  apply sub_nonneg.mpr
  calc
    _ ≤ ∑ x ∈ distinctOrdinates T, ∑ j : Copies T,
          distinctTriangleKernel h x (copyOrdinate T j) :=
      Finset.sum_le_sum fun x _ => sum_distinct_ordinates_le_copies T _ (hp x)
    _ ≤ _ := sum_distinct_ordinates_le_copies T _ (fun x => Finset.sum_nonneg (fun j _ =>
      hp x (copyOrdinate T j)))

/-- Exact nonnegative lattice remainder for the integer count of distinct
ordinates in the translated windows. -/
def distinctWindowLatticeExcess (T h shift : ℝ) (k : ℕ) : ℝ :=
  let W := windowCount (distinctOrdinates T) (fun x => x+shift) (T+shift) h
  ∫ t : ℝ, W t ^ 2 - (2*(k:ℝ)+1)*W t + (k:ℝ)*(k+1)*pulse 0 (T+shift) t

theorem distinctWindowLatticeExcess_nonneg (T h shift : ℝ) (k : ℕ) :
    0 ≤ distinctWindowLatticeExcess T h shift k := by
  classical
  unfold distinctWindowLatticeExcess
  apply integral_nonneg
  intro t
  let W := windowCount (distinctOrdinates T) (fun x => x+shift) (T+shift) h
  change 0 ≤ W t^2-(2*(k:ℝ)+1)*W t+(k:ℝ)*(k+1)*pulse 0 (T+shift) t
  by_cases ht : t ∈ Ioc (0:ℝ) (T+shift)
  · have hPulse : pulse 0 (T+shift) t = 1 := Set.indicator_of_mem ht _
    let n := ((distinctOrdinates T).filter fun x => t ∈ Ioc (max 0 (x+shift-h)) (min (T+shift) (x+shift))).card
    have hW : W t = (n:ℝ) := by
      simp [W,windowCount,windowPulse,pulse,Set.indicator,n,Finset.sum_boole]
    rw [hPulse,hW]
    have hprod : 0 ≤ ((n:ℝ)-k)*((n:ℝ)-k-1) := by
      by_cases h : n ≤ k
      · have hc : (n:ℝ) ≤ k := by exact_mod_cast h
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hc) (by linarith)
      · have hc : (k:ℝ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
        exact mul_nonneg (by linarith) (by linarith)
    nlinarith only [hprod]
  · have hPulse : pulse 0 (T+shift) t = 0 := Set.indicator_of_notMem ht _
    have hW := windowCount_mul_support (distinctOrdinates T) (fun x => x+shift) (T+shift) h t
    change W t * pulse 0 (T+shift) t = W t at hW
    rw [hPulse,mul_zero] at hW
    rw [← hW,hPulse]
    norm_num

private theorem triangle_split (h x y : ℝ) (hh : 0 ≤ h) :
    max (h-|x-y|) 0 = (if x=y then h else 0) + distinctTriangleKernel h x y := by
  by_cases he : x=y
  · simp [he,distinctTriangleKernel,max_eq_left hh]
  · simp [he,distinctTriangleKernel]

/-- At supported physical widths, the actual primitive has an exact signed
decomposition with two nonnegative remainders. The diagonal of repeated
ordinates drops out before the integer occupancy bound is taken. -/
theorem integrated_gap_distinct_lattice_shift_exact {T R shift : ℝ} (hT : 1 < T) (hR : 0 ≤ R)
    (hshift : 0 ≤ shift)
    (hs : ∀ x ∈ distinctOrdinates T, R/(Real.log T/(2*Real.pi)) ≤ x+shift ∧ x+shift ≤ T+shift) (k : ℕ) :
    let D := unfoldedCutoff T
    let h := R/(Real.log T/(2*Real.pi))
    2*(∫ u in (0:ℝ)..R, positiveGapMass T u) =
      2*(k:ℝ)*R*((distinctOrdinates T).card:ℝ)/D - (k:ℝ)*(k+1)*(1+shift/T) +
        distinctWindowLatticeExcess T h shift k/T + multiplicityOffDiagonalTriangleExcess T h/T := by
  classical
  let L := Real.log T/(2*Real.pi)
  let D := unfoldedCutoff T
  let h := R/L
  let S := distinctOrdinates T
  let W := windowCount S (fun x => x+shift) (T+shift) h
  let X := ∑ x ∈ S, ∑ y ∈ S, distinctTriangleKernel h x y
  let Y := ∑ i : Copies T, ∑ j : Copies T, distinctTriangleKernel h (copyOrdinate T i) (copyOrdinate T j)
  let C := (actualCollision T : ℝ)
  let M := (S.card:ℝ)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hh : 0 ≤ h := div_nonneg hR hL.le
  have ht := zero_lt_one.trans hT
  have hD : 0 < D := div_pos (mul_pos ht (Real.log_pos hT)) (by positivity)
  have hm : (∫ t : ℝ, W t) = M*h := integral_windowCount_of_supported S (fun x => x+shift) (T+shift) h hh hs
  have hm₂ : (∫ t : ℝ, W t^2) = M*h + X := by
    rw [integral_windowCount_sq_of_supported S (fun x => x+shift) (T+shift) h hs]
    simp_rw [add_sub_add_right_eq_sub,triangle_split h _ _ hh,Finset.sum_add_distrib]
    have heq : (∑ x ∈ S, ∑ y ∈ S, if x=y then h else 0) = M*h := by
      have hr (x : ℝ) (hx : x ∈ S) : (∑ y ∈ S, if x=y then h else 0) = h := by
        exact (Finset.sum_ite_eq S x (fun _ => h)).trans (if_pos hx)
      rw [Finset.sum_congr rfl hr]
      simp [M]
    rw [heq]
  have hlocal : distinctWindowLatticeExcess T h shift k =
      X - 2*(k:ℝ)*M*h+(k:ℝ)*(k+1)*(T+shift) := by
    have hw : Integrable W := windowCount_integrable S (fun x => x+shift) (T+shift) h
    have hw₂ : Integrable (fun t : ℝ => W t^2) := windowCount_sq_integrable S (fun x => x+shift) (T+shift) h
    unfold distinctWindowLatticeExcess
    change (∫ t : ℝ, W t^2-(2*(k:ℝ)+1)*W t+(k:ℝ)*(k+1)*pulse 0 (T+shift) t) = _
    have hsub : Integrable (fun t : ℝ => W t^2-(2*(k:ℝ)+1)*W t) := hw₂.sub (hw.const_mul _)
    rw [integral_add hsub ((pulse_integrable 0 (T+shift)).const_mul ((k:ℝ)*(k+1))),
      integral_sub hw₂ (hw.const_mul (2*(k:ℝ)+1)),integral_const_mul,integral_const_mul,integral_pulse,
      sub_zero,max_eq_left (by linarith only [ht,hshift] : 0 ≤ T+shift),hm,hm₂]
    ring
  have hdiag : (∑ i : Copies T, ∑ j : Copies T, if copyOrdinate T i=copyOrdinate T j then h else 0) =
      h*C := by
    dsimp only [C,actualCollision,occurrenceCollision]
    simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (if copyOrdinate T i=copyOrdinate T j then h else 0) =
      h*(if copyOrdinate T i=copyOrdinate T j then 1 else 0)
    split <;> simp_all
  have hraw : actualPhysicalTriangleEnergy T h = (h*C + Y)/T := by
    change (∑ i : Copies T, ∑ j : Copies T, max (h-|copyOrdinate T i-copyOrdinate T j|) 0)/T = _
    simp_rw [triangle_split h _ _ hh,Finset.sum_add_distrib]
    rw [hdiag]
  have htri := physicalTriangle_eq_collision_add_positive_gaps hT hR
  change actualPhysicalTriangleEnergy T h = R*(C/D) + 2*(∫ u in (0:ℝ)..R, positiveGapMass T u) at htri
  rw [hraw] at htri
  have hscale : R/D = h/T := by
    dsimp only [D,unfoldedCutoff,h,L]
    field_simp [ht.ne',(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring
  change 2*(∫ u in (0:ℝ)..R, positiveGapMass T u) =
    2*(k:ℝ)*R*M/D-(k:ℝ)*(k+1)*(1+shift/T)+distinctWindowLatticeExcess T h shift k/T+(Y-X)/T
  rw [hlocal]
  have hc : R*(C/D)=h*C/T := by
    calc
      _ = (R/D)*C := by ring
      _ = _ := by rw [hscale]; ring
  have hmain : 2*(k:ℝ)*R*M/D=2*(k:ℝ)*M*h/T := by
    calc _ = (2*(k:ℝ)*M)*(R/D) := by ring
         _ = _ := by rw [hscale]; ring
  rw [hmain]
  rw [hc] at htri
  have heq : (k:ℝ)*(k+1)*(T+shift)/T=(k:ℝ)*(k+1)*(1+shift/T) := by
    field_simp [ht.ne'] <;> ring
  linear_combination -htri - heq

/-- On supported physical widths no extension of the observation interval
is needed and the finite boundary-length charge vanishes. -/
theorem integrated_gap_distinct_lattice_exact {T R : ℝ} (hT : 1 < T) (hR : 0 ≤ R)
    (hs : ∀ x ∈ distinctOrdinates T, R/(Real.log T/(2*Real.pi)) ≤ x ∧ x ≤ T) (k : ℕ) :
    let D := unfoldedCutoff T
    let h := R/(Real.log T/(2*Real.pi))
    2*(∫ u in (0:ℝ)..R, positiveGapMass T u) =
      2*(k:ℝ)*R*((distinctOrdinates T).card:ℝ)/D - (k:ℝ)*(k+1) +
        distinctWindowLatticeExcess T h 0 k/T + multiplicityOffDiagonalTriangleExcess T h/T := by
  simpa only [zero_div,add_zero,mul_one] using
    integrated_gap_distinct_lattice_shift_exact hT hR (shift := 0) (by norm_num)
      (by simpa only [add_zero] using hs) k

/-- Extending the observation on the left by one physical window length
gives a finite inequality for all widths, including growing widths. -/
theorem integrated_gap_distinct_lattice_all_widths {T R : ℝ} (hT : 1 < T) (hR : 0 ≤ R) (k : ℕ) :
    let D := unfoldedCutoff T
    2*(k:ℝ)*R*((distinctOrdinates T).card:ℝ)/D - (k:ℝ)*(k+1)*(1+R/D) ≤
      2*(∫ u in (0:ℝ)..R, positiveGapMass T u) := by
  let h := R/(Real.log T/(2*Real.pi))
  have hh : 0 ≤ h := div_nonneg hR (div_nonneg (Real.log_pos hT).le (by positivity))
  have ht := zero_lt_one.trans hT
  have hs (x : ℝ) (hx : x ∈ distinctOrdinates T) : h ≤ x+h ∧ x+h ≤ T+h := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hv := (mem_cutoff.mp hz).2
    constructor <;> linarith only [hv.1,hv.2]
  have hid := integrated_gap_distinct_lattice_shift_exact hT hR hh hs k
  dsimp only at hid ⊢
  have hscale : R/unfoldedCutoff T=h/T := by
    dsimp only [unfoldedCutoff,h]
    field_simp [ht.ne',(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring
  rw [hscale,hid]
  exact (le_add_of_nonneg_right (div_nonneg (distinctWindowLatticeExcess_nonneg T _ h k) ht.le)).trans
    (le_add_of_nonneg_right (div_nonneg (multiplicityOffDiagonalTriangleExcess_nonneg T _) ht.le))

/-- Optimizing the translated integer count gives a finite quadratic bound
on the integrated strict-gap statistic at every observation width. -/
theorem integrated_gap_quadratic_lower {T R : ℝ} (hT : 1 < T) (hR : 0 ≤ R) :
    let D := unfoldedCutoff T
    let M := ((distinctOrdinates T).card:ℝ)
    (R*(M/D))^2/(1+R/D)-R*(M/D) ≤ 2*(∫ u in (0:ℝ)..R, positiveGapMass T u) := by
  let D := unfoldedCutoff T
  let M := ((distinctOrdinates T).card:ℝ)
  let m := R*(M/D)
  let A := 1+R/D
  let k := ⌊m/A⌋₊
  let δ := m/A-(k:ℝ)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hm : 0 ≤ m := mul_nonneg hR (div_nonneg hM hD.le)
  have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hR hD.le)
  have hd₀ : 0 ≤ δ := sub_nonneg.mpr (Nat.floor_le (div_nonneg hm hA.le))
  have hd₁ : δ ≤ 1 := by dsimp only [δ,k]; linarith only [Nat.lt_floor_add_one (m/A)]
  have hcorr := mul_nonneg (mul_nonneg hA.le hd₀) (sub_nonneg.mpr hd₁)
  have he : 2*(k:ℝ)*m-(k:ℝ)*(k+1)*A=m^2/A-m+A*δ*(1-δ) := by
    dsimp only [δ]
    field_simp [hA.ne'] <;> ring
  have h := integrated_gap_distinct_lattice_all_widths hT hR k
  change 2*(k:ℝ)*R*M/D-(k:ℝ)*(k+1)*A ≤ _ at h
  rw [show 2*(k:ℝ)*R*M/D=2*(k:ℝ)*m by dsimp only [m]; ring,he] at h
  change m^2/A-m ≤ _
  linarith only [hcorr,h]

/-- Uniform lower estimate for the actual positive-gap primitive over each
bounded width interval, retaining every distinct ordinate and no unproved
estimate of the multiplicity diagonal. -/
theorem eventually_integrated_gap_distinct_lattice_lower (B : ℝ) (k : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc (0:ℝ) B,
      2*(k:ℝ)*R*((distinctOrdinates T).card:ℝ)/(unfoldedCutoff T) - (k:ℝ)*(k+1) ≤
        2*(∫ u in (0:ℝ)..R, positiveGapMass T u) := by
  filter_upwards [ZeroDPPCorrelation.eventually_supported_width B,eventually_gt_atTop (1:ℝ)]
    with T hsupport hT R hR
  obtain ⟨_,hw⟩ := hsupport R hR.1 hR.2
  have hs (x : ℝ) (hx : x ∈ distinctOrdinates T) :
      R/(Real.log T/(2*Real.pi)) ≤ x ∧ x ≤ T := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    let c : Copies T := ⟨⟨z,hz⟩,⟨0,multiplicity_pos hz⟩⟩
    exact ⟨hw c,(mem_cutoff.mp hz).2.2⟩
  rw [integrated_gap_distinct_lattice_exact hT hR.1 hs k]
  have ht := (zero_lt_one.trans hT).le
  exact (le_add_of_nonneg_right (div_nonneg (distinctWindowLatticeExcess_nonneg T _ 0 k) ht)).trans
    (le_add_of_nonneg_right (div_nonneg (multiplicityOffDiagonalTriangleExcess_nonneg T _) ht))

private theorem eventually_distinct_scaled_gt {κ q : ℝ}
    (hκ : CumulativeDistinctOrdinateProportion κ) (hq : q < κ) :
    ∀ᶠ T : ℝ in atTop, q < ((distinctOrdinates T).card:ℝ)/unfoldedCutoff T := by
  let δ := (κ-q)/2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hq)
  obtain ⟨t,ht⟩ := hκ δ hδ
  have hlim := tendsto_count_div_mainTerm.const_mul (κ-δ)
  have hl : q < (κ-δ)*1 := by dsimp [δ]; linarith only [hq]
  filter_upwards [hlim.eventually (lt_mem_nhds hl),eventually_ge_atTop t,
    eventually_gt_atTop (1:ℝ)] with T hratio hT hpos
  have hD : 0 < unfoldedCutoff T :=
    div_pos (mul_pos (zero_lt_one.trans hpos) (Real.log_pos hpos)) (by positivity)
  apply hratio.trans_le
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (ht T hT) hD.le

/-- Every strict lower approximation to the kernel-proved Montgomery–Taylor
fraction bounds all the actual positive-gap primitives on a bounded interval
at once. -/
theorem eventually_integrated_gap_montgomeryTaylor_uniform (B : ℝ) (k : ℕ) {q : ℝ}
    (hq : q < ThmD.HD 1) :
    ∀ᶠ T : ℝ in atTop, ∀ R ∈ Icc (0:ℝ) B,
      2*(k:ℝ)*R*q-(k:ℝ)*(k+1) ≤ 2*(∫ u in (0:ℝ)..R, positiveGapMass T u) := by
  filter_upwards [eventually_integrated_gap_distinct_lattice_lower B k,
    eventually_distinct_scaled_gt montgomeryTaylor_distinctCriticalProportion.distinct_ordinates hq]
    with T hT hfrac R hR
  apply le_trans _ (hT R hR)
  rw [mul_div_assoc]
  have hp : 0 ≤ 2*(k:ℝ)*R := mul_nonneg (by positivity) hR.1
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hfrac.le hp) _

/-- The actual strict-positive-gap primitive at width two is eventually
larger than one third. -/
theorem eventually_integrated_microscopic_gap_two_gt_one_third :
    ∀ᶠ T : ℝ in atTop, 1/3 < ∫ u in (0:ℝ)..2, positiveGapMass T u := by
  let q : ℝ := ((2/3:ℝ)+305/457)/2
  have hq : q < ThmD.HD 1 := lt_of_lt_of_le (by norm_num [q]) montgomeryTaylor_fraction_ge_305_div_457
  filter_upwards [eventually_integrated_gap_montgomeryTaylor_uniform 2 1 hq] with T hT
  have h := hT 2 ⟨by norm_num,le_rfl⟩
  norm_num [q] at h
  linarith only [h]

/-- The mean accumulated strict-gap mass on every escaping submacroscopic
width has lower coefficient HD(1)²/2, even below the logarithmic scale. -/
theorem eventually_moving_integrated_gap_lower_montgomeryTaylor
    (r : ℝ → ℝ) (hr : Tendsto r atTop atTop)
    (hscale : Tendsto (fun T : ℝ => r T/unfoldedCutoff T) atTop (𝓝 0)) {z : ℝ}
    (hz : z < (ThmD.HD 1)^2/2) :
    ∀ᶠ T : ℝ in atTop, z < (∫ u in (0:ℝ)..r T, positiveGapMass T u)/(r T)^2 := by
  apply eventually_moving_lower_of_distinct_quadratic
    (fun T R => (∫ u in (0:ℝ)..R, positiveGapMass T u)/R^2) _ _
    montgomeryTaylor_distinctCriticalProportion.distinct_ordinates
    ((by norm_num : (0:ℝ)<305/457).trans_le montgomeryTaylor_fraction_ge_305_div_457)
    r hr hscale hz
  · intro T R hT hR
    exact div_nonneg (intervalIntegral.integral_nonneg hR.le
      (fun _ _ => positiveGapMass_nonneg hT _)) (sq_nonneg _)
  · intro T R hT hR
    let D := unfoldedCutoff T
    let m := ((distinctOrdinates T).card:ℝ)/D
    let A := 1+R/D
    have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
    have hA : 0 < A := add_pos_of_pos_of_nonneg zero_lt_one (div_pos hR hD).le
    have hi := integrated_gap_quadratic_lower hT hR.le
    change (R*m)^2/A-R*m ≤ 2*(∫ u in (0:ℝ)..R, positiveGapMass T u) at hi
    change m^2/(2*A)-m/(2*R) ≤ _
    calc
      _ = ((R*m)^2/A-R*m)/(2*R^2) := by field_simp [hR.ne',hA.ne'] <;> ring
      _ ≤ (2*(∫ u in (0:ℝ)..R, positiveGapMass T u))/(2*R^2) :=
        div_le_div_of_nonneg_right hi (by positivity)
      _ = _ := by field_simp [hR.ne']

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.multiplicityOffDiagonalTriangleExcess_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms multiplicityOffDiagonalTriangleExcess_nonneg

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.distinctWindowLatticeExcess_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms distinctWindowLatticeExcess_nonneg

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.integrated_gap_distinct_lattice_shift_exact'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrated_gap_distinct_lattice_shift_exact

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.integrated_gap_distinct_lattice_exact'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrated_gap_distinct_lattice_exact

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.integrated_gap_distinct_lattice_all_widths'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrated_gap_distinct_lattice_all_widths

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.integrated_gap_quadratic_lower'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrated_gap_quadratic_lower

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_integrated_gap_distinct_lattice_lower'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_integrated_gap_distinct_lattice_lower

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_integrated_gap_montgomeryTaylor_uniform'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_integrated_gap_montgomeryTaylor_uniform

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_integrated_microscopic_gap_two_gt_one_third'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_integrated_microscopic_gap_two_gt_one_third

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_moving_integrated_gap_lower_montgomeryTaylor'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_moving_integrated_gap_lower_montgomeryTaylor

end RiemannResearch.Analysis.MontgomeryPositiveGap

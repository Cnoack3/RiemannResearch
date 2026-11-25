import RiemannResearch.Analysis.MontgomeryMicroscopicGapPacking
import Mathlib.Data.Finset.Max

/-! # Distinct heights supporting microscopic positive gaps

The packing lower bound is witnessed by many distinct base ordinates.
In a cell of width R, at most k heights have fewer than k strict forward
neighbors, and at most k have fewer than k strict backward neighbors.
This bounds the number of deficient rows even when one ordinate supports
many analytic zero occurrences.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

/-- Genuinely different partner heights within R unfolded units in the
chosen orientation. A true orientation looks forward from the base height. -/
def microscopicNeighborHeights (T R : ℝ) (forward : Bool) (x : ℝ) : Finset ℝ :=
  (distinctOrdinates T).filter fun y =>
    let d := Real.log T/(2*Real.pi) * (if forward then y-x else x-y)
    0 < d ∧ d ≤ R

/-- Distinct base ordinates with at least k distinct short-gap partners in
the specified direction. -/
def microscopicNeighborBases (T R : ℝ) (forward : Bool) (k : ℕ) : Finset ℝ :=
  (distinctOrdinates T).filter fun x => k ≤ (microscopicNeighborHeights T R forward x).card

/-- There are at most k deficient rows in each unfolded cell, even with
arbitrary coincidences elsewhere in the zero configuration. -/
theorem microscopicNeighborBases_packing {T R : ℝ} (hT : 1 < T) (hR : 0 < R)
    (forward : Bool) (k : ℕ) :
    (distinctOrdinates T).card ≤ (microscopicNeighborBases T R forward k).card +
      (⌊unfoldedCutoff T/R⌋₊+1)*k := by
  classical
  let S := distinctOrdinates T
  let L := Real.log T/(2*Real.pi)
  let D := unfoldedCutoff T
  let B := ⌊D/R⌋₊+1
  let key := fun x : ℝ => ⌊L*x/R⌋₊
  let bad := S.filter fun x => ¬ k ≤ (microscopicNeighborHeights T R forward x).card
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hDT : L*T=D := by dsimp [L,D,unfoldedCutoff]; ring
  have hx (x : ℝ) (h : x ∈ S) : 0 < x ∧ x ≤ T := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    exact (mem_cutoff.mp hz).2
  have hkey (x : ℝ) (h : x ∈ S) : key x < B := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hx x h).2 hL.le).trans_eq hDT) hR.le
  have hnear {x y : ℝ} (hxS : x ∈ S) (he : key x=key y) (hlt : x<y) :
      0 < L*(y-x) ∧ L*(y-x) ≤ R := by
    have hfloor : (key x:ℝ) ≤ L*x/R :=
      Nat.floor_le (div_nonneg (mul_nonneg hL.le (hx x hxS).1.le) hR.le)
    have hnext : L*y/R < (key y:ℝ)+1 := Nat.lt_floor_add_one _
    rw [← he] at hnext
    have hdiv : L*(y-x)/R ≤ 1 := by rw [mul_sub,sub_div]; linarith only [hfloor,hnext]
    exact ⟨mul_pos hL (sub_pos.mpr hlt),by simpa only [one_mul] using (div_le_iff₀ hR).mp hdiv⟩
  let A := fun j : ℕ => bad.filter fun x => key x=j
  have hc (j : ℕ) : (A j).card ≤ k := by
    by_cases hn : (A j).Nonempty
    · have hex : ∃ x ∈ A j, ∀ y ∈ A j, y ≠ x →
          y ∈ microscopicNeighborHeights T R forward x := by
        cases forward with
        | true =>
          let x := (A j).min' hn
          have hxA : x ∈ A j := Finset.min'_mem _ _
          refine ⟨x,hxA,?_⟩
          intro y hyA hy
          obtain ⟨hxB,hxj⟩ := Finset.mem_filter.mp hxA
          obtain ⟨hyB,hyj⟩ := Finset.mem_filter.mp hyA
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyB).1,
            hnear (Finset.mem_filter.mp hxB).1 (hxj.trans hyj.symm)
              ((Finset.min'_le (A j) y hyA).lt_of_ne hy.symm)⟩
        | false =>
          let x := (A j).max' hn
          have hxA : x ∈ A j := Finset.max'_mem _ _
          refine ⟨x,hxA,?_⟩
          intro y hyA hy
          obtain ⟨hxB,hxj⟩ := Finset.mem_filter.mp hxA
          obtain ⟨hyB,hyj⟩ := Finset.mem_filter.mp hyA
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyB).1,
            hnear (Finset.mem_filter.mp hyB).1 (hyj.trans hxj.symm)
              ((Finset.le_max' (A j) y hyA).lt_of_ne hy)⟩
      obtain ⟨x,hxA,hall⟩ := hex
      have hsub : (A j).erase x ⊆ microscopicNeighborHeights T R forward x :=
        fun y hy => hall y (Finset.mem_erase.mp hy).2 (Finset.mem_erase.mp hy).1
      have hsmall : (microscopicNeighborHeights T R forward x).card < k :=
        lt_of_not_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hxA).1).2
      have hsize := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hxA] at hsize
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have hm : ∀ x ∈ bad, key x ∈ Finset.range B := fun x hx =>
    Finset.mem_range.mpr (hkey x (Finset.mem_filter.mp hx).1)
  have hcount : (∑ j ∈ Finset.range B, (A j).card) = bad.card := by
    simpa only [A, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using
      (Finset.sum_fiberwise_of_maps_to hm (fun _ : ℝ => (1:ℕ)))
  have hbound := Finset.sum_le_sum (s := Finset.range B) (fun j _ => hc j)
  rw [hcount] at hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] at hbound
  have hpartition := Finset.card_filter_add_card_filter_not (s := S)
    (fun x => k ≤ (microscopicNeighborHeights T R forward x).card)
  change (microscopicNeighborBases T R forward k).card+bad.card=S.card at hpartition
  change S.card ≤ (microscopicNeighborBases T R forward k).card + B * k
  rw [← hpartition]
  exact Nat.add_le_add_left hbound _

private theorem eventually_scaled_neighbor_count_lower {R z : ℝ} (hR : 0 < R)
    (s : ℝ → ℕ) (k : ℕ)
    (hpacking : ∀ T : ℝ, 1 < T → (distinctOrdinates T).card ≤
      s T + (⌊unfoldedCutoff T/R⌋₊+1)*k)
    (hz : z < ThmD.HD 1 - (k:ℝ)/R) :
    ∀ᶠ T : ℝ in atTop, z < (s T:ℝ)/unfoldedCutoff T := by
  let κ := ThmD.HD 1
  let q := (z+(k:ℝ)/R+κ)/2
  have hq : q < κ := by dsimp only [q,κ]; linarith only [hz]
  let δ := κ-q
  have hδ : 0 < δ := sub_pos.mpr hq
  obtain ⟨t,ht⟩ := montgomeryTaylor_distinctCriticalProportion.distinct_ordinates δ hδ
  have hfrac := tendsto_count_div_mainTerm.const_mul q
  have hi := unfoldedCutoff_inv_tendsto_zero
  have hlim := ((hfrac.sub (hi.const_mul (k:ℝ))).sub_const ((k:ℝ)/R))
  have htar : z < q*1-(k:ℝ)*0-(k:ℝ)/R := by dsimp only [q,κ]; linarith only [hz]
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop t,hlim.eventually (lt_mem_nhds htar)]
    with T hT hot hZ
  let D := unfoldedCutoff T
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hn := ht T hot
  change (κ-δ)*(Ncount 0 T:ℝ) ≤ ((distinctOrdinates T).card:ℝ) at hn
  rw [show κ-δ=q by dsimp [δ]; ring] at hn
  have hc := hpacking T hT
  have hc' : ((distinctOrdinates T).card:ℝ) ≤ (s T:ℝ) +
      ((⌊D/R⌋₊:ℝ)+1)*(k:ℝ) := by exact_mod_cast hc
  have hf := mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hD.le hR.le)) (Nat.cast_nonneg k)
  apply hZ.trans_le
  change q*((Ncount 0 T:ℝ)/D)-(k:ℝ)*D⁻¹-(k:ℝ)/R ≤ _
  calc _ = (q*(Ncount 0 T:ℝ)-(D/R+1)*(k:ℝ))/D := by field_simp [hD.ne',hR.ne'] <;> ring
       _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hn,hc',hf]) hD.le

/-- Unconditional lower density of distinct base ordinates with k strict
distinct partners, at each fixed microscopic width in either direction. -/
theorem eventually_microscopicNeighborBases_lower {R z : ℝ} (hR : 0 < R)
    (forward : Bool) (k : ℕ) (hz : z < ThmD.HD 1 - (k:ℝ)/R) :
    ∀ᶠ T : ℝ in atTop, z < ((microscopicNeighborBases T R forward k).card:ℝ)/unfoldedCutoff T :=
  eventually_scaled_neighbor_count_lower hR _ k
    (fun _ hT => microscopicNeighborBases_packing hT hR forward k) hz

/-- Distinct heights with at least k strictly larger and at least k strictly
smaller distinct partners within R unfolded spacings. -/
def microscopicTwoSidedBases (T R : ℝ) (k : ℕ) : Finset ℝ :=
  microscopicNeighborBases T R true k ∩ microscopicNeighborBases T R false k

/-- The two directional packing bounds control the same distinct base heights
simultaneously. -/
theorem microscopicTwoSidedBases_packing {T R : ℝ} (hT : 1 < T) (hR : 0 < R) (k : ℕ) :
    (distinctOrdinates T).card ≤ (microscopicTwoSidedBases T R k).card +
      (⌊unfoldedCutoff T/R⌋₊+1)*(2*k) := by
  classical
  let a := microscopicNeighborBases T R true k
  let b := microscopicNeighborBases T R false k
  let n := (distinctOrdinates T).card
  let c := (⌊unfoldedCutoff T/R⌋₊+1)*k
  have ha : n ≤ a.card+c := microscopicNeighborBases_packing hT hR true k
  have hb : n ≤ b.card+c := microscopicNeighborBases_packing hT hR false k
  have sub : a ∪ b ⊆ distinctOrdinates T := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx <;> exact (Finset.mem_filter.mp hx).1
  have hsize : (a ∪ b).card ≤ n := Finset.card_le_card sub
  have h := Finset.card_union_add_card_inter a b
  have hc : (⌊unfoldedCutoff T/R⌋₊+1)*(2*k)=2*c := by dsimp only [c]; ring
  rw [hc]
  change n ≤ (a ∩ b).card+2*c
  omega

/-- A positive proportion of distinct central heights have k short-gap
partners on each side whenever the chosen width is greater than twice k
divided by the Montgomery–Taylor proportion. -/
theorem eventually_microscopicTwoSidedBases_lower {R z : ℝ} (hR : 0 < R)
    (k : ℕ) (hz : z < ThmD.HD 1 - 2*(k:ℝ)/R) :
    ∀ᶠ T : ℝ in atTop, z < ((microscopicTwoSidedBases T R k).card:ℝ)/unfoldedCutoff T := by
  apply eventually_scaled_neighbor_count_lower hR _ (2*k)
    (fun _ hT => microscopicTwoSidedBases_packing hT hR k)
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz

/-- At width 3/2, positive microscopic gaps are witnessed by a uniformly
positive proportion of distinct base heights, in either orientation. -/
theorem eventually_microscopicNeighborBases_three_halves (forward : Bool) {z : ℝ} (hz : z < 1/1371) :
    ∀ᶠ T : ℝ in atTop,
      z < ((microscopicNeighborBases T (3/2) forward 1).card:ℝ)/unfoldedCutoff T := by
  apply eventually_microscopicNeighborBases_lower (by norm_num) forward 1
  norm_num
  linarith only [hz,montgomeryTaylor_fraction_ge_305_div_457]

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.microscopicNeighborBases_packing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms microscopicNeighborBases_packing

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_microscopicNeighborBases_lower'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_microscopicNeighborBases_lower

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.microscopicTwoSidedBases_packing'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms microscopicTwoSidedBases_packing

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_microscopicTwoSidedBases_lower'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_microscopicTwoSidedBases_lower

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_microscopicNeighborBases_three_halves'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_microscopicNeighborBases_three_halves

end RiemannResearch.Analysis.MontgomeryPositiveGap

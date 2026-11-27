import RiemannResearch.Analysis.MontgomeryMicroscopicPacking
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.LinearCombination

/-! # A rational Montgomery–Taylor certificate for microscopic positive pair counts

Two alternating Taylor bounds certify the constant from Alpöge–Furman,
arXiv:2608.13637v2, Theorem A, in the repository's existing ThmD formula.
The finite occupancy inequality then applies to actual distinct ordinates.
-/
noncomputable section
open Filter Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

private theorem primitive_nonneg {f g : ℝ → ℝ} (hd : Differentiable ℝ f)
    (h0 : f 0 = 0) (hD : ∀ x, deriv f x = g x) (hg : ∀ x, 0 ≤ x → 0 ≤ g x) :
    ∀ x, 0 ≤ x → 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici _) hd.continuous.continuousOn hd.differentiableOn
      (fun x hx => (hD x).symm ▸ hg x (interior_subset hx))
  intro x hx
  simpa only [h0] using hm (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl) hx hx

private theorem taylor_at_positive :
    (∀ x : ℝ, 0 ≤ x → x - x^3/6 + x^5/120 - x^7/5040 ≤ Real.sin x) ∧
    (∀ x : ℝ, 0 ≤ x → Real.cos x ≤ 1-x^2/2+x^4/24-x^6/720+x^8/40320) := by
  have h3 (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.sin x - (x-x^3/6) :=
    sub_nonneg.mpr (Real.sin_ge_sub_cube hx)
  have h4 : ∀ x : ℝ, 0 ≤ x → 0 ≤ (1-x^2/2+x^4/24)-Real.cos x := by
    apply primitive_nonneg (f := fun x : ℝ => (1-x^2/2+x^4/24)-Real.cos x)
      (g := fun x : ℝ => Real.sin x - (x-x^3/6))
      (by fun_prop) (by norm_num) _ h3
    intro x
    simp (disch := fun_prop)
    ring
  have h5 : ∀ x : ℝ, 0 ≤ x → 0 ≤ (x-x^3/6+x^5/120)-Real.sin x := by
    apply primitive_nonneg (f := fun x : ℝ => (x-x^3/6+x^5/120)-Real.sin x)
      (g := fun x : ℝ => (1-x^2/2+x^4/24)-Real.cos x)
      (by fun_prop) (by norm_num) _ h4
    intro x
    simp (disch := fun_prop)
    ring
  have h6 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.cos x-(1-x^2/2+x^4/24-x^6/720) := by
    apply primitive_nonneg (f := fun x : ℝ => Real.cos x-(1-x^2/2+x^4/24-x^6/720))
      (g := fun x : ℝ => (x-x^3/6+x^5/120)-Real.sin x)
      (by fun_prop) (by norm_num) _ h5
    intro x
    simp (disch := fun_prop)
    ring
  have h7 : ∀ x : ℝ, 0 ≤ x → 0 ≤ Real.sin x-(x-x^3/6+x^5/120-x^7/5040) := by
    apply primitive_nonneg (f := fun x : ℝ => Real.sin x-(x-x^3/6+x^5/120-x^7/5040))
      (g := fun x : ℝ => Real.cos x-(1-x^2/2+x^4/24-x^6/720))
      (by fun_prop) (by norm_num) _ h6
    intro x
    simp (disch := fun_prop)
    ring
  have h8 : ∀ x : ℝ, 0 ≤ x → 0 ≤ (1-x^2/2+x^4/24-x^6/720+x^8/40320)-Real.cos x := by
    apply primitive_nonneg (f := fun x : ℝ => (1-x^2/2+x^4/24-x^6/720+x^8/40320)-Real.cos x)
      (g := fun x : ℝ => Real.sin x-(x-x^3/6+x^5/120-x^7/5040))
      (by fun_prop) (by norm_num) _ h7
    intro x
    simp (disch := fun_prop)
    ring
  exact ⟨fun x hx => sub_nonneg.mp (h7 x hx), fun x hx => sub_nonneg.mp (h8 x hx)⟩

/-- An exact rational certificate for the published Montgomery–Taylor constant. -/
private theorem fraction_certificate :
    (1345001/2000000 : ℝ) <
      3/2 - (Real.sqrt 2)⁻¹ * (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) := by
  let x := (Real.sqrt 2)⁻¹
  change 1345001/2000000 < 3/2 - x*(Real.cos x / Real.sin x)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx2 : x^2 = 1/2 := by
    dsimp [x]; rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hs := taylor_at_positive.1 x hx.le
  have hc := taylor_at_positive.2 x hx.le
  have hl : (1-1/12+1/480-1/40320 : ℝ)*x ≤ Real.sin x := by
    calc
      _ = x*(1-x^2/6+(x^2)^2/120-(x^2)^3/5040) := by rw [hx2]; ring
      _ = x-x^3/6+x^5/120-x^7/5040 := by ring
      _ ≤ _ := hs
  have hu : Real.cos x ≤ (1-1/4+1/96-1/5760+1/645120 : ℝ) := by
    calc
      _ ≤ _ := hc
      _ = 1-x^2/2+(x^2)^2/24-(x^2)^3/720+(x^2)^4/40320 := by ring
      _ = _ := by rw [hx2]; norm_num
  have hspos : 0 < Real.sin x := (mul_pos (by norm_num) hx).trans_le hl
  have hlt : x * Real.cos x < (3/2-1345001/2000000)*Real.sin x := by
    nlinarith only [mul_le_mul_of_nonneg_left hu hx.le,
      mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 3/2-1345001/2000000), hx]
  rw [← mul_div_assoc]
  linarith only [(div_lt_iff₀ hspos).mpr hlt]

theorem montgomeryTaylor_fraction_gt_1345001_div_2000000 : (1345001/2000000 : ℝ) < ThmD.HD 1 := by
  rw [ThmD.HD_one]
  exact fraction_certificate

/-- A single unconditional estimate for varying test widths on any increasing
sequence of cutoffs. The limit q is in unfolded units. -/
theorem moving_strict_pair_density_lower {ι : Type*} {l : Filter ι}
    {T w : ι → ℝ} {q z : ℝ} (hT : Tendsto T l atTop) (hq : 0 < q)
    (hw : Tendsto (fun i => unfoldingScale (T i) * w i) l (𝓝 q))
    (hz : z < ThmD.HD 1 - 1/q) :
    ∀ᶠ i in l, z < physicalStrictPairs (T i) (w i) / unfoldedCutoff (T i) := by
  let b := (z+1/q+ThmD.HD 1)/2
  have hb : b < ThmD.HD 1 := by dsimp [b]; linarith
  have hzb : z < b-1/q := by dsimp [b]; linarith
  have hpack := eventually_microscopic_gap_uniform_lower
    montgomeryTaylor_distinctCriticalProportion.distinct_ordinates 1 (z := b)
    (by simpa only [Nat.cast_one,one_mul] using hb)
  have hlim := (tendsto_const_nhds (x := b)).sub ((tendsto_const_nhds (x := (1:ℝ))).div hw hq.ne')
  filter_upwards [hT.eventually hpack, hw.eventually (lt_mem_nhds hq),
    hlim.eventually (lt_mem_nhds hzb), hT.eventually (eventually_gt_atTop (1:ℝ))]
    with i hi hR hnear hcut
  rw [physicalStrictPairs_normalized hcut]
  apply hnear.trans
  have H := hi _ hR
  norm_num only [Nat.cast_one, one_mul, one_add_one_eq_two] at H
  have hs (x : ℝ) : 2/(2*x) = 1/x := by rw [div_mul_eq_div_div]; norm_num
  rw [hs] at H
  exact H

theorem microscopic_gap_two_gt_345001_div_2000000 :
    ∀ᶠ T : ℝ in atTop, 345001/2000000 < positiveGapMass T 2 := by
  apply eventually_microscopic_gap_ge_montgomeryTaylor (by norm_num : (0:ℝ) < 2) 1
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_1345001_div_2000000]

theorem microscopic_gap_three_halves_gt_35003_div_6000000 :
    ∀ᶠ T : ℝ in atTop, 35003/6000000 < positiveGapMass T (3/2) := by
  apply eventually_microscopic_gap_ge_montgomeryTaylor (by norm_num : (0:ℝ) < 3/2) 1
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_1345001_div_2000000]

end RiemannResearch.Analysis.MontgomeryPositiveGap

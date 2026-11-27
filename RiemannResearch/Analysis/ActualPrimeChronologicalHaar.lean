/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.InfiniteDiagonalFMZ
import RiemannResearch.Analysis.ActualConsecutiveOrdinates
import RiemannResearch.Analysis.OrdinateLagPhase

/-! # Diagonal Haar limits for genuine chronological prime-ordinate pairs

The unscaled height shift has vanishing average for lags o(log T).
Taking a smaller range omits the terminal pairs whose second ordinate
would lie outside the sample. Analytic zero multiplicity is retained. The ingredients are the
repository's multiplicity-weighted one-point Haar theorem, the Riemann–von Mangoldt count, and
the deterministic lag telescoping identity in OrdinateLagPhase.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open ActualZeroOrdinate CompactGaugeOrbitLaw

local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace (PrimeTorus × PrimeTorus) := borel _
local instance : BorelSpace (PrimeTorus × PrimeTorus) := ⟨rfl⟩

theorem continuous_phasePoint : Continuous phasePoint := by
  apply continuous_pi
  intro p
  unfold phasePoint
  fun_prop

theorem phasePoint_add (u v : ℝ) : phasePoint (u + v) = phasePoint u * phasePoint v := by
  funext p
  change Circle.exp (_ * (u + v)) = Circle.exp (_ * u) * Circle.exp (_ * v)
  rw [mul_add, Circle.exp_add]

@[simp] theorem phasePoint_zero : phasePoint 0 = 1 := by
  funext p
  simp [phasePoint]

private theorem flow_increment_bound (F : C(PrimeTorus × PrimeTorus, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : PrimeTorus, ∀ u : ℝ, 0 ≤ u →
      ‖F (z, z * phasePoint u) - F (z, z)‖ ≤ ε + C * u := by
  let H : C(ℝ × PrimeTorus, ℂ) :=
    ⟨fun x => F (x.2, x.2 * phasePoint x.1) - F (x.2, x.2),
      (F.continuous.comp (continuous_snd.prodMk (continuous_snd.mul (continuous_phasePoint.comp continuous_fst)))).sub
        (F.continuous.comp (continuous_snd.prodMk continuous_snd))⟩
  have h0 : H.curry 0 = 0 := by ext z; simp [H]
  have hh := (Metric.continuousAt_iff.mp (H.curry.continuous.continuousAt (x := (0 : ℝ)))) ε hε
  obtain ⟨δ, hδ, hd⟩ := hh
  let C := 2 * ‖F‖ / δ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z u hu
  by_cases h : u < δ
  · have hi := hd (show dist u 0 < δ by simpa [Real.dist_eq, abs_of_nonneg hu] using h)
    rw [h0, dist_zero_right] at hi
    have hz := (H.curry u).norm_coe_le_norm z
    change ‖F (z, z * phasePoint u) - F (z, z)‖ ≤ ‖H.curry u‖ at hz
    linarith only [hz, hi, mul_nonneg hC hu]
  · have hab := (norm_sub_le (F (z, z * phasePoint u)) (F (z, z))).trans
        (add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _))
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) hC
    have he : C * δ = 2 * ‖F‖ := by dsimp [C]; field_simp
    linarith only [hab, hm, he, hε]

/-- The mass is (N-ell)/N. When a lag skips beyond the list the sum is empty. -/
def chronologicalPairAverage (T : ℝ) (ell : ℕ) (F : C(PrimeTorus × PrimeTorus, ℂ)) : ℂ :=
  (∑ j ∈ Finset.range (Ncount 0 T - ell), F (phasePoint (cutoffOrdinate T j),
    phasePoint (cutoffOrdinate T (j + ell)))) / (Ncount 0 T : ℂ)

private theorem chronological_error_bound (T : ℝ) (hT : 1 ≤ T) (hN : 0 < Ncount 0 T)
    (ell : ℕ) (F : C(PrimeTorus × PrimeTorus, ℂ)) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hflow : ∀ z : PrimeTorus, ∀ u : ℝ, 0 ≤ u → ‖F (z, z * phasePoint u) - F (z, z)‖ ≤ ε + C * u) :
    ‖chronologicalPairAverage T ell F - ∫ z, F (z, z) ∂empiricalProbability T‖ ≤
      ε + (C + ‖F‖) * ((ell : ℝ) * T / (Ncount 0 T : ℝ)) := by
  let N := Ncount 0 T
  let J := N - ell
  let γ := cutoffOrdinate T
  let z := fun j => phasePoint (γ j)
  let g := fun j => F (z j, z j)
  have hm : J ≤ N := Nat.sub_le ..
  have htail : N - J ≤ ell := by dsimp [J]; omega
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht0 := (cutoffOrdinate_bounds hN).1
  have horb (j : ℕ) : z (j + ell) = z j * phasePoint (γ (j + ell) - γ j) := by
    simp only [z, ← phasePoint_add, add_sub_cancel]
  have hgap (j : ℕ) : 0 ≤ γ (j + ell) - γ j :=
    sub_nonneg.mpr (cutoffOrdinate_monotone T (Nat.le_add_right j ell))
  have hsum := OrdinateLagPhase.lag_gap_sum_le γ (cutoffOrdinate_monotone T) J ell
  have hsum' : (∑ j ∈ Finset.range J, (γ (j + ell) - γ j)) ≤ (ell : ℝ) * T :=
    hsum.trans (mul_le_mul_of_nonneg_left (by linarith only [cutoffOrdinate_le T (J + ell), ht0]) (Nat.cast_nonneg _))
  have herr : ‖∑ j ∈ Finset.range J, (F (z j, z (j + ell)) - g j)‖ ≤ (N : ℝ) * ε + C * ((ell : ℝ) * T) := by
    apply (_root_.norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ Finset.range J, (ε + C * (γ (j + ell) - γ j)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [horb]
        exact hflow _ _ (hgap j)
      _ = (J : ℝ) * ε + C * (∑ j ∈ Finset.range J, (γ (j + ell) - γ j)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hε)
        (mul_le_mul_of_nonneg_left hsum' hC)
  have hend : ‖∑ j ∈ Finset.range (N - J), g (J + j)‖ ≤ (ell : ℝ) * T * ‖F‖ := by
    apply (_root_.norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range (N - J), ‖F‖ := Finset.sum_le_sum fun _ _ => F.norm_coe_le_norm _
      _ = ((N - J : ℕ) : ℝ) * ‖F‖ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((show ((N - J : ℕ) : ℝ) ≤ (ell : ℝ) by exact_mod_cast htail).trans
          (by simpa using mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg ell))) (norm_nonneg _)
  have hs : (∑ j ∈ Finset.range N, g j) = (∑ j ∈ Finset.range J, g j) +
      ∑ j ∈ Finset.range (N - J), g (J + j) := by
    simpa only [Nat.add_sub_of_le hm] using Finset.sum_range_add g J (N - J)
  have he := integral_empiricalProbability T hN (fun z => F (z, z))
  rw [sum_eq_copies] at he
  change (∫ z, F (z, z) ∂empiricalProbability T) =
    (∑ c : Copies T, F (phasePoint (copyOrdinate T c), phasePoint (copyOrdinate T c))) / (N : ℂ) at he
  rw [← cutoffOrdinate_sum T (fun t => F (phasePoint t, phasePoint t))] at he
  rw [he]
  change ‖(∑ j ∈ Finset.range J, F (z j, z (j + ell))) / (N : ℂ) - (∑ j ∈ Finset.range N, g j) / (N : ℂ)‖ ≤ _
  rw [← sub_div, hs, ← sub_sub, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hN').mpr
  apply (norm_sub_le _ _).trans
  apply (add_le_add herr hend).trans_eq
  change _ = (ε + (C + ‖F‖) * ((ell : ℝ) * T / (N : ℝ))) * (N : ℝ)
  field_simp
  ring

theorem tendsto_lag_height_div_count (ell : ℝ → ℕ)
    (h : Tendsto (fun T => (ell T : ℝ) / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => (ell T : ℝ) * T / (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hn⟩ := exists_count_normalization
  have hz := h.div_const c
  simp only [zero_div] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T ht; positivity
  · filter_upwards [hn, eventually_gt_atTop (1 : ℝ), eventually_count_pos] with T hN hT hpos
    have hL := Real.log_pos hT
    have hT0 : 0 < T := by linarith
    have hN0 : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hpos
    change _ ≤ ((ell T : ℝ) / Real.log T) / c
    rw [div_div, div_le_div_iff₀ hN0 (mul_pos hL hc)]
    nlinarith only [mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg (ell T))]

/-- Every continuous observable on two infinite prime tori converges to its
diagonal Haar integral for genuine chronological lags o(log T). -/
theorem tendsto_chronologicalPairAverage (ell : ℝ → ℕ)
    (h : Tendsto (fun T => (ell T : ℝ) / Real.log T) atTop (𝓝 0))
    (F : C(PrimeTorus × PrimeTorus, ℂ)) :
    Tendsto (fun T => chronologicalPairAverage T (ell T) F) atTop (𝓝 (∫ x, F x ∂diagonalHaar)) := by
  let G : C(PrimeTorus, ℂ) := ⟨fun z => F (z, z), F.continuous.comp (continuous_id.prodMk continuous_id)⟩
  have hsingle := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    tendsto_primeHaar (ContinuousMap.equivBoundedOfCompact PrimeTorus ℂ G)
  change Tendsto (fun T => ∫ z, F (z, z) ∂empiricalProbability T) atTop (𝓝 (∫ z, F (z, z) ∂primeHaar)) at hsingle
  have hd : Tendsto (fun T => chronologicalPairAverage T (ell T) F -
      ∫ z, F (z, z) ∂empiricalProbability T) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨C, hC, hflow⟩ := flow_increment_bound F (half_pos hε)
    have hz := (tendsto_lag_height_div_count ell h).const_mul (C + ‖F‖)
    simp only [mul_zero] at hz
    filter_upwards [hz.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (1 : ℝ), eventually_count_pos]
      with T ht hT hN
    rw [dist_zero_right]
    have hi := chronological_error_bound T hT hN (ell T) F (half_pos hε).le hC hflow
    linarith only [hi, ht]
  rw [diagonalHaar_integral]
  simpa only [sub_add_cancel, zero_add] using hd.add hsingle

/--
info: 'RiemannResearch.Analysis.ActualInfinitePrimeTorus.tendsto_chronologicalPairAverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_chronologicalPairAverage

end RiemannResearch.Analysis.ActualInfinitePrimeTorus

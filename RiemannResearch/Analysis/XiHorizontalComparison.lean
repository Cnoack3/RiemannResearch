import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.XiOrderBridge
import RiemannResearch.Analysis.LiCriterionImport.Lc.XiZeros
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Horizontal comparison of the completed zeta function

Sondow and Dumitrescu, "A monotonicity property of Riemann's xi function
and a reformulation of the Riemann Hypothesis", arXiv:1005.1104, prove a
strict monotonicity criterion. We use its weak form and the multiplicity-aware
paired Hadamard product already present in the repository. Countability of the
zeros suffices for the converse even with a non-strict inequality.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.XiHorizontalComparison
open LiCriterion

private theorem norm_factor_le {z w ρ : ℂ} (hr : ρ ≠ 0)
    (ha : ρ.re ≤ z.re) (hab : z.re ≤ w.re) (hi : z.im = w.im) :
    ‖1 - z / ρ‖ ≤ ‖1 - w / ρ‖ := by
  have hdist : ‖ρ - z‖ ^ 2 ≤ ‖ρ - w‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, hi]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ha),
      sq_nonneg (w.re - z.re)]
  have hlo : ‖ρ - z‖ ≤ ‖ρ - w‖ := by
    nlinarith only [hdist, norm_nonneg (ρ - z), norm_nonneg (ρ - w)]
  rw [← div_self hr, ← sub_div, ← sub_div, norm_div, norm_div]
  exact div_le_div_of_nonneg_right hlo (norm_nonneg ρ)

/-- A common upper bound for the real parts of all nontrivial zeros gives
horizontal xi monotonicity throughout the half-plane starting there. -/
theorem norm_xi_le_of_zero_abscissae_le {a : ℝ}
    (hon : ∀ ρ : NontrivialZero, ρ.val.re ≤ a) {z w : ℂ}
    (ha : a ≤ z.re) (hab : z.re ≤ w.re) (hi : z.im = w.im) :
    ‖riemannXi z‖ ≤ ‖riemannXi w‖ := by
  classical
  have hfac (ρ : NontrivialZero) : ‖xiPairedLinearFactor ρ z‖ ≤ ‖xiPairedLinearFactor ρ w‖ := by
    rw [xiPairedLinearFactor, xiPairedLinearFactor, norm_mul, norm_mul]
    exact mul_le_mul (norm_factor_le ρ.ne_zero ((hon ρ).trans ha) hab hi)
      (norm_factor_le (pairedZero ρ).ne_zero ((hon _).trans ha) hab hi) (norm_nonneg _)
      (norm_nonneg _)
  have hg := xi_weighted_genus_one_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one
  have hmult := summable_inv_norm_sq_zeros_with_multiplicity_of_weighted_genus hg
  obtain ⟨b, hxi⟩ := xi_sq_factorization_pairedLinear_withMultiplicity_of_weighted_genus hg
    (xi_factorization_prod_with_multiplicity_of_hadamard_order_one xi_hasFiniteOrder xi_order_le_one)
  have ht (v : ℂ) : Tendsto (fun S : Finset XiZeroWithMultiplicity =>
      ‖∏ i ∈ S, xiPairedLinearFactor i.1 v‖) atTop
      (𝓝 ‖∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 v‖) := by
    have h : Tendsto (fun S : Finset XiZeroWithMultiplicity =>
        ∏ i ∈ S, xiPairedLinearFactor i.1 v) atTop
        (𝓝 (∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 v)) :=
      (multipliable_xiPairedLinearFactor_withMultiplicity_of_genus_one v hmult).hasProd
    exact h.norm
  have hp : ‖∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 z‖ ≤
      ‖∏' i : XiZeroWithMultiplicity, xiPairedLinearFactor i.1 w‖ := by
    apply le_of_tendsto_of_tendsto' (ht z) (ht w)
    intro S
    simp only [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hfac i.1)
  have hz := congrArg norm (hxi z)
  have hw := congrArg norm (hxi w)
  simp only [norm_pow, norm_mul] at hz hw
  have hs := mul_le_mul_of_nonneg_left hp (norm_nonneg (Complex.exp b))
  nlinarith only [hz, hw, hs, norm_nonneg (riemannXi z), norm_nonneg (riemannXi w)]

/-- Horizontal comparison is unconditional on Re(s) ≥ 1. -/
theorem norm_xi_le_to_right_of_one {z w : ℂ}
    (ha : 1 ≤ z.re) (hab : z.re ≤ w.re) (hi : z.im = w.im) :
    ‖riemannXi z‖ ≤ ‖riemannXi w‖ :=
  norm_xi_le_of_zero_abscissae_le (fun ρ => ρ.property.2.2.le) ha hab hi

/-- RH extends the same horizontal comparison to Re(s) ≥ 1/2. -/
theorem norm_xi_le_of_riemannHypothesis (hRH : RiemannHypothesis) {z w : ℂ}
    (ha : 1 / 2 ≤ z.re) (hab : z.re ≤ w.re) (hi : z.im = w.im) :
    ‖riemannXi z‖ ≤ ‖riemannXi w‖ :=
  norm_xi_le_of_zero_abscissae_le
    (fun ρ => (rh_equiv_mathlib.mp hRH _ ρ.property.1 ρ.property.2).le) ha hab hi

/-- Weak horizontal comparison alone rules out every zero to the right of the
critical line. A right zero would force a whole real interval of zero abscissae. -/
theorem riemannHypothesis_iff_horizontal_xi_comparison :
    RiemannHypothesis ↔ ∀ z w : ℂ, 1/2 ≤ z.re → z.re ≤ w.re → z.im = w.im →
      ‖riemannXi z‖ ≤ ‖riemannXi w‖ := by
  refine ⟨fun h _ _ => norm_xi_le_of_riemannHypothesis h, ?_⟩
  intro h
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro w hw hw1 hwzero
  have hz : riemannXi w = 0 :=
    (xi_zeros_are_nontrivial_zeros w).mpr ⟨⟨w, hwzero, by linarith, hw1⟩, rfl⟩
  let Z := Set.range (fun ρ : NontrivialZero => ρ.val.re)
  have hsub : Ioo (1/2 : ℝ) w.re ⊆ Z := by
    intro x hx
    let v : ℂ := ⟨x, w.im⟩
    have hnorm := h v w hx.1.le hx.2.le rfl
    rw [hz, norm_zero] at hnorm
    obtain ⟨ρ, he⟩ := (xi_zeros_are_nontrivial_zeros v).mp (norm_le_zero_iff.mp hnorm)
    exact ⟨ρ, (congrArg Complex.re he).symm⟩
  have hZ : Z.Countable := Set.countable_range _
  have hmass := measure_mono (μ := volume) hsub
  rw [Real.volume_Ioo, hZ.measure_zero volume, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hmass
  linarith

/-- The abscissae and height may all be rational. This countable family
of completed-zeta inequalities is equivalent to the full RH. -/
theorem riemannHypothesis_iff_rational_horizontal_xi_comparison :
    RiemannHypothesis ↔ ∀ p q t : ℚ, 1 / 2 ≤ p → p ≤ q →
      ‖riemannXi ((p : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ‖riemannXi ((q : ℂ) + (t : ℂ) * Complex.I)‖ := by
  constructor
  · intro h p q t hp hpq
    apply norm_xi_le_of_riemannHypothesis h
    · have hpr : ((1/2 : ℚ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      norm_num at hpr ⊢
      exact hpr
    · simpa using (show (p : ℝ) ≤ q by exact_mod_cast hpq)
    · simp
  · intro hr
    apply riemannHypothesis_iff_horizontal_xi_comparison.mpr
    intro z w hz hzw hi
    by_contra! hb
    let L (x : Fin 3 → ℝ) : ℂ := (((1/2 + (x 0)^2 : ℝ) : ℂ) + (x 2 : ℂ)*Complex.I)
    let R (x : Fin 3 → ℝ) : ℂ := L x + ((x 1)^2 : ℝ)
    have hc : Continuous L := by dsimp [L]; fun_prop
    have hd : Continuous R := by dsimp [R]; fun_prop
    let x : Fin 3 → ℝ := ![Real.sqrt (z.re-1/2), Real.sqrt (w.re-z.re), z.im]
    have hx : L x = z := by
      have he : 1/2+(x 0)^2 = z.re := by
        change 1/2+Real.sqrt (z.re-1/2)^2 = z.re
        rw [Real.sq_sqrt (sub_nonneg.mpr hz)]
        ring
      change (((1/2+(x 0)^2 : ℝ) : ℂ) + (z.im : ℂ)*Complex.I) = z
      rw [he, Complex.re_add_im]
    have hxw : R x = w := by
      rw [show R x = L x + ((x 1)^2 : ℝ) by rfl, hx]
      apply Complex.ext <;> simp [x, Real.sq_sqrt (sub_nonneg.mpr hzw), hi]
    have hden : DenseRange (fun v : Fin 3 → ℚ => fun i => (v i : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    obtain ⟨v, hv⟩ := hden.exists_mem_open
      (isOpen_lt ((xi_entire.continuous.comp hd).norm) ((xi_entire.continuous.comp hc).norm))
      ⟨x, by change ‖riemannXi (R x)‖ < ‖riemannXi (L x)‖; rwa [hx, hxw]⟩
    let p : ℚ := 1/2 + (v 0)^2
    let q : ℚ := p + (v 1)^2
    have htest := hr p q (v 2) (by dsimp [p]; nlinarith [sq_nonneg (v 0)]) (by dsimp [q]; nlinarith [sq_nonneg (v 1)])
    change ‖riemannXi (R fun i => ↑(v i))‖ < ‖riemannXi (L fun i => ↑(v i))‖ at hv
    have hp : L (fun i => ↑(v i)) = (p : ℂ)+(v 2 : ℂ)*Complex.I := by dsimp [L,p]; push_cast; ring
    have hq : R (fun i => ↑(v i)) = (q : ℂ)+(v 2 : ℂ)*Complex.I := by dsimp [R,L,q,p]; push_cast; ring
    rw [hp, hq] at hv
    exact (not_lt_of_ge htest) hv

private theorem norm_xi_as_zeta_product {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖riemannXi s‖ = (1 / 2 : ℝ) * ‖s‖ * ‖s-1‖ * ‖Complex.Gammaℝ s‖ * ‖riemannZeta s‖ := by
  have hs₀ : s ≠ 0 := fun h => by simpa [h] using hs
  have hΛ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs₀]
    field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
  have hxi : riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s :=
    XiZeros.xi_eq_half_s_sm1_Lambda hs₀ hs₁
  rw [hxi, hΛ]
  simp [norm_mul, norm_div, mul_assoc]

/-- The shifted zeta comparison retains the elementary xi prefactors. -/
theorem zeta_horizontal_comparison (hRH : RiemannHypothesis) {s w : ℂ}
    (hs : 1/2 ≤ s.re) (hw : s.re ≤ w.re) (hi : s.im = w.im)
    (hs₁ : s ≠ 1) (hw₁ : w ≠ 1) :
    ‖s‖ * ‖s - 1‖ * ‖Complex.Gammaℝ s‖ * ‖riemannZeta s‖ ≤
      ‖w‖ * ‖w - 1‖ * ‖Complex.Gammaℝ w‖ * ‖riemannZeta w‖ := by
  have h := norm_xi_le_of_riemannHypothesis hRH hs hw hi
  rw [norm_xi_as_zeta_product (by linarith) hs₁,
    norm_xi_as_zeta_product (by linarith) hw₁] at h
  linarith only [h]

end RiemannResearch.Analysis.XiHorizontalComparison


namespace RiemannResearch.Analysis.XiHorizontalComparison

/--
info: 'RiemannResearch.Analysis.XiHorizontalComparison.riemannHypothesis_iff_rational_horizontal_xi_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_iff_rational_horizontal_xi_comparison

end RiemannResearch.Analysis.XiHorizontalComparison

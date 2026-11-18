import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualZeroFixedStripConcentration
import RiemannResearch.Analysis.ActualUniformRationalLandau
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# Fixed real frequencies of the actual zeta zeros

At a positive frequency outside the integer logarithms, the right contour
side is bounded independently of both endpoints. The actual centered Landau
sum then has zero height-normalized limit. This extends the rational-frequency
contour calculation to the nonintegral prime roots needed for Ramanujan sums.
The count-normalized result only needs fixed-strip concentration to pass from
centered zeros to their ordinates.

Source for the fixed-frequency analytic formulas: Ford and Zaharescu,
*On the distribution of imaginary parts of zeros of the Riemann zeta
function*, (1.1) and Corollary 2, https://arxiv.org/abs/math/0405459.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- At a fixed nonresonant frequency all integer-log kernels share an
endpoint-independent majorant. The finite low frequencies retain their gaps. -/
theorem exists_bound_rightLandauLine_of_nonresonance (u : ℝ)
    (hn : ∀ k : ℕ, u ≠ Real.log k) :
    ∃ K : ℝ, ∀ A B : ℝ, ‖rightLandauLine A B u‖ ≤ K := by
  classical
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlog.eventually_ge_atTop (u + 1))
  let b (k : ℕ) : ℝ := 2 / |u - Real.log k|
  let D : ℝ := 2 + ∑ k ∈ Finset.range M, b k
  have hb (k : ℕ) : 0 ≤ b k := by unfold b; positivity
  have hD (k : ℕ) : b k ≤ D := by
    by_cases hk : k < M
    · have h := Finset.single_le_sum (s := Finset.range M) (f := b)
          (fun i _ => hb i) (Finset.mem_range.mpr hk)
      dsimp [D]
      linarith
    · have hk' := hM k (le_of_not_gt hk)
      have hgap : 1 ≤ |u - Real.log k| := by
        rw [abs_of_nonpos (by linarith : u - Real.log k ≤ 0)]
        linarith
      have hsmall : b k ≤ 2 := (div_le_iff₀ (by linarith : 0 < |u - Real.log k|)).2
        (by linarith)
      exact hsmall.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hb i))
  let c : ℂ := -((Real.exp (3 * u / 2) / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨‖c‖ * (D * ∑' k, mangoldtSquareCoeff k), ?_⟩
  intro A B
  rw [rightLandauLine_eq_kernel_tsum, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply tsum_of_norm_bounded (summable_mangoldtSquareCoeff.hasSum.mul_left D)
  intro k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mangoldtSquareCoeff_nonneg k),
    mul_comm D]
  exact mul_le_mul_of_nonneg_left
    ((norm_finitePhaseKernel_le (sub_ne_zero.mpr (hn k)) A B).trans (hD k))
    (mangoldtSquareCoeff_nonneg k)

/-- Fixed-frequency contour remainder with all three other sides and the short
terminal zero window included. -/
theorem exists_landau_log_sq_bound_of_bounded_right {u : ℝ} (hu : 0 < u)
    (hbounded : ∃ K : ℝ, ∀ A B : ℝ, ‖rightLandauLine A B u‖ ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 9 ≤ T →
      ‖landauSum T u‖ ≤ C * (Real.log (T+3))^2 := by
  obtain ⟨K,hK⟩ := hbounded
  obtain ⟨Cg,hCg,R,hR⟩ := WeilEF.good_heights_centered_exponential_horizontals
  obtain ⟨D,hD,htransfer⟩ := exists_landauSum_short_height_bound
  let A := R 1
  let e := Real.exp (3*u/2)
  let s := (9 + 2 * ∑' k, mangoldtSquareCoeff k) * (1 + 1/u)
  let b := 3*e*Cg*(Real.log 11)^2
  let h := 12*e*Cg
  let c := 4*D*Real.exp (|u|/2)
  let k₀ := ‖landauSum A u‖ + K + b
  refine ⟨|k₀| + |s+c| + |h| + 1,by positivity,?_⟩
  intro T hT
  let L := Real.log (T+3)
  let j := Nat.floor T - 6
  let B := R j
  obtain ⟨_, hjT, hTB, hBT⟩ := Real.goodHeight_floor_choice R
    (fun k => ⟨(hR k).1, (hR k).2.1⟩) hT
  change (j : ℝ) ≤ T at hjT
  change T ≤ B at hTB
  change B ≤ T + 2 at hBT
  obtain ⟨hAlo,hAhi,hAgood,hAh⟩ := hR 1
  norm_num at hAlo hAhi
  change 8 ≤ A at hAlo
  change A ≤ 9 at hAhi
  obtain ⟨_,_,hBgood,hBh⟩ := hR j
  have hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A := fun ρ hz hρ =>
    (hAgood ρ (Or.inl hρ) (by linarith [hz.2.1]) (by linarith [hz.2.2])) hz.1
  have hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B := fun ρ hz hρ =>
    (hBgood ρ (Or.inl hρ) (by linarith [hz.2.1]) (by linarith [hz.2.2])) hz.1
  have hL : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    linarith [Real.exp_one_lt_d9]
  have hleft : ‖leftLandauLine A B u‖ ≤ s * L :=
    norm_leftLandauLine_le_log_budget A B u L hAlo (by linarith) hu hL
      (Real.log_le_log (by linarith) (by linarith))
  have hbottom := hAh u A (Or.inl rfl)
  have htop := hBh u B (Or.inl rfl)
  rw [abs_of_pos hu] at hbottom htop
  norm_num only [Nat.cast_one,show (1:ℝ)+10=11 by norm_num] at hbottom
  change ‖_‖ ≤ b at hbottom
  change ‖_‖ ≤ 3 * e * Cg * (Real.log ((j : ℝ)+10))^2 at htop
  have hjlog := Real.log_nat_add_ten_le_two_log_add_three hT hjT
  change _ ≤ 2*L at hjlog
  have hsq : (Real.log ((j:ℝ)+10))^2 ≤ 4*L^2 := by
    have hj0 := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j] : 1 ≤ (j:ℝ)+10)
    nlinarith only [hjlog,hL,hj0]
  have hhor : ‖horizontalLandauCorrection A B u‖ ≤ b + h * L^2 := by
    refine (norm_horizontalLandauCorrection_le A B u).trans (add_le_add hbottom ?_)
    calc
      _ ≤ _ := htop
      _ ≤ (3*e*Cg) * (4*L^2) := mul_le_mul_of_nonneg_left hsq (by dsimp [e]; positivity)
      _ = _ := by dsimp [h]; ring
  have hshort : ‖landauSum B u - landauSum T u‖ ≤ c * L := by
    refine (htransfer T B u (by linarith) hTB hBT).trans ?_
    have hx := Real.log_add_four_le_two_log_add_three hT
    change _ ≤ 2*L at hx
    calc
      _ ≤ (2*D*(2*L)) * Real.exp (|u|/2) := by gcongr
      _ = _ := by dsimp [c]; ring
  have hfour := landauSum_sub_eq_four_sides A B u (by linarith) (by linarith) hgoodA hgoodB
  have heq : landauSum T u = landauSum A u + rightLandauLine A B u -
      leftLandauLine A B u + horizontalLandauCorrection A B u -
      (landauSum B u - landauSum T u) := by linear_combination hfour
  have hnorm : ‖landauSum T u‖ ≤ k₀ + (s+c)*L + h*L^2 := by
    calc
      _ ≤ ‖landauSum A u‖ + ‖rightLandauLine A B u‖ + ‖leftLandauLine A B u‖ +
          ‖horizontalLandauCorrection A B u‖ + ‖landauSum B u - landauSum T u‖ := by
        conv_lhs => rw [heq]
        calc
          _ ≤ _ := norm_sub_le _ _
          _ ≤ _ := by
            have ha := norm_add_le (landauSum A u) (rightLandauLine A B u)
            have hs := norm_sub_le (landauSum A u + rightLandauLine A B u) (leftLandauLine A B u)
            have hh := norm_add_le (landauSum A u + rightLandauLine A B u - leftLandauLine A B u)
              (horizontalLandauCorrection A B u)
            linarith
      _ ≤ _ := by dsimp [k₀]; linarith [hK A B]
  have hLL : L ≤ L^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (sub_nonneg.mpr hL)]
  have h1 : 1 ≤ L^2 := by nlinarith
  calc
    _ ≤ _ := hnorm
    _ ≤ |k₀| * L^2 + |s+c| * L^2 + |h| * L^2 := by
      have ha := (le_abs_self k₀).trans (le_mul_of_one_le_right (abs_nonneg k₀) h1)
      have hb := mul_le_mul (le_abs_self (s+c)) hLL (by linarith : 0 ≤ L) (abs_nonneg _)
      have hc := mul_le_mul_of_nonneg_right (le_abs_self h) (sq_nonneg L)
      linarith
    _ ≤ _ := by
      change _ ≤ (|k₀| + |s+c| + |h| + 1) * L^2
      nlinarith [sq_nonneg L]

theorem tendsto_landau_div_of_bounded_right {u : ℝ} (hu : 0 < u)
    (hbounded : ∃ K : ℝ, ∀ A B : ℝ, ‖rightLandauLine A B u‖ ≤ K) :
    Tendsto (fun T : ℝ => landauSum T u / (T : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := exists_landau_log_sq_bound_of_bounded_right hu hbounded
  apply squeeze_zero_norm' _ (by simpa using
    (shifted_log_pow_div_self_tendsto_zero 2).const_mul C)
  filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
  have hTp : 0 < T := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hb T hT) hTp.le

theorem tendsto_landau_div_of_nonresonance {u : ℝ} (hu : 0 < u)
    (hn : ∀ k : ℕ, u ≠ Real.log k) :
    Tendsto (fun T : ℝ => landauSum T u / (T : ℂ)) atTop (𝓝 0) :=
  tendsto_landau_div_of_bounded_right hu (exists_bound_rightLandauLine_of_nonresonance u hn)

/-- The contour gives a quantitative remainder at every fixed positive real
frequency. The limit parameter allows any of the arithmetic identifications
of the main term to be used without choosing a logarithmic representative. -/
theorem fixed_landau_remainder_isBigO_log_sq {u : ℝ} {m : ℂ} (hu : 0 < u)
    (hm : Tendsto (fun T : ℝ => landauSum T u / (T : ℂ)) atTop (𝓝 m)) :
    Asymptotics.IsBigO atTop (fun T : ℝ => landauSum T u / (T : ℂ) - m)
      (fun T : ℝ => (Real.log (T+3))^2 / T) := by
  classical
  by_cases hr : ∃ k : ℕ, u = Real.log (k : ℝ)
  · obtain ⟨k,rfl⟩ := hr
    have hk : 1 < k := by
      by_contra! hk
      interval_cases k <;> norm_num at hu
    have hm' := tendsto_rational_landau_div (n:=k) (m:=1) (by decide) hk
    simp only [Nat.cast_one, div_one] at hm'
    have heq := tendsto_nhds_unique hm hm'
    obtain ⟨C,hC,hb⟩ := exists_uniform_rational_landau_rpow_bound
    let A := (k : ℝ) ^ (5 / 2 : ℝ)
    let B := (k : ℝ) ^ (3 / 2 : ℝ)
    refine Asymptotics.IsBigO.of_bound (C*(A+B+k)) ?_
    filter_upwards [eventually_ge_atTop (9 : ℝ)] with T hT
    have hTp : 0 < T := by linarith
    have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTp.ne'
    let L := Real.log (T+3)
    have hL : 1 ≤ L := by
      dsimp [L]
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
    have hA : 0 ≤ A := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hB := hb T (k:ℝ) k 1 hT (by decide) hk le_rfl
    simp only [Nat.cast_one, div_one] at hB
    have he : landauSum T (Real.log k) / (T:ℂ) - m =
        (landauSum T (Real.log k) + ((T*rationalLandauMain k 1 : ℝ) : ℂ)) / (T:ℂ) := by
      rw [heq]
      push_cast
      field_simp <;> ring
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hTp.le), ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hTp.le
    refine hB.trans ?_
    change C*(A + B*L^2 + k*L) ≤ C*(A+B+k)*L^2
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC.le
    have hL2 : L ≤ L^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ L) (sub_nonneg.mpr hL)]
    have h1 := le_mul_of_one_le_right hA (hL.trans hL2)
    have h2 := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg (α:=ℝ) k)
    linarith
  · have hn : ∀ k : ℕ, u ≠ Real.log k := fun k hk => hr ⟨k,hk⟩
    have hm0 := tendsto_nhds_unique hm (tendsto_landau_div_of_nonresonance hu hn)
    obtain ⟨C,hC,hb⟩ := exists_landau_log_sq_bound_of_bounded_right hu
      (exists_bound_rightLandauLine_of_nonresonance u hn)
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (9:ℝ)] with T hT
    have hTp : 0 < T := by linarith
    rw [hm0,sub_zero,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hTp,
      Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) hTp.le),← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hb T hT) hTp.le

/-- The count-normalized centered Landau mode vanishes for every positive
real frequency, including resonances, without a zero-density premise. -/
theorem tendsto_landau_div_count_of_pos {u : ℝ} (hu : 0 < u) :
    Tendsto (fun T : ℝ => landauSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
  have hc : ∃ a : ℂ, Tendsto (fun T : ℝ => landauSum T u / (T : ℂ)) atTop (𝓝 a) := by
    by_cases hn : ∃ k : ℕ, u = Real.log k
    · obtain ⟨k,rfl⟩ := hn
      have hk : 1 < k := by
        by_contra! h
        interval_cases k <;> norm_num at hu
      exact ⟨_, by simpa using tendsto_rational_landau_div (n:=k) (m:=1) (by decide) hk⟩
    · exact ⟨0,tendsto_landau_div_of_nonresonance hu (fun k h => hn ⟨k,h⟩)⟩
  obtain ⟨a,ha⟩ := hc
  have hprod := ha.mul tendsto_complex_height_div_count
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  have hTc : (T:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  field_simp [hTc]

theorem tendsto_ordinate_div_count_of_pos {u : ℝ} (hu : 0 < u)
    (hs : FixedStripConcentration) :
    Tendsto (fun T : ℝ => ordinateSum T u / (Ncount 0 T : ℂ)) atTop (𝓝 0) :=
  tendsto_normalized_ordinate_of_fixedStrip u hs (tendsto_landau_div_count_of_pos hu)

end RiemannResearch.Analysis.ActualZeroOrdinate

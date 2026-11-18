import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualRationalLandauRightLine
import RiemannResearch.Analysis.ActualZeroHeightTransfer
import RiemannResearch.Analysis.ActualZetaGoodLandauHorizontals
import RiemannResearch.Analysis.FiniteOscillatoryKernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The moving prime-two resonance for the actual zeta ordinates

On the compact frequency interval from `log 2 / 2` to `log 2`, keep the
whole prime-two phase kernel. All the other Dirichlet-series frequencies
have a fixed positive gap. For the corresponding analytic strategy see
Ford and Zaharescu, *On the distribution of imaginary parts of zeros of the
Riemann zeta function*, Lemma 1, https://arxiv.org/abs/math/0405459.
-/

noncomputable section
open Complex Filter MeasureTheory Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem primeTwo_band_gap {u : ℝ} (hlo : Real.log 2 / 2 ≤ u)
    (hhi : u ≤ Real.log 2) {k : ℕ} (hk : k ≠ 2) :
    min (Real.log 2 / 2) (Real.log 3 - Real.log 2) ≤ |u - Real.log (k : ℝ)| := by
  rcases (show k = 0 ∨ k = 1 ∨ 3 ≤ k by omega) with rfl | rfl | hk₃
  · simpa [abs_of_pos (show 0 < u by linarith [log_two_pos])] using
      (min_le_left (Real.log 2 / 2) (Real.log 3 - Real.log 2)).trans hlo
  · simpa [abs_of_pos (show 0 < u by linarith [log_two_pos])] using
      (min_le_left (Real.log 2 / 2) (Real.log 3 - Real.log 2)).trans hlo
  · have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ k by exact_mod_cast hk₃)
    have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

private def primeTwoGap : ℝ :=
  min (Real.log 2 / 2) (Real.log 3 - Real.log 2)

private theorem primeTwoGap_pos : 0 < primeTwoGap :=
  lt_min (by linarith [log_two_pos])
    (sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num)))

private def primeTwoRemainderTerm (A B u : ℝ) (k : ℕ) : ℂ :=
  if k = 2 then 0 else
    (mangoldtSquareCoeff k : ℂ) * finitePhaseKernel A B (u - Real.log (k : ℝ))

private theorem norm_primeTwoRemainderTerm_le (A B : ℝ) {u : ℝ}
    (hlo : Real.log 2 / 2 ≤ u) (hhi : u ≤ Real.log 2) (k : ℕ) :
    ‖primeTwoRemainderTerm A B u k‖ ≤ (2 / primeTwoGap) * mangoldtSquareCoeff k := by
  by_cases hk : k = 2
  · simp only [primeTwoRemainderTerm, hk, if_true, norm_zero]
    exact mul_nonneg (div_nonneg (by norm_num) primeTwoGap_pos.le) (mangoldtSquareCoeff_nonneg 2)
  · have hgap := primeTwo_band_gap hlo hhi hk
    change primeTwoGap ≤ _ at hgap
    have hne : u - Real.log (k : ℝ) ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hgap
      exact (primeTwoGap_pos.not_ge hgap).elim
    have h := (norm_finitePhaseKernel_le hne A B).trans
      (div_le_div_of_nonneg_left (by norm_num) primeTwoGap_pos hgap)
    rw [primeTwoRemainderTerm, if_neg hk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mangoldtSquareCoeff_nonneg k), mul_comm (2 / primeTwoGap)]
    exact mul_le_mul_of_nonneg_left h (mangoldtSquareCoeff_nonneg k)

/-- The complete prime-two contribution of the right contour, with its
coefficient taken positive so the contribution enters with a minus sign. -/
def primeTwoLandauKernel (A B u : ℝ) : ℂ :=
  ((Real.exp (3 * u / 2) / (2 * Real.pi) : ℝ) : ℂ) *
    ((mangoldtSquareCoeff 2 : ℂ) * finitePhaseKernel A B (u - Real.log 2))

/-- Isolate only the term at two, retaining every other term with its sign. -/
theorem rightLandauLine_add_primeTwoLandauKernel (A B : ℝ) {u : ℝ}
    (hlo : Real.log 2 / 2 ≤ u) (hhi : u ≤ Real.log 2) :
    rightLandauLine A B u + primeTwoLandauKernel A B u =
      -((Real.exp (3 * u / 2) / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' k : ℕ, if k = 2 then 0 else
          (mangoldtSquareCoeff k : ℂ) * finitePhaseKernel A B (u - Real.log (k : ℝ)) := by
  let f (k : ℕ) : ℂ :=
    (mangoldtSquareCoeff k : ℂ) * finitePhaseKernel A B (u - Real.log (k : ℝ))
  let g := primeTwoRemainderTerm A B u
  have hgs : Summable g := (summable_mangoldtSquareCoeff.mul_left _).of_norm_bounded
    (norm_primeTwoRemainderTerm_le A B hlo hhi)
  let s (k : ℕ) : ℂ := if k = 2 then f 2 else 0
  have hss : Summable s := summable_of_ne_finset_zero (s := {2})
    (fun k hk => by simp [s, show k ≠ 2 by simpa using hk])
  have hsum : (∑' k, s k) = f 2 := by
    rw [tsum_eq_single 2 (fun k hk => by simp [s, hk])]
    simp [s]
  have hsplit : (∑' k, f k) = f 2 + ∑' k, g k := by
    rw [← hsum, ← hss.tsum_add hgs]
    apply tsum_congr
    intro k
    by_cases hk : k = 2 <;> simp [s, g, primeTwoRemainderTerm, f, hk]
  rw [rightLandauLine_eq_kernel_tsum, primeTwoLandauKernel]
  change -_ * (∑' k, f k) + _ * f 2 = -_ * (∑' k, g k)
  rw [hsplit]
  ring

private theorem norm_rightLandauLine_add_primeTwoLandauKernel_le (A B : ℝ) {u : ℝ}
    (hlo : Real.log 2 / 2 ≤ u) (hhi : u ≤ Real.log 2) :
    ‖rightLandauLine A B u + primeTwoLandauKernel A B u‖ ≤
      Real.exp (3 * Real.log 2 / 2) *
        ((2 / min (Real.log 2 / 2) (Real.log 3 - Real.log 2)) * ∑' k, mangoldtSquareCoeff k) := by
  rw [rightLandauLine_add_primeTwoLandauKernel A B hlo hhi, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < Real.exp (3*u/2)/(2*Real.pi))]
  have hsum : ‖∑' k, primeTwoRemainderTerm A B u k‖ ≤
      (2 / primeTwoGap) * ∑' k, mangoldtSquareCoeff k :=
    tsum_of_norm_bounded (summable_mangoldtSquareCoeff.hasSum.mul_left (2 / primeTwoGap))
      (norm_primeTwoRemainderTerm_le A B hlo hhi)
  have he : Real.exp (3*u/2)/(2*Real.pi) ≤ Real.exp (3*Real.log 2/2) := by
    calc
      _ ≤ Real.exp (3*u/2) := div_le_self (Real.exp_pos _).le (by linarith [Real.pi_gt_three])
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul he hsum (norm_nonneg _) (Real.exp_pos _).le

private theorem primeTwoLandauKernel_add (A B C u : ℝ) :
    primeTwoLandauKernel A B u + primeTwoLandauKernel B C u = primeTwoLandauKernel A C u := by
  let f (t : ℝ) : ℂ := Complex.exp (((u - Real.log 2 : ℝ) : ℂ) * Complex.I * (t : ℂ))
  have hf : Continuous f := by unfold f; fun_prop
  have hAB : IntervalIntegrable f volume A B := hf.intervalIntegrable A B
  have hBC : IntervalIntegrable f volume B C := hf.intervalIntegrable B C
  have h := intervalIntegral.integral_add_adjacent_intervals hAB hBC
  change (∫ t in A..B, _) + (∫ t in B..C, _) = (∫ t in A..C, _) at h
  simp only [f, integral_phase_eq_finitePhaseKernel] at h
  let weight (k : ℂ) := ((Real.exp (3*u/2)/(2*Real.pi) : ℝ) : ℂ) *
    ((mangoldtSquareCoeff 2 : ℂ) * k)
  simpa only [primeTwoLandauKernel, weight, ← mul_add] using congrArg weight h

private theorem norm_primeTwoLandauKernel_le (A B : ℝ) {u : ℝ} (hhi : u ≤ Real.log 2) :
    ‖primeTwoLandauKernel A B u‖ ≤ Real.exp (3 * Real.log 2 / 2) *
      mangoldtSquareCoeff 2 * |B - A| := by
  have hkernel : ‖finitePhaseKernel A B (u - Real.log 2)‖ ≤ |B - A| := by
    rw [← integral_phase_eq_finitePhaseKernel]
    simpa only [one_mul] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) (a := A) (b := B)
        (fun t _ => by simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          sub_zero, zero_mul, Real.exp_zero, le_rfl]))
  have he : Real.exp (3*u/2)/(2*Real.pi) ≤ Real.exp (3*Real.log 2/2) := by
    calc
      _ ≤ Real.exp (3*u/2) := div_le_self (Real.exp_pos _).le (by linarith [Real.pi_gt_three])
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  rw [primeTwoLandauKernel, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mangoldtSquareCoeff_nonneg 2),
    abs_of_pos (by positivity : 0 < Real.exp (3*u/2)/(2*Real.pi))]
  rw [mul_assoc]
  exact mul_le_mul he (mul_le_mul_of_nonneg_left hkernel (mangoldtSquareCoeff_nonneg 2))
    (mul_nonneg (mangoldtSquareCoeff_nonneg 2) (norm_nonneg _)) (Real.exp_pos _).le

/-- Exact arbitrary-cutoff identity with the full moving prime-two main term. -/
theorem landauSum_add_primeTwoLandauKernel_eq_complete (T A B u : ℝ)
    (hA : 0 < A) (hAB : A ≤ B)
    (hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A)
    (hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B) :
    landauSum T u + primeTwoLandauKernel 0 T u =
      (landauSum A u + primeTwoLandauKernel 0 A u) +
      (rightLandauLine A B u + primeTwoLandauKernel A B u) -
      leftLandauLine A B u + horizontalLandauCorrection A B u -
      (landauSum B u - landauSum T u) - primeTwoLandauKernel T B u := by
  have h := landauSum_sub_eq_four_sides A B u hA hAB hgoodA hgoodB
  have h₁ := primeTwoLandauKernel_add 0 A B u
  have h₂ := primeTwoLandauKernel_add 0 T B u
  linear_combination h + h₂ - h₁

/-- An arbitrary actual height has a uniform log-squared error in the whole
prime-two band, even at frequencies approaching the exact resonance. -/
theorem exists_uniform_primeTwo_landau_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T u : ℝ, 9 ≤ T → Real.log 2 / 2 ≤ u → u ≤ Real.log 2 →
      ‖landauSum T u + primeTwoLandauKernel 0 T u‖ ≤ C * (Real.log (T + 3)) ^ 2 := by
  obtain ⟨Cg, hCg, R, hR⟩ := WeilEF.good_heights_centered_exponential_horizontals
  obtain ⟨D, hD, htransfer⟩ := exists_landauSum_short_height_bound
  let a := Real.log 2
  let A := R 1
  let E := Real.exp (3 * a / 2)
  let S := ∑' k : ℕ, mangoldtSquareCoeff k
  let M := mangoldtSquareCoeff 2
  let P := 2 / min (a / 2) (Real.log 3 - a)
  let J := (9 + 2 * S) * (1 + 2 / a)
  let C := E * ((Ncount 0 A : ℝ) + 11*M + P*S + 15*Cg + 4*D) + J + 1
  have ha : 0 < a := log_two_pos
  have hE : 0 < E := Real.exp_pos _
  have hS : 0 ≤ S := tsum_nonneg mangoldtSquareCoeff_nonneg
  have hM : 0 ≤ M := mangoldtSquareCoeff_nonneg 2
  have hP : 0 < P := div_pos (by norm_num) (lt_min (by linarith)
    (sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))))
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T u hT hlo hhi
  let L := Real.log (T + 3)
  let j := Nat.floor T - 6
  let B := R j
  obtain ⟨_, hjT, hTB, hBT⟩ := Real.goodHeight_floor_choice R
    (fun k => ⟨(hR k).1, (hR k).2.1⟩) hT
  change (j : ℝ) ≤ T at hjT
  change T ≤ B at hTB
  change B ≤ T + 2 at hBT
  obtain ⟨hAlo, hAhi, hAgood, hAh⟩ := hR 1
  norm_num at hAlo hAhi
  change 8 ≤ A at hAlo
  change A ≤ 9 at hAhi
  obtain ⟨_, _, hBgood, hBh⟩ := hR j
  have hgoodA : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ A := fun ρ hρ h =>
    (hAgood ρ (Or.inl h) (by linarith [hρ.2.1]) (by linarith [hρ.2.2])) hρ.1
  have hgoodB : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ B := fun ρ hρ h =>
    (hBgood ρ (Or.inl h) (by linarith [hρ.2.1]) (by linarith [hρ.2.2])) hρ.1
  have hu : 0 < u := by linarith
  have hL : 1 ≤ L := by
    rw [show L = Real.log (T+3) from rfl, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hLL : L ≤ L^2 := by nlinarith only [hL]
  have hL1 : 1 ≤ L^2 := by nlinarith only [hL]
  have he : Real.exp (3*u/2) ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hhalf : Real.exp (|u|/2) ≤ E := by
    rw [abs_of_pos hu]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlow : ‖landauSum A u‖ ≤ (Ncount 0 A : ℝ) * E :=
    (norm_landauSum_le_count A u).trans (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg _))
  have hcA : ‖primeTwoLandauKernel 0 A u‖ ≤ E*M*9 := by
    apply (norm_primeTwoLandauKernel_le 0 A hhi).trans
    rw [sub_zero, abs_of_nonneg (by linarith : 0 ≤ A)]
    gcongr
  have hcB : ‖primeTwoLandauKernel T B u‖ ≤ E*M*2 := by
    apply (norm_primeTwoLandauKernel_le T B hhi).trans
    rw [abs_of_nonneg (by linarith : 0 ≤ B-T)]
    gcongr
    linarith
  have hright : ‖rightLandauLine A B u + primeTwoLandauKernel A B u‖ ≤ E*(P*S) :=
    norm_rightLandauLine_add_primeTwoLandauKernel_le A B hlo hhi
  have hinv : 1/u ≤ 2/a := by
    rw [show 2/a = 1/(a/2) by ring]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hlo
  have hleft : ‖leftLandauLine A B u‖ ≤ J*L^2 := by
    apply (norm_leftLandauLine_le_log_budget A B u L hAlo (by linarith) hu hL
      (Real.log_le_log (by linarith) (by linarith))).trans
    change (9+2*S)*(1+1/u)*L ≤ J*L^2
    unfold J
    gcongr
  have hbottom := hAh u A (Or.inl rfl)
  have htop := hBh u B (Or.inl rfl)
  rw [abs_of_pos hu] at hbottom htop
  norm_num only [Nat.cast_one, show (1:ℝ)+10=11 by norm_num] at hbottom
  have hjlog := Real.log_nat_add_ten_le_two_log_add_three hT hjT
  have h11 : Real.log 11 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hhs : ‖horizontalLandauCorrection A B u‖ ≤ (15*Cg*E)*L^2 := by
    apply (norm_horizontalLandauCorrection_le A B u).trans
    have hj0 := Real.log_nonneg (show (1:ℝ) ≤ (j:ℝ)+10 by
      linarith [Nat.cast_nonneg (α := ℝ) j])
    have h110 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 11)
    have h11sq : (Real.log 11)^2 ≤ L^2 := (sq_le_sq₀ h110 (by linarith)).2 h11
    have hjsq : (Real.log ((j:ℝ)+10))^2 ≤ (2*L)^2 := (sq_le_sq₀ hj0 (by linarith)).2 hjlog
    have hb : ‖_‖ ≤ (3*E*Cg)*L^2 := hbottom.trans (by gcongr)
    have ht : ‖_‖ ≤ (3*E*Cg)*(2*L)^2 := htop.trans (by gcongr)
    linarith only [hb, ht]
  have hshort : ‖landauSum B u - landauSum T u‖ ≤ (4*D*E)*L^2 := by
    calc
      _ ≤ (2 * D * Real.log (T + 4)) * Real.exp (|u|/2) :=
        htransfer T B u (by linarith) hTB hBT
      _ ≤ (2 * D * (2*L)) * E := by
        gcongr
        exact Real.log_add_four_le_two_log_add_three hT
      _ = (4*D*E)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLL (by positivity)
  rw [landauSum_add_primeTwoLandauKernel_eq_complete T A B u (by linarith)
    (by linarith) hgoodA hgoodB, sub_eq_add_neg _ (primeTwoLandauKernel T B u)]
  have hn := Complex.norm_add_sub_add_sub_add_le
    (landauSum A u + primeTwoLandauKernel 0 A u)
    (rightLandauLine A B u + primeTwoLandauKernel A B u)
    (leftLandauLine A B u) (horizontalLandauCorrection A B u)
    (landauSum B u - landauSum T u) (-primeTwoLandauKernel T B u)
  rw [norm_neg] at hn
  refine hn.trans ?_
  have hf : 0 ≤ E * ((Ncount 0 A : ℝ) + 11*M + P*S) := by positivity
  have hconst := le_mul_of_one_le_right hf hL1
  have hfirst := (norm_add_le (landauSum A u) (primeTwoLandauKernel 0 A u)).trans
    (add_le_add hlow hcA)
  change _ ≤ C*L^2
  dsimp only [C]
  nlinarith only [hfirst, hcB, hright, hleft, hhs, hshort, hconst, sq_nonneg L]


/-- The same prime normalization as the divisor probe, written using the
real angular frequency directly. -/
def primeTwoOrdinateProbe (T u : ℝ) : ℂ :=
  ((-(2 * Real.pi * Real.exp (u / 2)) / Real.log 2 : ℝ) : ℂ) *
    (ordinateSum T u / (T : ℂ))

/-- The exact moving main term after the prime normalization. -/
def primeTwoOrdinateProfile (T u : ℝ) : ℂ :=
  ((Real.exp (2 * u) / 4 : ℝ) : ℂ) *
    (finitePhaseKernel 0 T (u - Real.log 2) / (T : ℂ))

/-- The signed discrepancy splits into the horizontal transfer and the
complete arbitrary-height contour remainder. -/
theorem primeTwoOrdinateProbe_sub_profile (T u : ℝ) :
    primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u =
      ((-(2 * Real.pi * Real.exp (u / 2)) / Real.log 2 : ℝ) : ℂ) *
        (((ordinateSum T u - landauSum T u) / (T : ℂ)) +
          ((landauSum T u + primeTwoLandauKernel 0 T u) / (T : ℂ))) := by
  have hM : mangoldtSquareCoeff 2 = Real.log 2 / 4 := by
    rw [mangoldtSquareCoeff, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have he : Real.exp (u / 2) * Real.exp (3 * u / 2) = Real.exp (2*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hα : (-(2 * Real.pi * Real.exp (u / 2)) / Real.log 2) *
      (Real.exp (3*u/2)/(2*Real.pi)) * (Real.log 2 / 4) = -(Real.exp (2*u)/4) := by
    rw [← he]
    field_simp [Real.pi_ne_zero, log_two_pos.ne']
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hα
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at hcast
  rw [primeTwoOrdinateProbe, primeTwoOrdinateProfile, primeTwoLandauKernel, hM]
  linear_combination (-finitePhaseKernel 0 T (u - Real.log 2) / (T : ℂ)) * hcast

/-- A uniform quantitative asymptotic for the prime-two ordinate probe,
including frequencies that converge to `log 2` as the height grows. -/
theorem eventually_primeTwoOrdinateProbe_profile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ u : ℝ,
      Real.log 2 / 2 ≤ u → u ≤ Real.log 2 →
      ‖primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u‖ ≤
        C * (horizontalLogRate T + (Real.log (T + 3)) ^ 2 / T) := by
  obtain ⟨A, hA, hLandau⟩ := exists_uniform_primeTwo_landau_bound
  obtain ⟨B, hEnergy⟩ := horizontalEnergy_div_height_isBigO_loglog_sq_div_log.bound
  let a := Real.log 2
  let W := 2 * Real.pi * Real.exp (a / 2) / a
  let D := a^2 * Real.exp (a / 2) * (|B| + 1)
  have ha : 0 < a := log_two_pos
  have hW : 0 < W := by dsimp [W]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨W * (D + A), by positivity, ?_⟩
  filter_upwards [hEnergy, eventually_ge_atTop (9 : ℝ)] with T hBnd hT
  intro u hlo hhi
  have hTp : 0 < T := by linarith
  have hU : 0 < u := by linarith
  have hE : 0 ≤ horizontalEnergy T / T := div_nonneg (horizontalEnergy_nonneg T) hTp.le
  have hr : 0 ≤ horizontalLogRate T := by
    unfold horizontalLogRate
    exact div_nonneg (sq_nonneg _) (Real.log_pos (by linarith : 1 < T)).le
  change ‖horizontalEnergy T / T‖ ≤ B * ‖horizontalLogRate T‖ at hBnd
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE, abs_of_nonneg hr] at hBnd
  have hBnd' := hBnd.trans (mul_le_mul_of_nonneg_right
    (show B ≤ |B| + 1 by linarith [le_abs_self B]) hr)
  have h_exp : Real.exp (u / 2) ≤ Real.exp (a / 2) := Real.exp_le_exp.mpr (by linarith)
  have hScale : ‖((-(2 * Real.pi * Real.exp (u / 2)) / Real.log 2 : ℝ) : ℂ)‖ ≤ W := by
    rw [neg_div, Complex.ofReal_neg, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    dsimp [W]
    gcongr
  have hTrans : ‖(ordinateSum T u - landauSum T u) / (T : ℂ)‖ ≤
      D * horizontalLogRate T := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp]
    calc
      _ ≤ (u^2 * Real.exp (|u| / 2) * horizontalEnergy T) / T :=
        div_le_div_of_nonneg_right (ordinate_landau_error T u) hTp.le
      _ = u^2 * Real.exp (u / 2) * (horizontalEnergy T / T) := by
        rw [abs_of_pos hU]; ring
      _ ≤ a^2 * Real.exp (a / 2) * ((|B| + 1) * horizontalLogRate T) := by
        gcongr
      _ = _ := by dsimp [D]; ring
  have hCont : ‖(landauSum T u + primeTwoLandauKernel 0 T u) / (T : ℂ)‖ ≤
      A * ((Real.log (T + 3)) ^ 2 / T) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTp, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hLandau T u hT hlo hhi) hTp.le
  rw [primeTwoOrdinateProbe_sub_profile, norm_mul]
  calc
    _ ≤ W * (D * horizontalLogRate T + A * ((Real.log (T + 3))^2 / T)) := by
      apply mul_le_mul hScale ((norm_add_le _ _).trans (add_le_add hTrans hCont))
        (norm_nonneg _) hW.le
    _ ≤ _ := by
      have hc : 0 ≤ (Real.log (T + 3))^2 / T := by positivity
      have hd := mul_nonneg hD.le hc
      have hb := mul_nonneg hA.le hr
      have hbudget : D * horizontalLogRate T + A * (Real.log (T + 3)^2 / T) ≤
          (D + A) * (horizontalLogRate T + Real.log (T + 3)^2 / T) := by
        nlinarith only [hd, hb]
      calc
        _ ≤ W * ((D + A) * (horizontalLogRate T + Real.log (T + 3)^2 / T)) :=
          mul_le_mul_of_nonneg_left hbudget hW.le
        _ = _ := by ring

/-- For any requested accuracy one height threshold works on the whole band. -/
theorem eventually_primeTwoOrdinateProbe_profile_close {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ u : ℝ, Real.log 2 / 2 ≤ u → u ≤ Real.log 2 →
      ‖primeTwoOrdinateProbe T u - primeTwoOrdinateProfile T u‖ < ε := by
  obtain ⟨C, _, hC⟩ := eventually_primeTwoOrdinateProbe_profile_bound
  have h := (horizontalLogRate_tendsto_zero.add
    (shifted_log_pow_div_self_tendsto_zero 2)).const_mul C
  simp only [add_zero, mul_zero] at h
  filter_upwards [hC, h.eventually_lt_const hε] with T hT hsmall
  exact fun u hlo hhi => (hT u hlo hhi).trans_lt hsmall

theorem primeTwoOrdinateProfile_resonant {T : ℝ} (hT : 0 < T) :
    primeTwoOrdinateProfile T (Real.log 2) = 1 := by
  rw [primeTwoOrdinateProfile, sub_self, finitePhaseKernel_zero, sub_zero,
    show (2:ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hn : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  norm_num [hn]

/-- Separation from the prime frequency bounds the entire moving main term. -/
theorem norm_primeTwoOrdinateProfile_le {T u : ℝ} (hT : 0 < T) (hu : u < Real.log 2) :
    ‖primeTwoOrdinateProfile T u‖ ≤ 2 / ((Real.log 2 - u) * T) := by
  have hcoef : Real.exp (2*u)/4 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4), one_mul,
      show (4:ℝ) = Real.exp (2*Real.log 2) by
        rw [show (2:ℝ)*Real.log 2 = Real.log 2 + Real.log 2 by ring,
          Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num]
    exact Real.exp_le_exp.mpr (by linarith)
  have h := norm_finitePhaseKernel_le (sub_ne_zero.mpr hu.ne) 0 T
  rw [abs_of_neg (sub_neg.mpr hu), neg_sub] at h
  rw [primeTwoOrdinateProfile, norm_mul, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.exp (2*u)/4), abs_of_pos hT]
  calc
    _ ≤ 1 * ((2 / (Real.log 2 - u)) / T) :=
      mul_le_mul hcoef (div_le_div_of_nonneg_right h hT.le) (by positivity) (by norm_num)
    _ = _ := by rw [one_mul, div_div]

private theorem finitePhaseKernel_div_height {x T : ℝ} (hT : 0 < T) :
    finitePhaseKernel 0 T (x / T) / (T : ℂ) = finitePhaseKernel 0 1 x := by
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  by_cases hx : x = 0
  · simp [hx, finitePhaseKernel_zero, hTc]
  · have hphase : (((x / T : ℝ) : ℂ) * Complex.I) * (T : ℂ) = (x : ℂ) * Complex.I := by
      push_cast
      field_simp
    simp only [finitePhaseKernel, if_neg hx, if_neg (div_ne_zero hx hT.ne'), hphase,
      Complex.ofReal_zero, Complex.ofReal_one, mul_zero, mul_one, Complex.exp_zero]
    rw [div_div, hphase]

/-- The order-`1/T` transition at the prime-two resonance is the exact
unit-interval oscillatory kernel. -/
theorem tendsto_primeTwoOrdinateProbe_scaled {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun T : ℝ => primeTwoOrdinateProbe T (Real.log 2 - x / T)) atTop
      (𝓝 (finitePhaseKernel 0 1 (-x))) := by
  have hsmall : Tendsto (fun T : ℝ => x / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul x
  have hlim : Tendsto (fun T : ℝ => Real.log 2 - x / T) atTop (𝓝 (Real.log 2)) := by
    simpa only [sub_zero] using hsmall.const_sub (Real.log 2)
  have hlow : Real.log 2 / 2 < Real.log 2 := by linarith [log_two_pos]
  have herror : Tendsto (fun T : ℝ =>
      primeTwoOrdinateProbe T (Real.log 2 - x / T) -
        primeTwoOrdinateProfile T (Real.log 2 - x / T)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    filter_upwards [eventually_primeTwoOrdinateProbe_profile_close hε,
      hlim.eventually (Ici_mem_nhds hlow), eventually_gt_atTop (0 : ℝ)] with T hT hlowT hpos
    simpa only [dist_zero_right] using hT _ hlowT
      (sub_le_self _ (div_nonneg hx hpos.le))
  have hcont : Continuous (fun u : ℝ => ((Real.exp (2 * u) / 4 : ℝ) : ℂ)) := by fun_prop
  have hAmp := (hcont.continuousAt.tendsto.comp hlim).mul_const (finitePhaseKernel 0 1 (-x))
  have hE : Real.exp (2 * Real.log 2) / 4 = 1 := by
    rw [show (2:ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  simp only [hE, Complex.ofReal_one, one_mul] at hAmp
  have hprof : Tendsto (fun T : ℝ => primeTwoOrdinateProfile T (Real.log 2 - x / T)) atTop
      (𝓝 (finitePhaseKernel 0 1 (-x))) := by
    apply hAmp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Function.comp_apply, primeTwoOrdinateProfile,
      show Real.log 2 - x / T - Real.log 2 = -x / T by ring, finitePhaseKernel_div_height hT]
  simpa only [zero_add, sub_add_cancel] using herror.add hprof

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.eventually_primeTwoOrdinateProbe_profile_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_primeTwoOrdinateProbe_profile_bound

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_primeTwoOrdinateProbe_scaled' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_primeTwoOrdinateProbe_scaled

end RiemannResearch.Analysis.ActualZeroOrdinate

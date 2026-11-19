import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pair-statistic transfer from averaged vacancies and a third moment

Source for the number-theoretic application: Arias de Reyna--Rodgers,
On convergence of points to limiting processes, with an application to zeta
zeros, https://arxiv.org/abs/2311.13441, Theorem 34 and Corollary 35 (Fujii's
microscopic count moments). That analytic input is external here.

These generic measure-theoretic statements are proved from the elementary
Young inequality for 0 <= d <= z. They retain every integrability, moment
and vacancy assumption; the theorem does not prove a zeta-zero moment bound,
vanishing actual vacancies, or a sine-kernel limit.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.PairVacancyMoment

theorem count_vacancy_young (z d a : ℝ) (hd : 0 ≤ d) (hdz : d ≤ z) (ha : 0 < a) :
    2*z*d ≤ a*z^3+d/a := by
  have h1 := mul_nonneg hd (sq_nonneg (a*z-1))
  have h2 := mul_nonneg (sub_nonneg.mpr hdz) (sq_nonneg (a*z))
  have h3 : a*(2*z*d) ≤ a^2*z^3+d := by nlinarith
  apply (mul_le_mul_iff_right₀ ha).mp
  calc
    a*(2*z*d) ≤ a^2*z^3+d := by nlinarith [h3]
    _ = a*(a*z^3+d/a) := by field_simp

theorem integral_pair_error_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f z d : Ω → ℝ) (M a : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (hf : Integrable f ν) (hz : Integrable (fun x => (z x) ^ 3) ν)
    (hd : Integrable d ν)
    (hpos : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ z x)
    (herr : ∀ x, |f x| ≤ 2 * M * z x * d x) :
    |∫ x, f x ∂ν| ≤ M*(a*(∫ x, (z x) ^ 3 ∂ν)+(∫ x, d x ∂ν)/a) := by
  have hg : Integrable (fun x => M*(a*(z x) ^ 3+d x/a)) ν :=
    ((hz.const_mul a).add (hd.div_const a)).const_mul M
  have habs : Integrable (fun x => |f x|) ν := by simpa only [Real.norm_eq_abs] using hf.norm
  calc
    _ ≤ ∫ x, |f x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, M*(a*(z x) ^ 3+d x/a) ∂ν := by
      apply integral_mono habs hg
      intro x
      calc
        |f x| ≤ 2 * M * z x * d x := herr x
        _ = M*(2*z x * d x) := by ring
        _ ≤ M*(a*(z x) ^ 3+d x/a) :=
          mul_le_mul_of_nonneg_left (count_vacancy_young _ _ _ (hpos x) (hle x) ha) hM
    _ = _ := by
      rw [integral_const_mul, integral_add (hz.const_mul a) (hd.div_const a),
        integral_const_mul, integral_div]

theorem tendsto_zero_of_young_bounds {β : Type*} {l : Filter β}
    (f d : β → ℝ) (M C : ℝ) (hM : 0 < M) (hC : 0 < C)
    (hd : Tendsto d l (𝓝 0))
    (hb : ∀ a : ℝ, 0 < a → ∀ t, |f t| ≤ M*(a*C+d t/a)) :
    Tendsto f l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let a := ε/(4*M*C)
  have ha : 0 < a := by dsimp [a]; positivity
  have hac : M*(a*C) = ε/4 := by dsimp [a]; field_simp
  have htol : 0 < a*ε/(4*M) := by positivity
  filter_upwards [(tendsto_order.mp hd).2 (a*ε/(4*M)) htol] with t ht
  have hs : M*(d t/a) < ε/4 := by
    calc
      _ < M*((a*ε/(4*M))/a) :=
        mul_lt_mul_of_pos_left ((div_lt_div_iff_of_pos_right ha).mpr ht) hM
      _ = ε/4 := by field_simp
  rw [Real.dist_eq, sub_zero]
  calc
    |f t| ≤ M*(a*C+d t/a) := hb a ha t
    _ = ε/4+M*(d t/a) := by rw [mul_add, hac]
    _ < ε/4+ε/4 := by linarith
    _ < ε := by linarith

theorem integral_tendsto_zero_of_vacancy {β Ω : Type*} [MeasurableSpace Ω]
    {l : Filter β} (ν : β → Measure Ω) (f z d : β → Ω → ℝ)
    (M C : ℝ) (hM : 0 < M) (hC : 0 < C)
    (hf : ∀ t, Integrable (f t) (ν t))
    (hz : ∀ t, Integrable (fun x => (z t x) ^ 3) (ν t))
    (hd : ∀ t, Integrable (d t) (ν t))
    (hpos : ∀ t x, 0 ≤ d t x) (hle : ∀ t x, d t x ≤ z t x)
    (herr : ∀ t x, |f t x| ≤ 2 * M * z t x * d t x)
    (hmoment : ∀ t, (∫ x, (z t x) ^ 3 ∂ν t) ≤ C)
    (hvacancy : Tendsto (fun t => ∫ x, d t x ∂ν t) l (𝓝 0)) :
    Tendsto (fun t => ∫ x, f t x ∂ν t) l (𝓝 0) := by
  apply tendsto_zero_of_young_bounds _ _ M C hM hC hvacancy
  intro a ha t
  apply (integral_pair_error_le (ν t) (f t) (z t) (d t) M a hM.le ha
    (hf t) (hz t) (hd t) (hpos t) (hle t) (herr t)).trans
  apply mul_le_mul_of_nonneg_left _ hM.le
  have h := mul_le_mul_of_nonneg_left (hmoment t) ha.le
  linarith

/-- An optimized version of the parameterized third-moment estimate. It also
covers zero vacancy and a zero third moment. -/
theorem integral_pair_error_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f z d : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : Integrable f ν) (hz : Integrable (fun x => (z x) ^ 3) ν) (hd : Integrable d ν)
    (hpos : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ z x)
    (herr : ∀ x, |f x| ≤ 2 * M * z x * d x) :
    |∫ x, f x ∂ν| ≤ 2 * M * Real.sqrt ((∫ x, (z x) ^ 3 ∂ν) * (∫ x, d x ∂ν)) := by
  let C := ∫ x, (z x) ^ 3 ∂ν
  let D := ∫ x, d x ∂ν
  have hc : 0 ≤ C := integral_nonneg fun x => pow_nonneg ((hpos x).trans (hle x)) _
  have hd' : 0 ≤ D := integral_nonneg hpos
  have bound (a : ℝ) (ha : 0 < a) :
      |∫ x, f x ∂ν| ≤ M * (a * C + D / a) :=
    integral_pair_error_le ν f z d M a hM ha hf hz hd hpos hle herr
  change |∫ x, f x ∂ν| ≤ 2 * M * Real.sqrt (C * D)
  by_cases hzD : D = 0
  · have hd0 : d =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all ν hpos) hd).mp hzD
    have hf0 : f =ᵐ[ν] 0 := by
      filter_upwards [hd0] with x hx
      have he := herr x
      change d x = 0 at hx
      simpa [hx] using he
    simp [integral_congr_ae hf0, hzD]
  by_cases hzC : C = 0
  · have hzae : (fun x => (z x) ^ 3) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all ν (fun x => pow_nonneg ((hpos x).trans (hle x)) 3)) hz).mp hzC
    have hf0 : f =ᵐ[ν] 0 := by
      filter_upwards [hzae] with x hx
      change (z x) ^ 3 = 0 at hx
      have hx' : z x = 0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx
      have he := herr x
      simpa [hx'] using he
    simp [integral_congr_ae hf0, hzC]
  have hsc := Real.sqrt_pos.mpr (lt_of_le_of_ne hc (Ne.symm hzC))
  have hsd := Real.sqrt_pos.mpr (lt_of_le_of_ne hd' (Ne.symm hzD))
  have ha := bound (Real.sqrt D / Real.sqrt C) (div_pos hsd hsc)
  rw [Real.sqrt_mul hc]
  calc
    _ ≤ _ := ha
    _ = _ := by
      rw [← Real.sq_sqrt hc, ← Real.sq_sqrt hd']
      simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
      field_simp [hsc.ne', hsd.ne']
      ring

/-- Splitting at a count threshold requires only control of the square-count
tail. Both terms remain visible for a moving family of windows. -/
theorem integral_pair_error_le_square_tail {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f z d : Ω → ℝ) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hf : Integrable f ν) (hd : Integrable d ν)
    (htail : Integrable (fun x => if A < z x then (z x) ^ 2 else 0) ν)
    (hpos : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ z x)
    (herr : ∀ x, |f x| ≤ 2 * M * z x * d x) :
    |∫ x, f x ∂ν| ≤ 2 * M * (A * (∫ x, d x ∂ν) +
      ∫ x, (if A < z x then (z x) ^ 2 else 0) ∂ν) := by
  let tail := fun x => if A < z x then (z x) ^ 2 else 0
  have hg : Integrable (fun x => (2 * M) * (A * d x + tail x)) ν :=
    ((hd.const_mul A).add htail).const_mul _
  have habs : Integrable (fun x => |f x|) ν := by simpa only [Real.norm_eq_abs] using hf.norm
  calc
    _ ≤ ∫ x, |f x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, (2 * M) * (A * d x + tail x) ∂ν := by
      apply integral_mono habs hg
      intro x
      apply (herr x).trans
      rw [mul_assoc (2 * M)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hx : A < z x
      · simp only [tail, if_pos hx]
        nlinarith [mul_nonneg (hpos x) hA,
          mul_nonneg ((hpos x).trans (hle x)) (sub_nonneg.mpr (hle x))]
      · simp only [tail, if_neg hx, add_zero]
        exact mul_le_mul_of_nonneg_right (le_of_not_gt hx) (hpos x)
    _ = _ := by rw [integral_const_mul, integral_add (hd.const_mul A) htail, integral_const_mul]

/-- Uniformly vanishing tails of squared window counts, along with averaged
vacancy decay, suffice for signed pair transfer. A third moment is optional. -/
theorem integral_tendsto_zero_of_square_tails {β Ω : Type*} [MeasurableSpace Ω]
    {l : Filter β} (ν : β → Measure Ω) (f z d : β → Ω → ℝ)
    (M : ℝ) (hM : 0 < M) (hf : ∀ t, Integrable (f t) (ν t))
    (hd : ∀ t, Integrable (d t) (ν t))
    (htail : ∀ A : ℝ, 0 < A → ∀ t, Integrable
      (fun x => if A < z t x then (z t x) ^ 2 else 0) (ν t))
    (hpos : ∀ t x, 0 ≤ d t x) (hle : ∀ t x, d t x ≤ z t x)
    (herr : ∀ t x, |f t x| ≤ 2 * M * z t x * d t x)
    (hUI : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ᶠ t in l,
      (∫ x, (if A < z t x then (z t x) ^ 2 else 0) ∂ν t) < ε)
    (hD : Tendsto (fun t => ∫ x, d t x ∂ν t) l (𝓝 0)) :
    Tendsto (fun t => ∫ x, f t x ∂ν t) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htol : 0 < ε / (4 * M) := by positivity
  obtain ⟨A, hA, ht⟩ := hUI _ htol
  have hsmall : ∀ᶠ t in l, A * (∫ x, d t x ∂ν t) < ε / (4 * M) := by
    have hh := hD.const_mul A
    rw [mul_zero] at hh
    exact (tendsto_order.mp hh).2 _ htol
  filter_upwards [ht, hsmall] with t ht' hd'
  rw [Real.dist_eq, sub_zero]
  apply (integral_pair_error_le_square_tail _ _ _ _ M A hM.le hA.le (hf t) (hd t)
    (htail A hA t) (hpos t) (hle t) (herr t)).trans_lt
  have hh := add_lt_add hd' ht'
  calc
    _ < 2 * M * (ε / (4 * M) + ε / (4 * M)) := mul_lt_mul_of_pos_left hh (by positivity)
    _ = ε := by field_simp; ring

private theorem memLp_integrable_root {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {u : Ω → ℝ} (hu : Integrable u ν) (hn : ∀ x, 0 ≤ u x) {r : ℝ} (hr : 0 < r) :
    MemLp (fun x => u x ^ (1 / r)) (ENNReal.ofReal r) ν := by
  have hm := (hu.aemeasurable.pow_const (1 / r)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (ENNReal.ofReal_ne_zero_iff.mpr hr)
    ENNReal.ofReal_ne_top).mp
  have he (x : Ω) : ‖u x ^ (1 / r)‖ ^ (ENNReal.ofReal r).toReal = u x := by
    rw [ENNReal.toReal_ofReal hr.le, Real.norm_of_nonneg (Real.rpow_nonneg (hn x) _),
      ← Real.rpow_mul (hn x), one_div_mul_cancel hr.ne', Real.rpow_one]
  simpa only [he] using hu

/-- For every real moment order strictly greater than two, Hölder gives the
sharp interpolation powers of the count moment and the averaged vacancy. -/
theorem integral_pair_error_le_holder {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f z d : Ω → ℝ) {p M : ℝ} (hp : 2 < p) (hM : 0 ≤ M)
    (hf : Integrable f ν) (hz : Integrable (fun x => z x ^ p) ν) (hd : Integrable d ν)
    (hpos : ∀ x, 0 ≤ d x) (hle : ∀ x, d x ≤ z x)
    (herr : ∀ x, |f x| ≤ 2 * M * z x * d x) :
    |∫ x, f x ∂ν| ≤ 2 * M * (∫ x, z x ^ p ∂ν) ^ (1 / (p - 1)) *
      (∫ x, d x ∂ν) ^ ((p - 2) / (p - 1)) := by
  let r := p - 1
  let s := r / (r - 1)
  have hr₁ : 1 < r := by dsimp [r]; linarith
  have hr : 0 < r := zero_lt_one.trans hr₁
  have hs : 0 < s := div_pos hr (sub_pos.mpr hr₁)
  have hc : r.HolderConjugate s := (Real.holderConjugate_iff_eq_conjExponent hr₁).mpr rfl
  have hx : 1 / r + 1 / s = 1 := by
    simpa only [one_div] using (Real.holderConjugate_iff.mp hc).2
  letI : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal s) := by
    apply ENNReal.holderConjugate_iff.mpr
    rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_inv_of_pos hs,
      ← ENNReal.ofReal_add (inv_nonneg.mpr hr.le) (inv_nonneg.mpr hs.le),
      (Real.holderConjugate_iff.mp hc).2, ENNReal.ofReal_one]
  let F := fun x => (z x ^ p) ^ (1 / r)
  let G := fun x => d x ^ (1 / s)
  have hz₀ (x : Ω) : 0 ≤ z x := (hpos x).trans (hle x)
  have hF : MemLp F (ENNReal.ofReal r) ν :=
    memLp_integrable_root hz (fun x => Real.rpow_nonneg (hz₀ x) p) hr
  have hG : MemLp G (ENNReal.ofReal s) ν := memLp_integrable_root hd hpos hs
  have hprod : MemLp (G * F) 1 ν := hF.mul hG
  have hprod' := memLp_one_iff_integrable.mp hprod
  change Integrable (fun x => G x * F x) ν at hprod'
  have hFG : Integrable (fun x => F x * G x) ν := by simpa only [mul_comm] using hprod'
  have hpF (x : Ω) : F x ^ r = z x ^ p := by
    rw [show F x = (z x ^ p) ^ (1 / r) from rfl,
      ← Real.rpow_mul (Real.rpow_nonneg (hz₀ x) p), one_div_mul_cancel hr.ne', Real.rpow_one]
  have hpG (x : Ω) : G x ^ s = d x := by
    rw [show G x = d x ^ (1 / s) from rfl,
      ← Real.rpow_mul (hpos x), one_div_mul_cancel hs.ne', Real.rpow_one]
  have hp' : p * (1 / r) = 1 + 1 / r := by
    field_simp [hr.ne']
    dsimp [r]
    ring
  have hpoint (x : Ω) : z x * d x ≤ F x * G x := by
    have he : d x ^ (1 / r) * d x ^ (1 / s) = d x := by
      rw [← Real.rpow_add_of_nonneg (hpos x) (by positivity) (by positivity), hx, Real.rpow_one]
    have he' : F x = z x * z x ^ (1 / r) := by
      dsimp [F]
      rw [← Real.rpow_mul (hz₀ x), hp', Real.rpow_add_of_nonneg (hz₀ x) zero_le_one
        (by positivity), Real.rpow_one]
    calc
      z x * d x = (z x * d x ^ (1 / r)) * G x := by
        dsimp [G]
        rw [mul_assoc, he]
      _ ≤ (z x * z x ^ (1 / r)) * G x := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hpos x) _)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hpos x) (hle x) (by positivity)) (hz₀ x)
      _ = _ := by rw [he']
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (f := F) (g := G) hc
    (ae_of_all ν (fun x => Real.rpow_nonneg (Real.rpow_nonneg (hz₀ x) p) (1 / r)))
    (ae_of_all ν (fun x => Real.rpow_nonneg (hpos x) (1 / s))) hF hG
  simp only [hpF, hpG] at hHolder
  have hs' : 1 / s = (p - 2) / (p - 1) := by
    dsimp only [s, r]
    rw [one_div, inv_div]
    ring
  calc
    _ ≤ ∫ x, |f x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, (2 * M) * (F x * G x) ∂ν := by
      apply integral_mono (by simpa only [Real.norm_eq_abs] using hf.norm) (hFG.const_mul _)
      intro x
      exact (herr x).trans (by
        rw [mul_assoc (2 * M)]
        exact mul_le_mul_of_nonneg_left (hpoint x) (by positivity))
    _ = 2 * M * (∫ x, F x * G x ∂ν) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hHolder (show 0 ≤ 2 * M by positivity)
      simpa only [r, hs', ← mul_assoc] using hh

end RiemannResearch.Analysis.PairVacancyMoment

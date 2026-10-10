import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

-- This private project has no Mathlib Apache license header.
set_option linter.style.header false in
/-!
# Logarithmic growth exponents and exact subpower transfers

The extended-real limsup avoids assuming boundedness of an unknown arithmetic
energy. A zero exponent is exactly eventual subpower upper growth.
Subpower perturbations preserve the exponent; the functions may be signed.

Source: the energy-exponent argument in the user-provided annular research
record, Section 13.5, and an independently assembled extension to signed
perturbations. NIST DLMF 2.5(i), https://dlmf.nist.gov/2.5, supplies only the
classical Mellin context. No arithmetic cancellation estimate is proved here.
-/

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.Analysis.LogarithmicGrowth

def slope (E : ℝ → ℝ) (X : ℝ) : ℝ :=
  Real.log (1 + max (E X) 0) / Real.log X

def exponent (E : ℝ → ℝ) : EReal :=
  Filter.limsup (fun X : ℝ => (slope E X : EReal)) atTop

def PowerUpperBound (E : ℝ → ℝ) (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ X : ℝ in atTop, E X ≤ C * X ^ p

def SubpowerUpperBound (E : ℝ → ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → PowerUpperBound E p

theorem slope_nonneg {E : ℝ → ℝ} {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ slope E X := by
  apply div_nonneg
  · exact Real.log_nonneg (by linarith [le_max_right (E X) 0])
  · exact Real.log_nonneg hX

theorem slope_le_iff {E : ℝ → ℝ} {X p : ℝ} (hX : 1 < X) :
    slope E X ≤ p ↔ 1 + max (E X) 0 ≤ X ^ p := by
  unfold slope
  rw [div_le_iff₀ (Real.log_pos hX), ← Real.log_rpow (by linarith : 0 < X) p]
  exact Real.log_le_log_iff (by linarith [le_max_right (E X) 0])
    (Real.rpow_pos_of_pos (by linarith) _)

theorem slope_lt_iff {E : ℝ → ℝ} {X p : ℝ} (hX : 1 < X) :
    slope E X < p ↔ 1 + max (E X) 0 < X ^ p := by
  unfold slope
  rw [div_lt_iff₀ (Real.log_pos hX), ← Real.log_rpow (by linarith : 0 < X) p]
  exact Real.log_lt_log_iff (by linarith [le_max_right (E X) 0])
    (Real.rpow_pos_of_pos (by linarith) _)

theorem exponent_nonneg (E : ℝ → ℝ) : 0 ≤ exponent E := by
  refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  exact_mod_cast (slope_nonneg (E := E) (by linarith : 1 ≤ X))

theorem eventually_slope_lt_of_power {E : ℝ → ℝ} {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (h : PowerUpperBound E p) :
    ∀ᶠ X : ℝ in atTop, slope E X < q := by
  obtain ⟨C, hC⟩ := h
  let r : ℝ := (p + q) / 2
  have hpr : p < r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  have hlog : ∀ᶠ X : ℝ in atTop,
      Real.log (1 + max C 0) / (r - p) ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (Real.log (1 + max C 0) / (r - p)))
  have hpow : ∀ᶠ X : ℝ in atTop, 1 + max C 0 ≤ X ^ (r - p) := by
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with X hX hX2
    apply (Real.log_le_log_iff (by linarith [le_max_right C 0] :
      0 < 1 + max C 0) (Real.rpow_pos_of_pos (by linarith : 0 < X) _)).mp
    rw [Real.log_rpow (by linarith : 0 < X)]
    have hmul := (div_le_iff₀ (by linarith : 0 < r - p)).mp hX
    linarith
  filter_upwards [hC, hpow, eventually_ge_atTop (2 : ℝ)] with X hCX hK hX
  have hX0 : 0 < X := by linarith
  have hone : 1 ≤ X ^ p := Real.one_le_rpow (by linarith) hp
  have hmax : max (E X) 0 ≤ max C 0 * X ^ p := by
    apply max_le
    · exact hCX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hX0.le _))
    · exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hX0.le _)
  have hbound : 1 + max (E X) 0 ≤ X ^ r := by
    calc
      _ ≤ (1 + max C 0) * X ^ p := by nlinarith
      _ ≤ X ^ (r - p) * X ^ p :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hX0.le _)
      _ = X ^ r := by rw [← Real.rpow_add hX0]; congr 1; ring
  exact ((slope_le_iff (by linarith)).2 hbound).trans_lt hrq

theorem exponent_le_of_power {E : ℝ → ℝ} {p : ℝ}
    (hp : 0 ≤ p) (h : PowerUpperBound E p) : exponent E ≤ (p : EReal) := by
  apply (Filter.limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro y hy
  obtain ⟨q, hpq, hqy⟩ := EReal.exists_between_coe_real hy
  have hpq' : p < q := by exact_mod_cast hpq
  filter_upwards [eventually_slope_lt_of_power hp hpq' h] with X hX
  exact (show (slope E X : EReal) < (q : EReal) by exact_mod_cast hX).trans hqy

theorem power_of_exponent_lt {E : ℝ → ℝ} {p : ℝ}
    (hp : exponent E < (p : EReal)) : PowerUpperBound E p := by
  have hbound : ∀ᶠ X : ℝ in atTop, (slope E X : EReal) < (p : EReal) :=
    (Filter.limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mp
      (le_refl (exponent E)) _ hp
  refine ⟨1, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (2 : ℝ)] with X hX hX2
  have hX' : slope E X < p := by exact_mod_cast hX
  have hb := (slope_lt_iff (by linarith : 1 < X)).mp hX'
  have hm := le_max_left (E X) 0
  simpa only [one_mul] using (show E X ≤ X ^ p by linarith)

theorem subpower_iff_exponent_zero (E : ℝ → ℝ) :
    SubpowerUpperBound E ↔ exponent E = 0 := by
  constructor
  · intro h
    apply le_antisymm _ (exponent_nonneg E)
    by_contra hn
    have hpos : (0 : EReal) < exponent E := lt_of_not_ge hn
    obtain ⟨p, hp, hpE⟩ := EReal.exists_between_coe_real hpos
    have hp' : 0 < p := by exact_mod_cast hp
    exact (not_le_of_gt hpE) (exponent_le_of_power hp'.le (h p hp'))
  · intro h p hp
    apply power_of_exponent_lt
    rw [h]
    exact_mod_cast hp

theorem exponent_ge_of_cofinal_power {E : ℝ → ℝ} {q : ℝ}
    (h : ∀ p : ℝ, 0 ≤ p → p < q → ∀ X₀ : ℝ,
      ∃ X : ℝ, max 2 X₀ ≤ X ∧ X ^ p < E X) :
    (q : EReal) ≤ exponent E := by
  apply (Filter.le_limsup_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro y hy
  obtain ⟨p, hyp, hpq⟩ := EReal.exists_between_coe_real hy
  have hpq' : p < q := by exact_mod_cast hpq
  by_cases hp : 0 ≤ p
  · apply Filter.frequently_atTop.mpr
    intro X₀
    obtain ⟨X, hX, he⟩ := h p hp hpq' X₀
    refine ⟨X, (le_max_right _ _).trans hX, ?_⟩
    have hs : p < slope E X := by
      apply lt_of_not_ge
      intro hn
      have hb := (slope_le_iff (by linarith [le_max_left (2 : ℝ) X₀] :
        1 < X)).mp hn
      linarith [le_max_left (E X) 0]
    exact hyp.trans (show (p : EReal) < (slope E X : EReal) by exact_mod_cast hs)
  · have hp0 : p < 0 := lt_of_not_ge hp
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    exact hyp.trans_le (show (p : EReal) ≤ (slope E X : EReal) by
      exact_mod_cast hp0.le.trans (slope_nonneg (E := E) (by linarith)))

theorem power_add_of_power {E F : ℝ → ℝ} {p : ℝ}
    (hE : PowerUpperBound E p) (hF : PowerUpperBound F p) :
    PowerUpperBound (fun X => E X + F X) p := by
  obtain ⟨C, hC⟩ := hE
  obtain ⟨D, hD⟩ := hF
  refine ⟨C + D, ?_⟩
  filter_upwards [hC, hD] with X hX hX'
  nlinarith

theorem power_of_le_add {E F D : ℝ → ℝ} {p : ℝ}
    (hEF : ∀ᶠ X : ℝ in atTop, E X ≤ F X + D X)
    (hF : PowerUpperBound F p) (hD : PowerUpperBound D p) :
    PowerUpperBound E p := by
  obtain ⟨C, hC⟩ := power_add_of_power hF hD
  exact ⟨C, hEF.and hC |>.mono (fun _ h => h.1.trans h.2)⟩

theorem exponent_eq_of_subpower_difference {E F : ℝ → ℝ}
    (h : SubpowerUpperBound (fun X => |E X - F X|)) :
    exponent E = exponent F := by
  suffices horder : ∀ E F : ℝ → ℝ,
      SubpowerUpperBound (fun X => |E X - F X|) → exponent E ≤ exponent F by
    apply le_antisymm (horder E F h)
    apply horder F E
    simpa only [abs_sub_comm] using h
  intro E F hEF
  by_contra hn
  have hlt : exponent F < exponent E := lt_of_not_ge hn
  obtain ⟨p, hFp, hpE⟩ := EReal.exists_between_coe_real hlt
  have hp : 0 < p := by
    exact_mod_cast (exponent_nonneg F).trans_lt hFp
  have hEp : PowerUpperBound E p := power_of_le_add
    (Eventually.of_forall (fun X => by linarith [le_abs_self (E X - F X)]))
    (power_of_exponent_lt hFp) (hEF p hp)
  exact (not_le_of_gt hpE) (exponent_le_of_power hp.le hEp)

/-- A bounded additive correction is subpower at every positive exponent. -/
theorem subpower_of_eventually_bounded {E : ℝ → ℝ} {K : ℝ}
    (h : ∀ᶠ X : ℝ in atTop, E X ≤ K) : SubpowerUpperBound E := by
  intro p hp
  refine ⟨max K 0, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  exact hX.trans ((le_max_left _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.one_le_rpow hX1 hp.le) (le_max_right K 0)))

/-- A logarithmic upper estimate supplies eventual subpower control. -/
theorem subpower_of_eventual_log_bound {E : ℝ → ℝ} {C : ℝ}
    (h : ∀ᶠ X : ℝ in atTop, E X ≤ C * Real.log X) :
    SubpowerUpperBound E := by
  intro p hp
  refine ⟨max C 0 / p, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  calc
    E X ≤ C * Real.log X := hX
    _ ≤ max C 0 * Real.log X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hX1)
    _ ≤ max C 0 * (X ^ p / p) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div
        (zero_le_one.trans hX1) hp) (le_max_right _ _)
    _ = (max C 0 / p) * X ^ p := by ring

end RiemannResearch.Analysis.LogarithmicGrowth

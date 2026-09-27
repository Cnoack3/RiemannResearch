import RiemannResearch.RH.BaezDuarteCenteredBridge
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Natural-dilation to centered Pareto approximation

The analytic density assertion in L. Báez-Duarte, "A strengthening of the
Nyman--Beurling criterion for the Riemann Hypothesis", Theorem 1.1,
https://arxiv.org/abs/math/0202141, is stated below as a proposition; the file does not assert it.
The lemmas prove its elementary normalization transfer. The harmless
constant 10 avoids using an improper-integral formula: the coefficient charge
is controlled on (1,2] alone.
-/

namespace RiemannResearch.RH.Pareto.BaezDuarte

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable def naturalSum (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ s, a d * Int.fract (1 / ((d : ℝ) * x))

noncomputable def naturalCharge (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, a d / (d : ℝ)

noncomputable def chi (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => 1) x

noncomputable def naturalError (s : Finset ℕ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2)

/-- Finite real-coefficient form of the published natural-dilation density
conclusion. The implication from RH is not assumed by any theorem in this file. -/
def NaturalApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℕ, ∃ a : ℕ → ℝ,
    (∀ d ∈ s, 0 < d) ∧ naturalError s a < ENNReal.ofReal ε

theorem chi_eq_one {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : chi x = 1 := by
  simp [chi, hx]

theorem chi_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) : chi x = 0 := by
  have hn : x ∉ Ioc (0 : ℝ) 1 := by intro h; linarith [h.2]
  simp [chi, hn]

theorem naturalSum_eq_charge_div (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) {x : ℝ} (hx : 1 < x) :
    naturalSum s a x = naturalCharge s a / x := by
  unfold naturalSum naturalCharge
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hs d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_of_lt (hs d hd))
  have hx0 : 0 < x := by linarith
  have hdx : 1 < (d : ℝ) * x := by
    have hmul := mul_nonneg (show 0 ≤ (d : ℝ) - 1 by linarith) hx0.le
    nlinarith
  rw [Int.fract_eq_self.mpr ⟨by positivity,
    (div_lt_one (by positivity : 0 < (d : ℝ) * x)).mpr hdx⟩]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem centered_sum_eq (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    (∑ d ∈ s, a d *
      (Int.fract (1 / ((d : ℝ) * x)) -
        (1 / (d : ℝ)) * Int.fract (1 / x))) =
      naturalSum s a x - naturalCharge s a * Int.fract (1 / x) := by
  unfold naturalSum naturalCharge
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The coefficient charge is controlled by the error on the finite interval
(1,2], so no improper integration theorem is needed here. -/
theorem charge_sq_le_four_error (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    ENNReal.ofReal ((naturalCharge s a) ^ 2) ≤ 4 * naturalError s a := by
  have hp (x : ℝ) (hx : x ∈ Ioc (1 : ℝ) 2) :
      ENNReal.ofReal ((naturalCharge s a) ^ 2) ≤
        4 * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) := by
    rw [chi_eq_zero_of_one_lt hx.1, naturalSum_eq_charge_div s a hs hx.1]
    have hx0 : 0 < x := by linarith [hx.1]
    have hx2 : x ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg (show 0 ≤ 2 - x by linarith [hx.2])
        (show 0 ≤ 2 + x by linarith [hx.1])]
    have hmul : (naturalCharge s a / x) * x = naturalCharge s a :=
      div_mul_cancel₀ _ (ne_of_gt hx0)
    have hreal : (naturalCharge s a) ^ 2 ≤
        4 * (0 - naturalCharge s a / x) ^ 2 := by
      have hm := mul_nonneg (sq_nonneg (naturalCharge s a / x))
        (show 0 ≤ 4 - x ^ 2 by linarith)
      have hsq := congrArg (fun z : ℝ => z ^ 2) hmul
      nlinarith only [hm, hsq]
    calc
      _ ≤ ENNReal.ofReal (4 * (0 - naturalCharge s a / x) ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc
    _ = ∫⁻ _x : ℝ in Ioc 1 2, ENNReal.ofReal ((naturalCharge s a) ^ 2) := by
      norm_num
    _ ≤ ∫⁻ x : ℝ in Ioc 1 2,
        4 * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hp x hx
    _ = 4 * ∫⁻ x : ℝ in Ioc 1 2,
        ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4 * naturalError s a := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply lintegral_mono_set
      intro x hx
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hx.1

/-- Centering a finite natural-dilation sum preserves approximation, with an
explicit universal squared-error loss. -/
theorem centeredError_le_ten_naturalError (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) : centeredError s a ≤ 10 * naturalError s a := by
  have hp (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      ENNReal.ofReal ((1 - ∑ d ∈ s, a d *
        (Int.fract (1 / ((d : ℝ) * x)) -
          (1 / (d : ℝ)) * Int.fract (1 / x))) ^ 2) ≤
        2 * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) +
          2 * ENNReal.ofReal ((naturalCharge s a) ^ 2) := by
    rw [centered_sum_eq, chi_eq_one hx]
    have hfrac0 := Int.fract_nonneg (1 / x)
    have hfrac1 := Int.fract_lt_one (1 / x)
    have hfrac2 : (Int.fract (1 / x)) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - Int.fract (1 / x) by linarith)
        (show 0 ≤ 1 + Int.fract (1 / x) by linarith)]
    have hreal : (1 - (naturalSum s a x -
        naturalCharge s a * Int.fract (1 / x))) ^ 2 ≤
          2 * (1 - naturalSum s a x) ^ 2 + 2 * (naturalCharge s a) ^ 2 := by
      have hB := mul_nonneg (sq_nonneg (naturalCharge s a))
        (show 0 ≤ 1 - (Int.fract (1 / x)) ^ 2 by linarith)
      nlinarith [sq_nonneg (1 - naturalSum s a x -
        naturalCharge s a * Int.fract (1 / x))]
    calc
      _ ≤ ENNReal.ofReal
          (2 * (1 - naturalSum s a x) ^ 2 + 2 * (naturalCharge s a) ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num
  calc
    centeredError s a ≤ ∫⁻ x : ℝ in Ioc 0 1,
        (2 * ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2) +
          2 * ENNReal.ofReal ((naturalCharge s a) ^ 2)) := by
      unfold centeredError
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hp x hx
    _ = 2 * (∫⁻ x : ℝ in Ioc 0 1,
        ENNReal.ofReal ((chi x - naturalSum s a x) ^ 2)) +
          2 * ENNReal.ofReal ((naturalCharge s a) ^ 2) := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ (by norm_num)]
      simp
    _ ≤ 2 * naturalError s a + 2 * (4 * naturalError s a) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact lintegral_mono_set (fun x hx => hx.1)
      · exact mul_le_mul_of_nonneg_left (charge_sq_le_four_error s a hs) (by positivity)
    _ = 10 * naturalError s a := by ring

theorem naturalApproximation_implies_centeredApproximation
    (h : NaturalApproximation) : CenteredApproximation := by
  intro ε hε
  obtain ⟨s, a, hs, he⟩ := h (ε / 20) (by positivity)
  refine ⟨s, a, hs, ?_⟩
  calc
    centeredError s a ≤ 10 * naturalError s a := centeredError_le_ten_naturalError s a hs
    _ ≤ 10 * ENNReal.ofReal (ε / 20) := mul_le_mul_of_nonneg_left he.le (by positivity)
    _ = ENNReal.ofReal (10 * (ε / 20)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ < ENNReal.ofReal ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end RiemannResearch.RH.Pareto.BaezDuarte


namespace RiemannResearch.RH.Pareto.BaezDuarte

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable def correctedCoefficient (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  (if d ∈ s then a d else 0) - if d = 1 then naturalCharge s a else 0

/-- Adding the index one absorbs precisely the coefficient charge. -/
theorem corrected_naturalSum_eq (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    naturalSum (insert 1 s) (correctedCoefficient s a) x =
      naturalSum s a x - naturalCharge s a * Int.fract (1 / x) := by
  classical
  have hbase : (∑ d ∈ insert 1 s,
      (if d ∈ s then a d else 0) * Int.fract (1 / ((d : ℝ) * x))) =
      naturalSum s a x := by
    unfold naturalSum
    by_cases h1 : 1 ∈ s
    · rw [Finset.insert_eq_of_mem h1]
      apply Finset.sum_congr rfl
      intro d hd
      simp [hd]
    · rw [Finset.sum_insert h1]
      simp only [if_neg h1, zero_mul, zero_add]
      apply Finset.sum_congr rfl
      intro d hd
      simp [hd]
  have hcharge : (∑ d ∈ insert 1 s,
      (if d = 1 then naturalCharge s a else 0) *
        Int.fract (1 / ((d : ℝ) * x))) =
      naturalCharge s a * Int.fract (1 / x) := by
    calc
      _ = (if (1 : ℕ) = 1 then naturalCharge s a else 0) *
          Int.fract (1 / (((1 : ℕ) : ℝ) * x)) := by
        apply Finset.sum_eq_single 1
        · intro d hd hd1
          simp [hd1]
        · intro hnot
          exact False.elim (hnot (Finset.mem_insert_self 1 s))
      _ = _ := by simp
  unfold naturalSum correctedCoefficient
  simp only [sub_mul, Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) hbase hcharge

theorem corrected_naturalSum_eq_zero_of_one_lt (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) {x : ℝ} (hx : 1 < x) :
    naturalSum (insert 1 s) (correctedCoefficient s a) x = 0 := by
  rw [corrected_naturalSum_eq, naturalSum_eq_charge_div s a hs hx]
  have hx0 : 0 < x := by linarith
  rw [Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hx0).mpr hx⟩]
  ring

/-- Conversely the correction gives exact equality of errors on the complete
source domain, because it vanishes identically to the right of one. -/
theorem corrected_naturalError_eq (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    naturalError (insert 1 s) (correctedCoefficient s a) = centeredError s a := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext x
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  unfold naturalError
  rw [hsplit, lintegral_union measurableSet_Ioi hdis]
  have hhead : (∫⁻ x : ℝ in Ioc 0 1,
      ENNReal.ofReal ((chi x - naturalSum (insert 1 s)
        (correctedCoefficient s a) x) ^ 2)) = centeredError s a := by
    unfold centeredError
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [chi_eq_one hx, corrected_naturalSum_eq, ← centered_sum_eq]
  have htail : (∫⁻ x : ℝ in Ioi 1,
      ENNReal.ofReal ((chi x - naturalSum (insert 1 s)
        (correctedCoefficient s a) x) ^ 2)) = 0 := by
    calc
      _ = ∫⁻ _x : ℝ in Ioi 1, (0 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [chi_eq_zero_of_one_lt hx,
          corrected_naturalSum_eq_zero_of_one_lt s a hs hx]
        norm_num
      _ = 0 := by simp
  rw [hhead, htail, add_zero]

theorem centeredApproximation_implies_naturalApproximation
    (h : CenteredApproximation) : NaturalApproximation := by
  intro ε hε
  obtain ⟨s, a, hs, he⟩ := h ε hε
  refine ⟨insert 1 s, correctedCoefficient s a, ?_, ?_⟩
  · intro d hd
    rcases Finset.mem_insert.mp hd with h1 | hd
    · subst d
      norm_num
    · exact hs d hd
  · rwa [corrected_naturalError_eq s a hs]

theorem naturalApproximation_iff_centeredApproximation :
    NaturalApproximation ↔ CenteredApproximation :=
  ⟨naturalApproximation_implies_centeredApproximation,
    centeredApproximation_implies_naturalApproximation⟩

end RiemannResearch.RH.Pareto.BaezDuarte

namespace RiemannResearch.RH.Pareto.BaezDuarte

/-- Exact correspondence with the existing Pareto residue closure. -/
theorem naturalApproximation_iff_one_mem :
    NaturalApproximation ↔ hilbertOne ∈ CoefficientStabilization.closedSpace :=
  naturalApproximation_iff_centeredApproximation.trans centeredApproximation_iff_one_mem

/-- Conditional research reduction: the sole external analytic input is the
RH-to-natural-approximation direction of Báez-Duarte's Theorem 1.1.
The complete normalization transfer is proved above; this is not a provider
of the analytic input itself. -/
theorem one_mem_of_riemannHypothesis
    (hBaezDuarte : RiemannHypothesis → NaturalApproximation)
    (hRH : RiemannHypothesis) : hilbertOne ∈ CoefficientStabilization.closedSpace :=
  naturalApproximation_iff_one_mem.mp (hBaezDuarte hRH)

end RiemannResearch.RH.Pareto.BaezDuarte

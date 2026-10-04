import RiemannResearch.RH.ActualIntegratedZeroTruncation
import Mathlib.Tactic.Abel

/-!
# Real-height truncation of the actual integrated zeta-zero series

The real-height proof uses Y ≥ 10 and K = floor Y.
The only analytic input is the proved actual unit-window zero count.
-/

noncomputable section
open Complex Set Filter Zeta23
open scoped BigOperators

namespace RiemannResearch.RH.ActualIntegratedZeroRealTruncation

open ActualIntegratedZeroSeries ActualIntegratedZeroTruncation

abbrev TailZeroReal (Y : ℝ) := {ρ : ActualZero // Y < |(ρ : ℂ).im|}

/-- Literal real-height version, with an absolute constant uniform in x and Y. -/
theorem actual_real_height_truncation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 10 ≤ Y → ∀ (x : ℝ), 1 ≤ x →
      ‖∑' ρ : TailZeroReal Y, term x ρ.1‖ ≤ C * x * Real.log Y / Y := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨768 * A₀, by linarith, fun Y hY x hx => ?_⟩
  set K : ℕ := ⌊Y⌋₊
  have hfloor : (K : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hupper : Y < (K : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hKreal : (5 : ℝ) ≤ K := by linarith
  have hK : 5 ≤ K := by exact_mod_cast hKreal
  have hhalf : Y / 2 ≤ K := by linarith
  have hlog : Real.log ((K : ℝ) + 3) ≤ 2 * Real.log Y := by
    have h := Real.log_le_log (by linarith : 0 < (K : ℝ) + 3)
      (by nlinarith : (K : ℝ) + 3 ≤ Y ^ 2)
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hscalar : 32 * A₀ * Real.log ((K : ℝ) + 3) / K ≤
      128 * A₀ * Real.log Y / Y := by
    calc
      _ ≤ 32 * A₀ * (2 * Real.log Y) / K := by gcongr
      _ ≤ 32 * A₀ * (2 * Real.log Y) / (Y / 2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by linarith)
            (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))))
          (by linarith) hhalf
      _ = _ := by ring
  have hpart : ∀ u : Finset (TailZeroReal Y),
      (∑ ρ ∈ u, weight ρ.1) ≤ 128 * A₀ * Real.log Y / Y := by
    intro u
    have h := weight_partial_tail_le hA₀ hloc K hK
      (u.map (Function.Embedding.subtype _)) (by
        intro ρ hρ
        obtain ⟨η, _, rfl⟩ := Finset.mem_map.mp hρ
        exact lt_of_le_of_lt hfloor η.2)
    have h' : (∑ ρ ∈ u, weight ρ.1) ≤
        32 * A₀ * Real.log ((K : ℝ) + 3) / K := by
      simpa only [Finset.sum_map, Function.Embedding.coe_subtype] using h
    exact h'.trans hscalar
  have hnonneg : ∀ ρ : TailZeroReal Y, 0 ≤ weight ρ.1 := by
    intro ρ
    unfold weight
    exact div_nonneg (Nat.cast_nonneg _)
      (by linarith [Complex.normSq_nonneg (gammaOf ((ρ.1 : ActualZero) : ℂ))])
  have hs : Summable (fun ρ : TailZeroReal Y => weight ρ.1) :=
    summable_of_sum_le hnonneg hpart
  have ht : (∑' ρ : TailZeroReal Y, weight ρ.1) ≤
      128 * A₀ * Real.log Y / Y := Real.tsum_le_of_sum_le hnonneg hpart
  have hpoint : ∀ ρ : TailZeroReal Y, ‖term x ρ.1‖ ≤ (6 * x) * weight ρ.1 := by
    intro ρ
    apply ActualIntegratedZeroSeries.term_norm_le x hx ρ.1
    linarith [ρ.2]
  have hnorm : ‖∑' ρ : TailZeroReal Y, term x ρ.1‖ ≤
      ∑' ρ : TailZeroReal Y, (6 * x) * weight ρ.1 :=
    tsum_of_norm_bounded (hs.mul_left (6 * x)).hasSum hpoint
  calc
    _ ≤ ∑' ρ : TailZeroReal Y, (6 * x) * weight ρ.1 := hnorm
    _ = (6 * x) * ∑' ρ : TailZeroReal Y, weight ρ.1 := tsum_mul_left
    _ ≤ (6 * x) * (128 * A₀ * Real.log Y / Y) :=
      mul_le_mul_of_nonneg_left ht (by linarith)
    _ = _ := by ring

/-- The actual zero tail is O(x log Y / Y), unconditionally. -/
theorem actual_real_height_tail_isBigO (x : ℝ) (hx : 1 ≤ x) :
    (fun Y : ℝ => ∑' ρ : TailZeroReal Y, term x ρ.1) =O[atTop]
      (fun Y : ℝ => x * Real.log Y / Y) := by
  obtain ⟨C, hC, hbound⟩ := actual_real_height_truncation_bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (10 : ℝ)] with Y hY
  have hnn : 0 ≤ x * Real.log Y / Y :=
    div_nonneg (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))
      (by linarith)
  have h := hbound Y hY x hx
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  simpa only [mul_div_assoc, mul_assoc] using h

/-- The symmetric finite head includes zeros at either boundary ordinate. -/
def headSet (Y : ℝ) : Set ActualZero := {ρ | |(ρ : ℂ).im| ≤ Y}

abbrev HeadZeroReal (Y : ℝ) := headSet Y

theorem finite_headSet (Y : ℝ) : (headSet Y).Finite := by
  have hwin : (zetaZeroConfig.window (-Y - 1) Y).Finite :=
    zetaZeroConfig.finite_window _ _
  have hpre : ((fun ρ : ActualZero => (ρ : ℂ)) ⁻¹'
      zetaZeroConfig.window (-Y - 1) Y).Finite :=
    hwin.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  change |(ρ : ℂ).im| ≤ Y at hρ
  have hb := abs_le.mp hρ
  exact ⟨ρ.property, by linarith [hb.1], hb.2⟩

/-- A genuine finite cutoff, rather than an unspecified enumeration prefix. -/
noncomputable def headFinset (Y : ℝ) : Finset ActualZero :=
  (finite_headSet Y).toFinset

theorem head_sum_eq_finite_sum (x Y : ℝ) :
    (∑' ρ : HeadZeroReal Y, term x ρ.1) =
      ∑ ρ ∈ headFinset Y, term x ρ := by
  have hco : (headFinset Y : Set ActualZero) = headSet Y :=
    (finite_headSet Y).coe_toFinset
  change (∑' ρ : headSet Y, term x ρ.1) = _
  rw [← hco]
  exact Finset.tsum_subtype' (headFinset Y) (term x)

/-- Exact partition of the actual absolutely convergent series, both signs kept. -/
theorem complete_series_eq_head_add_tail (x : ℝ) (hx : 1 ≤ x) (Y : ℝ) :
    (∑' ρ : ActualZero, term x ρ) =
      (∑' ρ : HeadZeroReal Y, term x ρ.1) +
      (∑' ρ : TailZeroReal Y, term x ρ.1) := by
  have hsum := (ActualIntegratedZeroSeries.absolutely_summable x hx).2
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl (headSet Y)
  have hcomp : (∑' ρ : ((headSet Y)ᶜ : Set ActualZero), term x ρ.1) =
      ∑' ρ : TailZeroReal Y, term x ρ.1 := by
    apply tsum_congr_subtype (term x)
    intro ρ
    change (¬ |(ρ : ℂ).im| ≤ Y) ↔ Y < |(ρ : ℂ).im|
    exact not_le
  rw [hcomp] at hsplit
  exact hsplit.symm

/-- Subtracting the precise finite ordinate head leaves the omitted zero tail. -/
theorem exact_finite_head_remainder (x : ℝ) (hx : 1 ≤ x) (Y : ℝ) :
    (∑' ρ : ActualZero, term x ρ) -
      (∑ ρ ∈ headFinset Y, term x ρ) =
      ∑' ρ : TailZeroReal Y, term x ρ.1 := by
  rw [complete_series_eq_head_add_tail x hx Y, head_sum_eq_finite_sum]
  abel

/-- The explicit rate bounds the error of the actual finite symmetric zero head. -/
theorem actual_finite_head_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 10 ≤ Y → ∀ (x : ℝ), 1 ≤ x →
      ‖(∑' ρ : ActualZero, term x ρ) -
        (∑ ρ ∈ headFinset Y, term x ρ)‖ ≤ C * x * Real.log Y / Y := by
  obtain ⟨C, hC, hbound⟩ := actual_real_height_truncation_bound
  refine ⟨C, hC, fun Y hY x hx => ?_⟩
  rw [exact_finite_head_remainder x hx Y]
  exact hbound Y hY x hx

end RiemannResearch.RH.ActualIntegratedZeroRealTruncation

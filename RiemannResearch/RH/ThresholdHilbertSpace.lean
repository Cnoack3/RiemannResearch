import RiemannResearch.RH.ThresholdDilationEnergy
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual weighted sequence Hilbert space

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Sections 1–2. The weighted space is realized unitarily on real l2 by
multiplying physical coordinate k by sqrt(1/(k(k+1))). Coordinate zero is
anchored, not an additional Hilbert coordinate. No RH hypothesis occurs.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

abbrev ThresholdHilbert := lp (fun _ : ℕ => ℝ) 2

/-- Physical, zero-anchored coordinates of the genuine complete Hilbert space. -/
def hilbertSequence (f : ThresholdHilbert) : ℕ → ℝ
  | 0 => 0
  | n+1 => f n / Real.sqrt (paretoWeight n)

@[simp] theorem hilbertSequence_zero (f : ThresholdHilbert) :
    hilbertSequence f 0 = 0 := rfl

@[simp] theorem hilbertSequence_succ (f : ThresholdHilbert) (n : ℕ) :
    hilbertSequence f (n+1) = f n / Real.sqrt (paretoWeight n) := rfl

private theorem pw_pos (n : ℕ) : 0 < paretoWeight n := by
  unfold paretoWeight
  positivity

private theorem sqrt_pw_ne (n : ℕ) : Real.sqrt (paretoWeight n) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (pw_pos n))

theorem hilbertSequence_weighted_square (f : ThresholdHilbert) (n : ℕ) :
    positiveWeight (n+1) * hilbertSequence f (n+1)^2 = (f n)^2 := by
  rw [positiveWeight_succ, hilbertSequence_succ, div_pow,
    Real.sq_sqrt (le_of_lt (pw_pos n))]
  field_simp [ne_of_gt (pw_pos n)]

theorem hilbert_coordinate_square_summable (f : ThresholdHilbert) :
    Summable (fun n => (f n)^2) := by
  have h := Memℓp.summable (show 0 < (2 : ENNReal).toReal by norm_num) f.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

theorem hilbertSequence_square_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveWeight k * hilbertSequence f k ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f

theorem hilbert_norm_sq (f : ThresholdHilbert) :
    ‖f‖^2 = ∑' n, (f n)^2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1
  funext n
  simp [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The norm is exactly the paper's infinite weighted norm. -/
theorem hilbert_norm_weighted_sq (f : ThresholdHilbert) :
    ‖f‖^2 = ∑' k, positiveWeight k * hilbertSequence f k^2 := by
  rw [(hilbertSequence_square_summable f).tsum_eq_zero_add]
  simp only [hilbertSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_add, hilbertSequence_weighted_square]
  exact hilbert_norm_sq f

def hilbertSequenceLinear : ThresholdHilbert →ₗ[ℝ] (ℕ → ℝ) where
  toFun := hilbertSequence
  map_add' f g := by
    funext k
    cases k with
    | zero => simp [hilbertSequence]
    | succ n => simp [hilbertSequence, add_div]
  map_smul' c f := by
    funext k
    cases k with
    | zero => simp [hilbertSequence]
    | succ n => simp [hilbertSequence, mul_div_assoc]

theorem hilbertSequence_injective : Function.Injective hilbertSequence := by
  intro f g h
  apply Subtype.ext
  funext n
  have hn := congrFun h (n+1)
  simpa only [hilbertSequence_succ, div_left_inj' (sqrt_pw_ne n)] using hn

/-- Encode every weighted-square-summable physical sequence. -/
def sequenceHilbert (g : ℕ → ℝ)
    (hg : Summable (fun k => positiveWeight k * g k^2)) : ThresholdHilbert :=
  ⟨fun n => Real.sqrt (paretoWeight n) * g (n+1), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    have hs := (summable_nat_add_iff 1).mpr hg
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      mul_pow, Real.sq_sqrt (le_of_lt (pw_pos _)), positiveWeight_succ] using hs⟩

@[simp] theorem hilbertSequence_sequenceHilbert (g : ℕ → ℝ)
    (hg : Summable (fun k => positiveWeight k * g k^2)) (hg0 : g 0 = 0) :
    hilbertSequence (sequenceHilbert g hg) = g := by
  funext k
  cases k with
  | zero => exact hg0.symm
  | succ n =>
    change Real.sqrt (paretoWeight n) * g (n+1) / Real.sqrt (paretoWeight n) = g (n+1)
    field_simp [sqrt_pw_ne n]

/-- This characterization supplies every physical weighted H vector, not merely
bounded or periodic sequences. -/
theorem hilbertSequence_range (g : ℕ → ℝ) :
    (∃ f : ThresholdHilbert, hilbertSequence f = g) ↔
      g 0 = 0 ∧ Summable (fun k => positiveWeight k * g k^2) := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨rfl, hilbertSequence_square_summable f⟩
  · rintro ⟨h0, hs⟩
    exact ⟨sequenceHilbert g hs, hilbertSequence_sequenceHilbert g hs h0⟩

end
end RiemannResearch.RH.Pareto

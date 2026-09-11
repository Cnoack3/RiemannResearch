import RiemannResearch.RH.DyadicResidueFourierBridge
import RiemannResearch.RH.DyadicResidueConductorBounds
import RiemannResearch.RH.DyadicRegularizedNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Damped conductor summability and exact scalar Fourier interchange

Source: continuation of the user-provided
`FourierResidueBridgeVerification20260911(1).md`, September 11, 2026.
The logarithmically weighted actual Möbius coefficients are summable for
every positive damping. The second part assembles the exact residue
Fourier rows under a logarithmic conductor/frequency provider.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- A single absolute constant controls every positive conductor and
every frequency by the product of the two logarithmic weights. -/
theorem dyadicResidueFourierSymbol_logarithmic_product_majorant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ), 0 < a → ∀ h : ℤ,
      ‖dyadicResidueFourierSymbol a h‖ ≤
        C * (1 + Real.log (a : ℝ)) * (1 + Real.log (2 + |(h : ℝ)|)) := by
  let A : ℝ := |2 * Real.pi / Real.log 2|
  let L : ℝ := Real.log (1 + A)
  let C : ℝ := 5 + 2 * L
  have hA : 0 ≤ A := abs_nonneg _
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC2 : 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro a ha h
  have hω : |dyadicLogFrequency h| = A * |(h : ℝ)| := by
    unfold dyadicLogFrequency
    calc
      |2 * Real.pi * (h : ℝ) / Real.log 2| =
          |(2 * Real.pi / Real.log 2) * (h : ℝ)| := by congr 1; ring
      _ = A * |(h : ℝ)| := abs_mul _ _
  have hlog : Real.log (1 + |dyadicLogFrequency h|) ≤
      L + Real.log (2 + |(h : ℝ)|) := by
    rw [hω]
    calc
      Real.log (1 + A * |(h : ℝ)|) ≤ Real.log ((1 + A) * (2 + |(h : ℝ)|)) := by
        apply Real.log_le_log (by positivity)
        nlinarith [abs_nonneg (h : ℝ)]
      _ = L + Real.log (2 + |(h : ℝ)|) := by
        rw [Real.log_mul (by positivity : 1 + A ≠ 0)
          (by positivity : 2 + |(h : ℝ)| ≠ 0)]
  have hx : 0 ≤ Real.log (a : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ a from ha))
  have hy : 0 ≤ Real.log (2 + |(h : ℝ)|) :=
    Real.log_nonneg (by linarith [abs_nonneg (h : ℝ)])
  have hCx : 2 ≤ C * (1 + Real.log (a : ℝ)) := by
    nlinarith [mul_nonneg hC hx]
  calc
    _ ≤ 5 + 2 * Real.log (a : ℝ) + 2 * Real.log (1 + |dyadicLogFrequency h|) :=
      norm_dyadicResidueFourierSymbol_le_log_conductor a ha h
    _ ≤ C + 2 * Real.log (a : ℝ) + 2 * Real.log (2 + |(h : ℝ)|) := by
      dsimp [C]
      linarith
    _ ≤ C * (1 + Real.log (a : ℝ)) + 2 * Real.log (2 + |(h : ℝ)|) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hx]
    _ ≤ C * (1 + Real.log (a : ℝ)) * (1 + Real.log (2 + |(h : ℝ)|)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hCx) hy]

/-- The genuine damped Möbius conductor weights remain absolutely summable
after the logarithmic conductor cost. No Mertens bound is assumed. -/
theorem summable_abs_dampedMobius_div_mul_one_add_log
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      |(ArithmeticFunction.moebius (n + 1) : ℝ) / (n + 1 : ℝ) ^ (1 + ε)| *
        (1 + Real.log (n + 1 : ℝ))) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hmajor := (regularizationZetaSeries_summable hε).add
    ((regularizationZetaSeries_summable hhalf).mul_left ((ε / 2)⁻¹))
  apply hmajor.of_nonneg_of_le
  · intro n
    have hlog : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    positivity
  · intro n
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hμ : |(ArithmeticFunction.moebius (n + 1) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n + 1))
    have hlog : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hweight :
        |(ArithmeticFunction.moebius (n + 1) : ℝ) / (n + 1 : ℝ) ^ (1 + ε)| ≤
          (n + 1 : ℝ) ^ (-(1 + ε)) := by
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_neg hn.le]
      simpa only [one_div] using
        div_le_div_of_nonneg_right hμ (Real.rpow_nonneg hn.le (1 + ε))
    have hlogpower := Real.log_le_rpow_div hn.le hhalf
    have hpower :
        (n + 1 : ℝ) ^ (-(1 + ε)) * (n + 1 : ℝ) ^ (ε / 2) =
          (n + 1 : ℝ) ^ (-(1 + ε / 2)) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    calc
      _ ≤ (n + 1 : ℝ) ^ (-(1 + ε)) * (1 + Real.log (n + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ = (n + 1 : ℝ) ^ (-(1 + ε)) +
          (n + 1 : ℝ) ^ (-(1 + ε)) * Real.log (n + 1 : ℝ) := by ring
      _ ≤ (n + 1 : ℝ) ^ (-(1 + ε)) +
          (n + 1 : ℝ) ^ (-(1 + ε)) * ((n + 1 : ℝ) ^ (ε / 2) / (ε / 2)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogpower
          (Real.rpow_nonneg hn.le _))
      _ = (n + 1 : ℝ) ^ (-(1 + ε)) +
          (ε / 2)⁻¹ * (n + 1 : ℝ) ^ (-(1 + ε / 2)) := by
        rw [← mul_div_assoc, hpower]
        ring

/-- A logarithmic symbol majorant gives absolute summability on the full
conductor-frequency product. The actual signed weights are retained. -/
theorem summable_norm_residue_fourier_conductor_packet
    {α : Type*} (a : α → ℕ) (ha : ∀ x, 0 < a x) (w : α → ℝ)
    (hw : Summable (fun x => |w x| * (1 + Real.log (a x : ℝ))))
    (i : ℕ) (C : ℝ)
    (hS : ∀ x h, ‖dyadicResidueFourierSymbol (a x) h‖ ≤
      C * (1 + Real.log (a x : ℝ)) * (1 + Real.log (2 + |(h : ℝ)|))) :
    Summable (fun p : α × ℤ =>
      ‖(w p.1 : ℂ) * (dyadicTentMellinCoefficient i p.2 *
        dyadicResidueFourierSymbol (a p.1) p.2)‖) := by
  have hlog (x : α) : 0 ≤ Real.log (a x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ a x from ha x))
  have hfreq (h : ℤ) : 0 ≤ Real.log (2 + |(h : ℝ)|) :=
    Real.log_nonneg (by have := abs_nonneg (h : ℝ); linarith)
  have hmajor := (hw.mul_of_nonneg
    (summable_norm_dyadicTentMellinCoefficient_mul_one_add_log i)
    (fun x => mul_nonneg (abs_nonneg _) (by linarith [hlog x]))
    (fun h => mul_nonneg (norm_nonneg _) (by linarith [hfreq h]))).mul_left C
  apply hmajor.of_norm_bounded
  rintro ⟨x, h⟩
  rw [norm_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = (|w x| * ‖dyadicTentMellinCoefficient i h‖) *
        ‖dyadicResidueFourierSymbol (a x) h‖ := by ring
    _ ≤ (|w x| * ‖dyadicTentMellinCoefficient i h‖) *
        (C * (1 + Real.log (a x : ℝ)) * (1 + Real.log (2 + |(h : ℝ)|))) :=
      mul_le_mul_of_nonneg_left (hS x h) (by positivity)
    _ = _ := by ring

/-- Exact infinite signed-conductor Fourier expansion; both summation
orders are justified by absolute summability of the entire product. -/
theorem residue_conductor_packet_hasSum_fourier
    {α : Type*} (a : α → ℕ) (ha : ∀ x, 0 < a x) (w : α → ℝ)
    (hw : Summable (fun x => |w x| * (1 + Real.log (a x : ℝ))))
    (i : ℕ) (C : ℝ)
    (hS : ∀ x h, ‖dyadicResidueFourierSymbol (a x) h‖ ≤
      C * (1 + Real.log (a x : ℝ)) * (1 + Real.log (2 + |(h : ℝ)|))) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑' x, (w x : ℂ) * dyadicResidueFourierSymbol (a x) h)
      (∑' x, (w x : ℂ) *
        (dyadicBoundaryCoordinate (hilbertResidue (a x) (ha x)) i : ℂ)) := by
  let f : α → ℤ → ℂ := fun x h =>
    (w x : ℂ) * (dyadicTentMellinCoefficient i h * dyadicResidueFourierSymbol (a x) h)
  have hf : Summable (Function.uncurry f) :=
    (summable_norm_residue_fourier_conductor_packet a ha w hw i C hS).of_norm
  have hrow : Summable (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑' x, (w x : ℂ) * dyadicResidueFourierSymbol (a x) h) := by
    apply hf.prod_symm.prod.congr
    intro h
    change (∑' x, (w x : ℂ) * (dyadicTentMellinCoefficient i h *
      dyadicResidueFourierSymbol (a x) h)) = _
    rw [← tsum_mul_left]
    apply tsum_congr
    intro x
    ring
  apply hrow.hasSum_iff.mpr
  calc
    _ = ∑' h, ∑' x, f x h := by
      apply tsum_congr
      intro h
      rw [← tsum_mul_left]
      apply tsum_congr
      intro x
      dsimp [f]
      ring
    _ = ∑' x, ∑' h, f x h := hf.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro x
      exact (HasSum.mul_left (w x : ℂ)
        (dyadicBoundaryCoordinate_residue_hasSum_fourier (a x) (ha x) i)).tsum_eq

/-- The actual positive-damping Möbius family has an absolutely convergent
conductor-frequency product, including the zero Fourier mode. -/
theorem summable_norm_dampedMobius_residue_fourier
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    Summable (fun p : ℕ × ℤ =>
      ‖(((ArithmeticFunction.moebius (p.1 + 1) : ℝ) /
          (p.1 + 1 : ℝ) ^ (1 + ε) : ℝ) : ℂ) *
        (dyadicTentMellinCoefficient i p.2 *
          dyadicResidueFourierSymbol (p.1 + 1) p.2)‖) := by
  obtain ⟨C, _, hC⟩ := dyadicResidueFourierSymbol_logarithmic_product_majorant
  exact summable_norm_residue_fourier_conductor_packet
    (fun n => n + 1) (fun n => by positivity)
    (fun n => (ArithmeticFunction.moebius (n + 1) : ℝ) / (n + 1 : ℝ) ^ (1 + ε))
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      summable_abs_dampedMobius_div_mul_one_add_log hε) i C
    (fun n h => hC (n + 1) (by positivity) h)

/-- Exact Fourier interchange through the actual damped Möbius conductor
family, with the signed zero mode and every frequency retained. -/
theorem dampedMobius_residue_hasSum_fourier
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑' n : ℕ, (((ArithmeticFunction.moebius (n + 1) : ℝ) /
          (n + 1 : ℝ) ^ (1 + ε) : ℝ) : ℂ) *
        dyadicResidueFourierSymbol (n + 1) h)
      (∑' n : ℕ, (((ArithmeticFunction.moebius (n + 1) : ℝ) /
          (n + 1 : ℝ) ^ (1 + ε) : ℝ) : ℂ) *
        (dyadicBoundaryCoordinate (hilbertResidue (n + 1) (by positivity)) i : ℂ)) := by
  obtain ⟨C, _, hC⟩ := dyadicResidueFourierSymbol_logarithmic_product_majorant
  exact residue_conductor_packet_hasSum_fourier
    (fun n => n + 1) (fun n => by positivity)
    (fun n => (ArithmeticFunction.moebius (n + 1) : ℝ) / (n + 1 : ℝ) ^ (1 + ε))
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      summable_abs_dampedMobius_div_mul_one_add_log hε) i C
    (fun n h => hC (n + 1) (by positivity) h)

end
end RiemannResearch.RH.Pareto

import RiemannResearch.Analysis.MontgomeryLatticeSinePrimitive
import RiemannResearch.Analysis.LatticeSineHoleTail
import RiemannResearch.Analysis.SineGapTail
import RiemannResearch.Analysis.LatticeTailRescaling

/-!
# Inverse-width rate for the discrete sine pair law

The discrete and continuous sinc-square tails have the same first-order
coefficient. Their difference is integrable at infinity, and the remaining
sawtooth has zero integral on each complete lattice cell. We obtain a
uniform bound for the integrated error and an inverse-width Cesàro rate
for the explicit positive pair law of Lagarias and Rodgers
(*Higher Correlations and the Alternative Hypothesis*, arXiv:1905.12123).
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryLatticeSine
open Set MeasureTheory
open scoped BigOperators

/-- The common inverse-width term cancels between the two positive sinc-square tails. -/
theorem lattice_continuous_hole_tail_difference {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      |(∑' j : ℕ, (a - gapWeight a (j + ⌊q/a⌋₊))) -
        ∫ x in Ioi q, Real.sinc (Real.pi*x)^2| ≤ C/q^2 := by
  have ha1 : a < 1 := by linarith
  have hsin : 0 < Real.sin (Real.pi*a) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by nlinarith only [mul_pos Real.pi_pos (sub_pos.mpr ha1)])
  let coeff : ℝ := 1 / (2*Real.pi^2)
  let A : ℝ := (1 / (2*Real.pi^2*a)) * (1 + 1 / Real.sin (Real.pi*a))
  let B : ℝ := 1 / (2*Real.pi^3)
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨4*a^2*A + 2*coeff*a + B, by positivity, ?_⟩
  intro q hq
  let n := ⌊q/a⌋₊
  have hn : 0 < n := LatticeTailRescaling.one_le_floor_width ha ha' hq
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hq' : 0 < q := zero_lt_one.trans_le hq
  have heq : (∑' j : ℕ, (a - gapWeight a (j + n))) =
      ∑' j : ℕ, a * Real.sinc (Real.pi * (a * ((j:ℝ)+n+1)))^2 := by
    apply tsum_congr
    intro j
    simp only [gapWeight, Nat.cast_add]
    ring
  apply LatticeTailRescaling.abs_sub_le_rescaled ha ha' hq hA hB hcoeff
  · change |(∑' j : ℕ, (a - gapWeight a (j + n))) - coeff / (a * (n : ℝ))| ≤ A / (n : ℝ)^2
    rw [heq]
    have hd := LatticeSineHoleTail.sinc_square_tail_asymptotic ha ha1 hn
    rw [show coeff / (a * (n:ℝ)) = (1/(2*Real.pi^2*a))*(1/(n:ℝ)) by dsimp [coeff]; field_simp [ha.ne', hn'.ne', Real.pi_ne_zero] <;> ring,
      show A / (n:ℝ)^2 = (1/(2*Real.pi^2*a))*((1 + 1/Real.sin (Real.pi*a))/(n:ℝ)^2)
        by dsimp [A]; ring]
    exact hd
  · rw [show coeff/q = 1/(2*Real.pi^2*q) by dsimp [coeff]; field_simp [hq'.ne', Real.pi_ne_zero] <;> ring,
      show B/q^2 = 1/(2*Real.pi^3*q^2) by dsimp [B]; field_simp [hq'.ne', Real.pi_ne_zero] <;> ring]
    exact SineGapTail.sinc_sq_tail_error_le (zero_lt_one.trans_le hq)


/-- The raw discrepancy is the lattice sawtooth up to an error bounded by C(a)/q². -/
theorem gap_discrepancy_sawtooth_error {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      |latticeGapMass a q - MontgomeryPositiveGap.sineGapMass q -
        a*(1/2 - (q/a - (⌊q/a⌋₊ : ℝ)))| ≤ C/q^2 := by
  obtain ⟨C,hC,h⟩ := lattice_continuous_hole_tail_difference ha ha'
  refine ⟨C,hC, fun q hq => ?_⟩
  rw [gap_discrepancy_tail_identity ha (by linarith) (zero_le_one.trans hq)]
  rw [show ∀ x y z : ℝ, x + y - z - x = y - z by intros; ring]
  exact h q hq

/-- For each admissible fixed lattice spacing the Cesàro discrepancy with
the continuous sine pair law is bounded by K(a)/Q for every positive Q. -/
theorem cesaro_error_inverse_width {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℝ, 0 < Q → |integratedError a Q / Q| ≤ K / Q := by
  obtain ⟨C,hC,h⟩ := lattice_continuous_hole_tail_difference ha ha'
  exact cesaro_inverse_width_of_tail_bound ha (by linarith) hC h

/-- The signed difference of the two consecutive width-band averages also
decays inversely with width. Here integratedError is twice the primitive. -/
theorem adjacent_cesaro_error_inverse_width {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℝ, 0 < Q →
      |integratedError a (2*Q) / (2*Q) - integratedError a Q / Q| ≤ K / Q := by
  obtain ⟨K, hK, h⟩ := cesaro_error_inverse_width ha ha'
  refine ⟨3*K/2, by positivity, ?_⟩
  intro Q hQ
  calc
    _ ≤ |integratedError a (2*Q)/(2*Q)| + |integratedError a Q/Q| := abs_sub _ _
    _ ≤ K/(2*Q) + K/Q := add_le_add (h _ (by positivity)) (h Q hQ)
    _ = (3*K/2)/Q := by field_simp [hQ.ne'] <;> ring

/-- info: 'RiemannResearch.Analysis.MontgomeryLatticeSine.cesaro_error_inverse_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cesaro_error_inverse_width

end RiemannResearch.Analysis.MontgomeryLatticeSine

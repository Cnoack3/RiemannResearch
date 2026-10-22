import RiemannResearch.RH.DerivativeSignedCorrection
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# Exact CRT decomposition of the actual derivative correction

Source: user-directed three-route continuation, September 29, 2026.
The divisor intersection is retained as the full lcm term, and every
arithmetic progression includes its complete positive tail.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open ArithmeticCumulative GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

def divisorMass (q : ℕ) : ℝ :=
  ∑' k : ℕ, positiveWeight k * divisorIndicator q k

theorem divisorIndicator_abs_le_one (q k : ℕ) : |divisorIndicator q k| ≤ 1 := by
  unfold divisorIndicator
  split_ifs <;> norm_num

theorem divisorMass_summable (q : ℕ) :
    Summable (fun k : ℕ => positiveWeight k * divisorIndicator q k) :=
  weighted_summable_of_bounded (divisorIndicator_abs_le_one q)

theorem divisorIndicator_mul (d e k : ℕ) :
    divisorIndicator d k * divisorIndicator e k = divisorIndicator (Nat.lcm d e) k := by
  simp only [divisorIndicator, Nat.lcm_dvd_iff]
  split_ifs <;> simp_all

/-- The zero CRT class uses the positive representative q, so the anchored
zero site contributes no spurious mass. -/
theorem divisorMass_eq_progressionWeight (q : ℕ) (hq : 0 < q) :
    divisorMass q = progressionWeight q q := by
  have hp (k : ℕ) : divisorIndicator q (k + q) = divisorIndicator q k := by
    simp only [divisorIndicator, Nat.dvd_add_left (dvd_refl q)]
  have he := periodic_paretoMean q hq (divisorIndicator q)
    (divisorIndicator_abs_le_one q) hp
  change divisorMass q = _ at he
  rw [he]
  let r : Fin q := ⟨q - 1, by omega⟩
  rw [Finset.sum_eq_single r]
  · have hr : r.val + 1 = q := by dsimp [r]; omega
    simp [hr, divisorIndicator]
  · intro s hs hsr
    have hnd : ¬q ∣ s.val + 1 := by
      intro h
      have hle := Nat.le_of_dvd (by omega : 0 < s.val + 1) h
      have hv : s.val = q - 1 := by omega
      apply hsr
      apply Fin.ext
      simpa only [r] using hv
    simp [divisorIndicator, hnd]
  · simp

/-- Four exact signed terms, including the full CRT divisor intersection. -/
theorem derivativeRowKernel_crt (i j : ℕ) :
    derivativeRowKernel i j =
      1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) -
      divisorMass (j + 2) / ((i + 2 : ℕ) : ℝ) -
      divisorMass (i + 2) / ((j + 2 : ℕ) : ℝ) +
      divisorMass (Nat.lcm (i + 2) (j + 2)) := by
  rw [derivativeRowKernel, hilbert_inner_weighted, paretoInner]
  have hs0 := positiveWeight_summable.mul_right
    (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hs1 := (divisorMass_summable (j + 2)).mul_right
    (1 / ((i + 2 : ℕ) : ℝ))
  have hs2 := (divisorMass_summable (i + 2)).mul_right
    (1 / ((j + 2 : ℕ) : ℝ))
  have hs3 := divisorMass_summable (Nat.lcm (i + 2) (j + 2))
  calc
    _ = ∑' k : ℕ,
        (positiveWeight k * (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) -
        (positiveWeight k * divisorIndicator (j + 2) k) *
          (1 / ((i + 2 : ℕ) : ℝ)) -
        (positiveWeight k * divisorIndicator (i + 2) k) *
          (1 / ((j + 2 : ℕ) : ℝ)) +
        positiveWeight k * divisorIndicator (Nat.lcm (i + 2) (j + 2)) k) := by
      apply tsum_congr
      intro k
      by_cases hk : k = 0
      · subst k; simp [positiveWeight]
      · rw [derivativeAtom_sequence_positive i k (Nat.pos_of_ne_zero hk),
          derivativeAtom_sequence_positive j k (Nat.pos_of_ne_zero hk),
          ← divisorIndicator_mul]
        ring
    _ = _ := by
      rw [((hs0.sub hs1).sub hs2).tsum_add hs3,
        (hs0.sub hs1).tsum_sub hs2, hs0.tsum_sub hs1]
      simp only [tsum_mul_right, positiveWeight_tsum, one_mul, divisorMass]
      ring

def correctionReciprocalMoment (n : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j / ((j.val + 2 : ℕ) : ℝ)

def correctionDivisorMoment (n : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j * divisorMass (j.val + 2)

def correctionCRTIntersection (n i : ℕ) : ℝ :=
  ∑ j : Fin n, correctionVector n j * divisorMass (Nat.lcm (i + 2) (j.val + 2))

def correctionCRTRow (n i : ℕ) : ℝ :=
  (1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2)) *
      correctionReciprocalMoment n -
    correctionDivisorMoment n / ((i + 2 : ℕ) : ℝ) +
    correctionCRTIntersection n i

theorem signedCorrectionRow_eq_crt (n i : ℕ) :
    signedCorrectionRow n i = correctionCRTRow n i := by
  change (∑ j : Fin n, correctionVector n j * derivativeRowKernel i j.val) = _
  simp_rw [derivativeRowKernel_crt]
  unfold correctionCRTRow correctionReciprocalMoment correctionDivisorMoment
    correctionCRTIntersection
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual Abel endpoint and every signed kernel difference equal three
complete CRT moments. No growing-family limit exchange occurs. -/
theorem correctionAbel_eq_crt (n i : ℕ) :
    primitive (correctionCoefficient n) n * derivativeRowKernel i n -
      ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) *
        difference (derivativeRowKernel i) k = correctionCRTRow n i := by
  rw [← signedCorrectionRow_eq_abel, signedCorrectionRow_eq_crt]

/-- CONDITIONAL RESEARCH REDUCTION: this retains cofinal smallness of the
combined signed CRT moments, not separate absolute-mass conditions. -/
theorem correctionCRT_cofinal_iff_residual_zero :
    (∀ i : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, |correctionCRTRow n i| < ε) ↔ limitResidual = 0 := by
  simpa only [← signedCorrectionRow_eq_crt] using
    signedCorrectionRow_cofinal_iff_residual_zero

/-- Complete square identity for the same signed CRT row. -/
theorem correctionCRT_row_square (n i : ℕ) :
    (signedCorrectionRow n i)^2 =
      ((1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2)) *
        correctionReciprocalMoment n -
        correctionDivisorMoment n / ((i + 2 : ℕ) : ℝ))^2 +
      2 * ((1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2)) *
        correctionReciprocalMoment n -
        correctionDivisorMoment n / ((i + 2 : ℕ) : ℝ)) *
        correctionCRTIntersection n i +
      (correctionCRTIntersection n i)^2 := by
  rw [signedCorrectionRow_eq_crt]
  unfold correctionCRTRow
  ring

-- Append before namespace end in DerivativeCRT.lean.

/-- The complete signed first difference of a fixed derivative row has a
reciprocal part, a progression-mass difference, and an lcm-mass difference. -/
theorem difference_derivativeRowKernel_crt (i k : ℕ) :
    difference (derivativeRowKernel i) k =
      (1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2)) *
        (1 / ((k + 3 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) -
      (divisorMass (k + 3) - divisorMass (k + 2)) / ((i + 2 : ℕ) : ℝ) +
      divisorMass (Nat.lcm (i + 2) (k + 3)) -
      divisorMass (Nat.lcm (i + 2) (k + 2)) := by
  unfold difference
  rw [derivativeRowKernel_crt, derivativeRowKernel_crt]
  have hk : k + 1 + 2 = k + 3 := by omega
  rw [hk]
  ring

/-- Both the endpoint and every kernel-difference summand are explicitly CRT
arithmetic. No estimate or limit is taken in this identity. -/
theorem correctionAbel_explicit_crt (n i : ℕ) :
    primitive (correctionCoefficient n) n *
      (1 / ((i + 2 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) -
        divisorMass (n + 2) / ((i + 2 : ℕ) : ℝ) -
        divisorMass (i + 2) / ((n + 2 : ℕ) : ℝ) +
        divisorMass (Nat.lcm (i + 2) (n + 2))) -
      ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) *
        ((1 / ((i + 2 : ℕ) : ℝ) - divisorMass (i + 2)) *
          (1 / ((k + 3 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) -
        (divisorMass (k + 3) - divisorMass (k + 2)) / ((i + 2 : ℕ) : ℝ) +
        divisorMass (Nat.lcm (i + 2) (k + 3)) -
        divisorMass (Nat.lcm (i + 2) (k + 2))) =
      correctionCRTRow n i := by
  simpa only [difference_derivativeRowKernel_crt, derivativeRowKernel_crt] using
    correctionAbel_eq_crt n i

-- Append inside the DerivativeCompatibility namespace.

/-- Every prefix used by Abel summation is an exact finite Mobius transform
of the physical derivative residual. All divisor signs remain present. -/
theorem correctionPrimitive_eq_divisor_sum (n K : ℕ) (hK : K ≤ n) :
    primitive (correctionCoefficient n) K =
      ∑ j ∈ Finset.range K, ∑ d ∈ (j + 2).divisors,
        (ArithmeticFunction.moebius ((j + 2) / d) : ℝ) *
          hilbertSequence (derivativeResidual n) d := by
  unfold primitive
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := lt_of_lt_of_le (Finset.mem_range.mp hj) hK
  simp only [correctionCoefficient, dif_pos hjn]
  rw [correctionVector_apply, correction_eq_residual_coordinate n (j + 2) (by omega)]
  simp only [mobiusDifferenceCLM_apply, mobiusDifference, derivativeResidual,
    hilbertDifference_sequence, PrimitiveEnergy.difference, PrimitiveEnergy.backwardShift]

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

import RiemannResearch.RH.DerivativeCRTPowerMoments
import RiemannResearch.RH.GeometricDerivativeMoments

/-!
# CRT evaluation of the finite geometric derivative moments

Source: user-directed three-route continuation, September 29, 2026.
All identities are finite in the moment index. The first physical site
is subtracted exactly from each inverse-power moment.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open GeometricMoments GramMobiusCorrection

/-- Every finite geometric coefficient is an exact CRT/zeta moment, with its
complete first-site correction retained. -/
theorem geometricMoment_derivativeAtoms (p i j : ℕ) :
    geometricMoment p (derivativeAtom i) (derivativeAtom j) =
      derivativePowerKernel (p + 2) i j -
        1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) := by
  rw [geometricMoment_eq_tsum]
  let F : ℕ → ℝ := fun k => hilbertSequence (derivativeAtom i) k *
    hilbertSequence (derivativeAtom j) k / (k : ℝ)^(p + 2)
  have he : (∑' k : ℕ, if 2 ≤ k then F k else 0) = ∑' k : ℕ, F (k + 2) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun a : Function.support (fun k : ℕ => F (k + 2)) => a.val + 2)
    · intro a b hab
      exact Subtype.ext (Nat.add_right_cancel hab)
    · intro k hk
      have hk2 : 2 ≤ k := by
        by_contra hh
        simpa only [Function.mem_support, if_neg hh, ne_eq, not_true_eq_false] using hk
      refine ⟨⟨k - 2, ?_⟩, Nat.sub_add_cancel hk2⟩
      simpa only [Function.mem_support, Nat.sub_add_cancel hk2, if_pos hk2] using hk
    · intro a
      exact if_pos (by omega)
  change (∑' k : ℕ, if 2 ≤ k then F k else 0) = _
  rw [he]
  exact derivativePowerKernel_tail (p + 2) i j (by omega)

/-- The two-source entry at each finite moment index retains all four CRT terms. -/
theorem geometricMoment_derivativeAtoms_crt (p i j : ℕ) :
    geometricMoment p (derivativeAtom i) (derivativeAtom j) =
      inversePowerSeries (p + 2) *
        (1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) -
          1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)^(p + 2) -
          1 / ((j + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ)^(p + 2) +
          1 / (Nat.lcm (i + 2) (j + 2) : ℝ)^(p + 2)) -
        1 / ((i + 2 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ) := by
  rw [geometricMoment_derivativeAtoms, derivativePowerKernel_crt _ _ _ (by omega)]

/-- Exact finite synthesis transports the pairwise moment identity to the
actual inverse-Gram correction coefficients. -/
theorem geometricMoment_correction (p n i : ℕ) :
    geometricMoment p (derivativeAtom i) (hilbertDifference (correctionSynthesis n)) =
      correctionPowerMoment (p + 2) n i -
        correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ) := by
  rw [derivative_correction_synthesis, geometricMoment_linearCombination]
  simp only [derivativeFamily]
  simp_rw [geometricMoment_derivativeAtoms]
  unfold correctionPowerMoment correctionReciprocalMoment
  simp only [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem correctionSynthesis_firstSite (n : ℕ) :
    hilbertSequence (hilbertDifference (correctionSynthesis n)) 1 =
      correctionReciprocalMoment n := by
  have h : inner ℝ (hilbertAtom 1 (by decide))
      (hilbertDifference (correctionSynthesis n)) = correctionReciprocalMoment n / 2 := by
    rw [derivative_correction_synthesis, Fintype.linearCombination_apply, inner_sum]
    simp only [real_inner_smul_right, derivativeFamily]
    unfold correctionReciprocalMoment
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm, derivativeAtom_inner_target]
    ring
  rw [hilbertAtom_inner] at h
  have hw : positiveWeight 1 = (1 / 2 : ℝ) := by norm_num [positiveWeight]
  rw [hw] at h
  linarith

/-- All entries of this finite core are explicit signed CRT/zeta moments.
In particular the k=1 boundary is A/(2d) and is never discarded. -/
def correctionZetaCRTCore (M n i : ℕ) : ℝ :=
  correctionReciprocalMoment n / (2 * ((i + 2 : ℕ) : ℝ)) +
    ∑ p ∈ Finset.range M, (-1 : ℝ)^p *
      (inversePowerSeries (p + 2) *
        (correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ) -
          correctionInversePowerMoment (p + 2) n / ((i + 2 : ℕ) : ℝ) -
          correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ)^(p + 2) +
          correctionLCMPowerMoment (p + 2) n i) -
        correctionReciprocalMoment n / ((i + 2 : ℕ) : ℝ))

theorem correctionMomentCore_eq_zetaCRT (M n i : ℕ) :
    correctionMomentCore M n i = correctionZetaCRTCore M n i := by
  unfold correctionMomentCore correctionZetaCRTCore
  rw [correctionSynthesis_firstSite, derivativeAtom_sequence_positive i 1 (by decide)]
  have hdi : ¬ (i + 2) ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  simp only [ArithmeticCumulative.divisorIndicator, if_neg hdi, sub_zero]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro p hp
    rw [geometricMoment_correction, correctionPowerMoment_crt _ _ _ (by omega)]

/-- Exact Abel-compatible CRT/zeta expansion with the complete signed
physical remainder. Both cutoffs remain finite throughout the proof. -/
theorem signedCorrectionRow_eq_zetaCRT (M n i : ℕ) :
    signedCorrectionRow n i = correctionZetaCRTCore M n i +
      (-1 : ℝ)^M * signedRemainder M (derivativeAtom i)
        (hilbertDifference (correctionSynthesis n)) := by
  rw [signedCorrectionRow_eq_momentCore M n i, correctionMomentCore_eq_zetaCRT]

/-- Dimension-independent error bound on the complete signed expression. -/
theorem signedCorrectionRow_zetaCRT_bound (M n i : ℕ) :
    |signedCorrectionRow n i - correctionZetaCRTCore M n i| ≤
      (1 / 2 : ℝ)^M * (‖derivativeAtom i‖ *
        ‖hilbertDifference (correctionSynthesis n)‖) := by
  rw [← correctionMomentCore_eq_zetaCRT]
  exact signedCorrectionRow_momentCore_bound M n i

/-- The square of the Abel expression retains the signed mixed term and
the complete squared remainder. -/
theorem signedCorrectionRow_zetaCRT_square (M n i : ℕ) :
    (signedCorrectionRow n i)^2 = (correctionZetaCRTCore M n i)^2 +
      2 * correctionZetaCRTCore M n i * ((-1 : ℝ)^M *
        signedRemainder M (derivativeAtom i) (hilbertDifference (correctionSynthesis n))) +
      ((-1 : ℝ)^M * signedRemainder M (derivativeAtom i)
        (hilbertDifference (correctionSynthesis n)))^2 := by
  rw [signedCorrectionRow_eq_zetaCRT M n i]
  ring


open Filter
open scoped Topology

/-- Growing moment order is justified by the uniform geometric bound, not by
an exchange of coordinatewise limits with a growing coefficient sum. -/
theorem correctionZetaCRT_diagonal_error_tendsto_zero (i : ℕ) :
    Tendsto (fun n => signedCorrectionRow n i - correctionZetaCRTCore n n i)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := correction_derivative_uniform_norm_bound
  apply squeeze_zero_norm (fun n => (signedCorrectionRow_zetaCRT_bound n n i).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _)) (by positivity)))
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
      (‖derivativeAtom i‖ * C)

/-- An explicit finite zeta/CRT arithmetic criterion equivalent to the
original cofinal signed Abel criterion. No cancellation provider is supplied. -/
theorem correctionZetaCRT_cofinal_iff_residual_zero :
    (∀ i : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, |correctionZetaCRTCore n n i| < ε) ↔ limitResidual = 0 := by
  rw [← signedCorrectionRow_cofinal_iff_residual_zero]
  constructor
  · intro h i ε hε
    have he : ∀ᶠ n : ℕ in atTop,
        |signedCorrectionRow n i - correctionZetaCRTCore n n i| < ε / 2 :=
      ((correctionZetaCRT_diagonal_error_tendsto_zero i).abs).eventually_lt_const
        (by simpa only [abs_zero] using (half_pos hε))
    apply ((h i (ε / 2) (half_pos hε)).and_eventually he).mono
    intro n hn
    rcases abs_lt.mp hn.1 with ⟨h1, h2⟩
    rcases abs_lt.mp hn.2 with ⟨h3, h4⟩
    apply abs_lt.mpr
    constructor <;> linarith
  · intro h i ε hε
    have he : ∀ᶠ n : ℕ in atTop,
        |signedCorrectionRow n i - correctionZetaCRTCore n n i| < ε / 2 :=
      ((correctionZetaCRT_diagonal_error_tendsto_zero i).abs).eventually_lt_const
        (by simpa only [abs_zero] using (half_pos hε))
    apply ((h i (ε / 2) (half_pos hε)).and_eventually he).mono
    intro n hn
    rcases abs_lt.mp hn.1 with ⟨h1, h2⟩
    rcases abs_lt.mp hn.2 with ⟨h3, h4⟩
    apply abs_lt.mpr
    constructor <;> linarith

theorem riemannHypothesis_of_cofinal_zetaCRT
    (h : ∀ i : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, |correctionZetaCRTCore n n i| < ε) : RiemannHypothesis :=
  riemannHypothesis_of_fixedMismatch_limits
    (fixedMismatch_limits_iff_residual_zero.mpr
      (correctionZetaCRT_cofinal_iff_residual_zero.mp h))

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

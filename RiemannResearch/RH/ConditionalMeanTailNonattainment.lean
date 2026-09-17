import RiemannResearch.RH.ConditionalMeanHeadMinimum
import RiemannResearch.RH.ParetoLegalStructure
import RiemannResearch.RH.FiniteResidueIndependence

/-!
# Actual arithmetic Cesàro tails and strict head-mass nonattainment

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Sections 10.3 and 11; the complete ordinary proof is recorded in
`ArithmeticVariationalProof.md`. Actual legal periodicity and exact Cesàro
inversion prove tail injectivity. No finite-support assumption, arithmetic
energy estimate, or RH/Nyman--Beurling converse is supplied as a premise.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

/-- Real positive-index Cesàro inversion, including the zero-endpoint convention. -/
theorem cesaro_recover (f : ℕ → ℝ) (n : ℕ) :
    f (n + 1) = ((n + 1 : ℕ) : ℝ) * cesaro f (n + 1) - (n : ℝ) * cesaro f n := by
  have h := Analysis.Cesaro.recover (fun k => (f k : ℂ)) n
  simp only [Analysis.Cesaro.mean_ofReal] at h
  exact_mod_cast h

end RiemannResearch.Probability.ConditionalIID

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- A genuine legal witness is determined by its entire tail of conditional means. -/
theorem legalSeedSpan_eq_zero_of_cesaro_tail (A : Set ℕ)
    (hA : ∀ a ∈ A, 0 < a) {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A)
    (N : ℕ) (htail : ∀ t, N < t → cesaro f t = 0) : f = 0 := by
  have hsucc (n : ℕ) (hn : N < n) : f (n + 1) = 0 := by
    rw [cesaro_recover f n, htail (n + 1) (by omega), htail n hn]
    ring
  obtain ⟨d, hd, hperiod⟩ := legalSeedSpan_hasLegalReflectionPeriod A hA hf
  have hQ : N + 1 ≤ d * (N + 1) := Nat.le_mul_of_pos_left (N + 1) hd
  have hp : ∀ n, f (n + d * (N + 1)) = f n :=
    (hperiod (d * (N + 1)) (dvd_mul_right d (N + 1))).1
  funext n
  cases n with
  | zero => exact legalSeedSpan_zero_value A hf
  | succ n =>
    have hz := hsucc (n + d * (N + 1)) (by omega)
    have he : n + d * (N + 1) + 1 = n + 1 + d * (N + 1) := by omega
    rw [he, hp] at hz
    exact hz

/-- The actual conditional-mean energy lying strictly beyond a finite head. -/
def conditionalMeanTailSquare (N : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, conditionalWeight (k + N) * (cesaro f (k + N + 1)) ^ 2

theorem conditionalMeanTailSquare_nonneg (N : ℕ) (f : ℕ → ℝ) :
    0 ≤ conditionalMeanTailSquare N f :=
  tsum_nonneg (fun k => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))

/-- Every nonzero legal witness has strictly positive energy on every tail. -/
theorem conditionalMeanTailSquare_pos (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ℕ → ℝ} (hf : f ∈ legalSeedSpan A) (hf0 : f ≠ 0) (N : ℕ) :
    0 < conditionalMeanTailSquare N f := by
  have hs : Summable (fun k : ℕ =>
      conditionalWeight (k + N) * (cesaro f (k + N + 1)) ^ 2) :=
    (legal_conditionalMeanSquare_summable A hA hf).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  by_contra hpos
  have hle : conditionalMeanTailSquare N f ≤ 0 := le_of_not_gt hpos
  have hzero (k : ℕ) : cesaro f (k + N + 1) = 0 := by
    have hc := hs.sum_le_tsum ({k} : Finset ℕ)
      (fun j _ => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))
    simp only [Finset.sum_singleton] at hc
    change conditionalWeight (k + N) * (cesaro f (k + N + 1)) ^ 2 ≤
      conditionalMeanTailSquare N f at hc
    by_contra hne
    have hp := mul_pos (conditionalWeight_pos (k + N)) (sq_pos_of_ne_zero hne)
    linarith
  apply hf0
  apply legalSeedSpan_eq_zero_of_cesaro_tail A hA hf N
  intro t ht
  have he : t - (N + 1) + N + 1 = t := by omega
  simpa only [he] using hzero (t - (N + 1))

/-- No actual finite legal exact head attains its compulsory head mass. -/
theorem conditionalMeanSquare_gt_head_mass (N : ℕ) (hN : 0 < N)
    {f : ℕ → ℝ} (hf : f ∈ conditionalHeadClass N) :
    (N : ℝ) / ((N : ℝ) + 2) < conditionalMeanSquare f := by
  have hf0 : f ≠ 0 := by
    intro hz
    have h := hf.2 1 (by omega) hN
    rw [hz] at h
    norm_num at h
  have hp := conditionalMeanTailSquare_pos (Set.Ici 1) (by intro a ha; exact ha)
    hf.1 hf0 N
  rw [conditionalMeanSquare_exact_head_split N hf]
  exact lt_add_of_pos_right _ hp

/-- An infimum can equal head mass, but that number is never an attained legal energy. -/
theorem head_mass_not_mem_conditionalHeadEnergies (N : ℕ) (hN : 0 < N) :
    (N : ℝ) / ((N : ℝ) + 2) ∉ conditionalHeadEnergies N := by
  rintro ⟨f, hf, he⟩
  have h := conditionalMeanSquare_gt_head_mass N hN hf
  rw [he] at h
  exact lt_irrefl _ h

/-- A finite residue combination is genuinely legal with all positive seeds. -/
theorem finite_residueCombination_mem_full_legal (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    (fun n => ∑ d ∈ s, c d * residue d n) ∈ legalSeedSpan (Set.Ici 1) := by
  have he : (fun n => ∑ d ∈ s, c d * residue d n) = ∑ d ∈ s, c d • residue d := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  apply (legalSeedSpan _).sum_mem
  intro d hd
  apply (legalSeedSpan _).smul_mem
  simpa only [dilation_one] using
    (dilation_generator_mem (Set.Ici 1) (a := d) (m := 1)
      (show d ∈ Set.Ici 1 from hs d hd) (by omega))

/-- The tail of the actual smoothed residue dictionary is independent:
an identically zero tail forces all finite coefficients to vanish. -/
theorem finite_residue_coefficients_zero_of_cesaro_tail (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (N : ℕ)
    (htail : ∀ t, N < t → cesaro (fun n => ∑ d ∈ s, c d * residue d n) t = 0) :
    ∀ d ∈ s, c d = 0 := by
  have hlegal := finite_residueCombination_mem_full_legal s c (by
    intro d hd
    have := hs d hd
    omega)
  have he := legalSeedSpan_eq_zero_of_cesaro_tail (Set.Ici 1)
    (by intro a ha; exact ha) hlegal N htail
  apply finite_residue_coefficients_zero s c hs
  intro n
  exact congrFun he n

/-- Positive definiteness of the actual finite tail energy, with the original
signed residue coefficients and without a supplied matrix positivity premise. -/
theorem finite_residue_tail_energy_pos (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (hc : ∃ d ∈ s, c d ≠ 0) (N : ℕ) :
    0 < conditionalMeanTailSquare N (fun n => ∑ d ∈ s, c d * residue d n) := by
  have hlegal := finite_residueCombination_mem_full_legal s c (by
    intro d hd
    have := hs d hd
    omega)
  apply conditionalMeanTailSquare_pos (Set.Ici 1) (by intro a ha; exact ha) hlegal
  intro he
  obtain ⟨d, hd, hcd⟩ := hc
  apply hcd
  apply finite_residue_coefficients_zero s c hs (fun n => congrFun he n) d hd

end RiemannResearch.RH.Pareto

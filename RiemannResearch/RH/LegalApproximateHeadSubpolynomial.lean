import RiemannResearch.RH.LegalExactHeadSubpolynomial
import RiemannResearch.RH.ParetoCompactHead

/-!
# Approximate physical heads and cofinal subpolynomial energy imply RH

Source: user-provided Green-Pareto-Schur continuation, Sections 23 and 28,
supporting the localized Mellin obstruction strategy.

This strictly relaxes the exact expanding-head premise in
`LegalExactHeadSubpolynomial`: the genuine orthogonal physical head of the
residual need only converge to zero in norm. The energy certificate still
controls the full infinite Pareto norm. The actual zeta-zero Mellin detector
is proved from the existing legal-closure theorem.

No arithmetic approximate-head family or subpolynomial provider is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.SubpolynomialWindow

/-- An actual legal residual with a sufficiently small physical head obeys
an off-line-zero power lower bound for its complete infinite energy.
The head condition is a norm condition; exact interpolation is unnecessary. -/
theorem legal_approximate_head_residual_power_lower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    (n : ℕ) (hn : 1 ≤ n)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0)
    (hsmall : Real.sqrt (1 / (2 * s.re - 1)) *
      ‖compactHead (n - 1) (hilbertOne - f)‖ ≤ 1 / (2 * ‖s‖)) :
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      (n : ℝ) ^ (2 * s.re - 1) ≤ ‖hilbertOne - f‖ ^ 2 := by
  let e := hilbertOne - f
  let h := compactHead (n - 1) e
  let t := e - h
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ) ^ (2 * s.re - 1) :=
    Real.rpow_pos_of_pos hnreal _
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin e s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have htval : paretoMellin t s = 1 / s - paretoMellin h s := by
    change paretoMellinContinuous s hs (e - h) = _
    rw [map_sub]
    change paretoMellin e s - paretoMellin h s = _
    rw [heval]
  have hhsmall : ‖paretoMellin h s‖ ≤ 1 / (2 * ‖s‖) :=
    (paretoMellin_norm_le h s hs).trans hsmall
  have htlow : 1 / (2 * ‖s‖) ≤ ‖paretoMellin t s‖ := by
    have hrev := norm_sub_norm_le (1 / s) (paretoMellin h s)
    rw [← htval, norm_div, norm_one] at hrev
    have htwice : 1 / ‖s‖ = 2 * (1 / (2 * ‖s‖)) := by ring
    rw [htwice] at hrev
    linarith
  have hthead : ∀ k, 0 < k → k < n → hilbertSequence t k = 0 := by
    intro k hk hkn
    change hilbertSequenceLinear (e - compactHead (n - 1) e) k = 0
    rw [map_sub]
    change hilbertSequence e k - hilbertSequence (compactHead (n - 1) e) k = 0
    rw [compactHead_sequence, if_pos (by omega)]
    exact sub_self _
  have hlocalized := mellin_zero_head_lower t n hn hthead s hs
  have hsq : (1 / (2 * ‖s‖)) ^ 2 ≤ ‖paretoMellin t s‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr htlow
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq hd.le) hp.le
  have hpy := compactHead_pythagoras (n - 1) e
  change ‖e‖ ^ 2 = ‖h‖ ^ 2 + ‖t‖ ^ 2 at hpy
  have htail : ‖t‖ ^ 2 ≤ ‖e‖ ^ 2 := by nlinarith [sq_nonneg ‖h‖]
  have hfinal := (hmul.trans hlocalized).trans htail
  have hcoef : (2 * s.re - 1) * (1 / (2 * ‖s‖)) ^ 2 =
      (2 * s.re - 1) / (4 * ‖s‖ ^ 2) := by
    field_simp
    ring
  rw [hcoef] at hfinal
  exact hfinal

/-- Cofinal legal trials whose physical residual heads tend to zero, and
whose complete residual-energy certificates have vanishing relative log
growth, imply the actual Riemann hypothesis. The expanding physical cutoff
may be chosen independently of the trial's conductor support. -/
theorem riemannHypothesis_of_cofinal_legal_approximate_head_subpolynomial
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hhead : Tendsto
      (fun i => ‖compactHead (n i - 1) (hilbertOne - f i)‖)
      atTop (𝓝 0))
    (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ‖hilbertOne - f i‖ ^ 2 ≤ C i + 1)
    (hsub : Tendsto (fun i => Real.log (1 + C i) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc : 0 < (2 * s.re - 1) / (4 * ‖s‖ ^ 2) :=
    div_pos (by linarith) (mul_pos (by norm_num) (pow_pos hspos 2))
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hscaled : Tendsto
      (fun i => Real.sqrt (1 / (2 * s.re - 1)) *
        ‖compactHead (n i - 1) (hilbertOne - f i)‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      hhead.const_mul (Real.sqrt (1 / (2 * s.re - 1)))
  have hsmall : ∀ᶠ i : ℕ in atTop,
      Real.sqrt (1 / (2 * s.re - 1)) *
        ‖compactHead (n i - 1) (hilbertOne - f i)‖ < 1 / (2 * ‖s‖) :=
    hscaled.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * ‖s‖)))
  have hfloor : ∀ᶠ i : ℕ in atTop,
      ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
        (n i : ℝ) ^ (2 * s.re - 1) ≤ C i + 1 := by
    filter_upwards [hn1, hsmall] with i hi hsi
    have hiNat : 1 ≤ n i := by exact_mod_cast hi
    exact (legal_approximate_head_residual_power_lower A hA (hf i)
      (n i) hiNat s hs hs1 hz hsi.le).trans (hbound i)
  exact no_positive_power_floor (fun i => (n i : ℝ)) C 1
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) (2 * s.re - 1)
    hn hC (by norm_num) hc ha hsub hfloor

end RiemannResearch.RH.Pareto

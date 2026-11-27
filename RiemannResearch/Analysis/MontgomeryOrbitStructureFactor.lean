import RiemannResearch.Analysis.MontgomeryOrdinateResidual
import RiemannResearch.Analysis.RationalLandauInghamTangent
import RiemannResearch.Probability.DPPContinuousSpectralRigidity

/-!
# Prime-orbit reconstruction and the lower slope of the regular spectrum

Source: the Compact Orbit A24 and M32 research question. The Ingham tangent
controls the error of horizontal reconstruction for a finite weighted test.
At each small unfolded frequency, the height limit is taken first. The
identification with the centered physical statistic and the arithmetic upper
estimate enter separately. The last section gives the corresponding signed
correction for the Cauchy-weighted ordinary form factor.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open RiemannResearch.DPPSpectral

/-- A finite real combination of prime-orbit characters and its Taylor parameters. -/
structure PrimeOrbitBandTest (ι : Type*) where
  support : Finset ι
  coeff : ι → ℝ
  primes : ι → Finset ℕ
  exponent : ι → ℕ → ℤ
  order : ℕ
  precision : ℕ

namespace PrimeOrbitBandTest
variable {ι : Type*}

def frequency (b : PrimeOrbitBandTest ι) (i : ι) : ℝ :=
  PrimePhaseTorus.primeFrequency (b.primes i) (b.exponent i)

def coeffMass (b : PrimeOrbitBandTest ι) : ℝ := ∑ i ∈ b.support, |b.coeff i|

/-- The hypotheses of the finite Ingham reconstruction at height `T`. -/
def inBand (b : PrimeOrbitBandTest ι) (T : ℝ) : Prop :=
  (∀ i ∈ b.support, |b.frequency i| ≤ (4 / 3) * Real.log T) ∧
  2 * Real.log T ≤ (b.precision : ℝ) * Real.log (Real.log T) ∧
  ((b.precision : ℝ) + 4) * (1 + (4 / 3) * Real.sqrt (Real.log T)) * Real.log (Real.log T)
    ≤ 2 * ((b.order : ℝ) + 1)

/-- The test of all ordered zero occurrences, with equal ordinates included. -/
def ordinateTest (b : PrimeOrbitBandTest ι) (T : ℝ) : ℝ :=
  ∑ i ∈ b.support, b.coeff i *
    ((∑ p : Copies T, ∑ q : Copies T,
      Real.cos ((copyOrdinate T p - copyOrdinate T q) * b.frequency i)) /
      (Zeta23.Ncount 0 T : ℝ))

/-- The same test of the squared reconstructed amplitudes. -/
def reconstructedTest (b : PrimeOrbitBandTest ι) (T : ℝ) : ℝ :=
  ∑ i ∈ b.support, b.coeff i *
    (‖reconstructedOrdinateSum T (b.frequency i) b.order‖ ^ 2 / (Zeta23.Ncount 0 T : ℝ))

/-- Quantitative reconstruction makes the difference vanish when the sum of
absolute coefficients is little-o of height. Both tests use the original normalization. -/
theorem tendsto_ordinate_sub_reconstructed {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (b : ℕ → PrimeOrbitBandTest ι) (hband : ∀ᶠ n in atTop, (b n).inBand (T n))
    (hcost : Tendsto (fun n => (b n).coeffMass / T n) atTop (𝓝 0)) :
    Tendsto (fun n => (b n).ordinateTest (T n) - (b n).reconstructedTest (T n)) atTop (𝓝 0) := by
  classical
  obtain ⟨C, _, hbound⟩ := eventually_weighted_primeOrbit_gap_count_precision (ι := ι)
  apply squeeze_zero_norm' _ (by simpa using hcost.mul_const C)
  filter_upwards [hT.eventually hbound, hband] with n hn hbn
  obtain ⟨hfreq, hk, hJ⟩ := hbn
  have hv := hn (b n).support (b n).coeff (b n).primes (b n).exponent
    (b n).order (b n).precision hfreq hk hJ
  rw [Real.norm_eq_abs, ordinateTest, reconstructedTest, ← Finset.sum_sub_distrib]
  calc
    _ ≤ (b n).coeffMass * (C / T n) := by
      simpa only [frequency, coeffMass, sub_div, mul_sub] using hv
    _ = _ := by ring

/-- Height tends to infinity first at each fixed unfolded probe. Arbitrary common
centerings are allowed; the identification of the centered all-occurrence test
with the regular spectrum of the same physical limit is an explicit hypothesis.
Only an eventual one-sided upper estimate on the reconstructed tests is needed. -/
theorem liminf_le_of_centered_reconstruction {T h : ℕ → ℝ} {S : ℝ → ℝ} {c : ℝ}
    (hT : Tendsto T atTop atTop) (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0))
    (b : ℕ → ℕ → PrimeOrbitBandTest ι) (center : ℕ → ℕ → ℝ)
    (hband : ∀ j, ∀ᶠ n in atTop, (b j n).inBand (T n))
    (hcost : ∀ j, Tendsto (fun n => (b j n).coeffMass / T n) atTop (𝓝 0))
    (hphysical : ∀ j, Tendsto (fun n => (b j n).ordinateTest (T n) - center j n)
      atTop (𝓝 (S (h j))))
    (hupper : ∀ᶠ j in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (b j n).reconstructedTest (T n) - center j n ≤ c * h j + ε) :
    liminf (fun x => ENNReal.ofReal (S x / x)) (𝓝[>] 0) ≤ ENNReal.ofReal c := by
  apply rightSlope_liminf_le_of_steps hp hz
  filter_upwards [hupper] with j hj
  have hdiff := tendsto_ordinate_sub_reconstructed hT (b j) (hband j) (hcost j)
  have hrec : Tendsto (fun n => (b j n).reconstructedTest (T n) - center j n)
      atTop (𝓝 (S (h j))) := by
    have hh := (hphysical j).sub hdiff
    rw [sub_zero] at hh
    apply hh.congr'
    filter_upwards with n
    ring
  by_contra! hbad
  have he : 0 < (S (h j) - c * h j) / 2 := by linarith
  have := le_of_tendsto hrec (hj _ he)
  linarith

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.PrimeOrbitBandTest.liminf_le_of_centered_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms liminf_le_of_centered_reconstruction

end PrimeOrbitBandTest
end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.MontgomeryOrdinateResidual
open MontgomeryFormFactor RiemannResearch.DPPSpectral

/-- Along one cofinal sequence of small positive frequencies, a one-sided signed
correction of relative size strictly below one suffices for spectral rigidity.
The form-factor identification and the signed limits concern the same heights. -/
theorem interval_of_signedArithmeticCorrection_steps {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hm : (∫ t, f t) = 1)
    {T h r : ℕ → ℝ} {c : ℝ} (hT : Tendsto T atTop atTop)
    (hp : ∀ j, 0 < h j) (hz : Tendsto h atTop (𝓝 0)) (hc : c < 1)
    (hF : ∀ j, Tendsto (fun n => formFactor (T n) (h j)) atTop (𝓝 (structureFactor f (h j))))
    (hR : ∀ j, Tendsto (fun n => signedArithmeticCorrection (T n) (h j)) atTop (𝓝 (r j)))
    (hr : ∀ᶠ j in atTop, r j ≤ c * h j) :
    ∃ a : ℝ, f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ) := by
  apply interval_spectrum_of_small_slope hf hb hm hp hz (c := 1 + c) (by linarith)
  filter_upwards [hr] with j hj
  have he := tendsto_nhds_unique (signedArithmeticCorrection_tendsto_of_formFactor
    (hp j) hT (hF j)) (hR j)
  rw [add_mul, one_mul]
  linarith only [he, hj]

/-- At an identified positive frequency, a rigid spectrum fixes the full signed
correction. In particular the required correction at `4/3` is negative. -/
theorem signedArithmeticCorrection_tendsto_of_interval {f : ℝ → ℝ} {a h : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ))
    (hh : 0 < h) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hF : Tendsto (fun n => formFactor (T n) h) atTop (𝓝 (structureFactor f h))) :
    Tendsto (fun n => signedArithmeticCorrection (T n) h) atTop (𝓝 (min h 1 - h)) := by
  simpa only [structureFactor_of_interval_ae hf, abs_of_pos hh] using
    signedArithmeticCorrection_tendsto_of_formFactor hh hT hF

/-- A literal rising ramp above one is incompatible with an identified
nonnegative convolution spectrum, even without a slope assumption. -/
theorem formFactor_not_tendsto_ramp_above_one {T : ℕ → ℝ} {f : ℝ → ℝ} {h : ℝ}
    (hf : ∀ᵐ t, 0 ≤ f t) (hh : 1 < h)
    (hF : Tendsto (fun n => formFactor (T n) h) atTop (𝓝 (structureFactor f h))) :
    ¬ Tendsto (fun n => formFactor (T n) h) atTop (𝓝 h) := by
  intro hramp
  have he := tendsto_nhds_unique hF hramp
  exact (not_le_of_gt hh) (he ▸ structureFactor_le_one hf h)

/-- At the Ingham endpoint the plateau forces an exact residual of minus one third. -/
theorem signedArithmeticCorrection_four_thirds {f : ℝ → ℝ} {a : ℝ}
    (hf : f =ᵐ[volume] (Ioo a (a + 1)).indicator (1 : ℝ → ℝ))
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hF : Tendsto (fun n => formFactor (T n) (4 / 3)) atTop (𝓝 (structureFactor f (4 / 3)))) :
    Tendsto (fun n => signedArithmeticCorrection (T n) (4 / 3)) atTop (𝓝 (-(1 / 3))) := by
  have hh := signedArithmeticCorrection_tendsto_of_interval hf (by norm_num : (0 : ℝ) < 4 / 3) hT hF
  norm_num at hh ⊢
  exact hh

/--
info: 'RiemannResearch.Analysis.MontgomeryOrdinateResidual.interval_of_signedArithmeticCorrection_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms interval_of_signedArithmeticCorrection_steps

/--
info: 'RiemannResearch.Analysis.MontgomeryOrdinateResidual.signedArithmeticCorrection_four_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms signedArithmeticCorrection_four_thirds

end RiemannResearch.Analysis.MontgomeryOrdinateResidual

import RiemannResearch.Probability.DPPIntervalSpectrum
import RiemannResearch.Probability.DPPSpectralMultiplier
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Structure-factor rigidity by translations and conservation of mass

Subadditivity propagates a subsequential small-frequency slope to a bound at
every frequency. For a unit-mass covariogram the resulting triangular lower
bound exhausts the integral. This argument avoids a choice of BV representative.
-/

noncomputable section

open Filter MeasureTheory Real
open scoped Topology Convolution FourierTransform
namespace RiemannResearch.DPPSpectral

/-- A continuous subadditive function on the positive half-line is controlled
everywhere by a subsequential upper bound on its quotient at zero. -/
theorem subadditive_le_of_small_steps {S : ℝ → ℝ}
    (hS : Continuous S) (hzero : S 0 = 0) (hadd : ∀ x y, S (x+y) ≤ S x + S y)
    {d c : ℕ → ℝ} {L : ℝ} (hpos : ∀ j, 0 < d j) (hd : Tendsto d atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 L)) (hstep : ∀ j, S (d j) ≤ c j * d j)
    {x : ℝ} (hx : 0 ≤ x) : S x ≤ L * x := by
  have iter (t : ℝ) (m : ℕ) : S (m * t) ≤ m * S t := by
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      simp only [Nat.cast_succ, add_mul, one_mul]
      exact (hadd _ _).trans (add_le_add ih le_rfl)
  let m : ℕ → ℕ := fun j => ⌊x / d j⌋₊
  let z : ℕ → ℝ := fun j => (m j : ℝ) * d j
  have up (j : ℕ) : z j ≤ x :=
    (le_div_iff₀ (hpos j)).mp (Nat.floor_le (div_nonneg hx (hpos j).le))
  have lo (j : ℕ) : x - d j ≤ z j := by
    have ht := (div_lt_iff₀ (hpos j)).mp (Nat.lt_floor_add_one (x / d j))
    change x - d j ≤ (⌊x / d j⌋₊ : ℝ) * d j
    rw [add_mul, one_mul] at ht
    linarith
  have hz : Tendsto z atTop (𝓝 x) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using (tendsto_const_nhds (x := x)).sub hd) tendsto_const_nhds lo up
  apply le_of_tendsto_of_tendsto' (hS.continuousAt.tendsto.comp hz) (hc.mul hz)
  intro j
  calc
    S (z j) ≤ (m j : ℝ) * S (d j) := iter _ _
    _ ≤ (m j : ℝ) * (c j * d j) := mul_le_mul_of_nonneg_left (hstep j) (Nat.cast_nonneg _)
    _ = c j * z j := by dsimp [z]; ring

/-- The integral of the autocorrelation is the square of the mass. -/
theorem integrable_overlap_integral {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun h : ℝ => ∫ x, f x * f (x+h)) ∧
    (∫ h : ℝ, ∫ x, f x * f (x+h)) = (∫ x, f x)^2 := by
  have heq := funext (overlap_as_convolution f)
  rw [← heq]
  refine ⟨hf.comp_neg.integrable_convolution _ hf, ?_⟩
  rw [integral_convolution _ hf.comp_neg hf, integral_neg_eq_self, pow_two]
  rfl

/-- Covariograms of real square-integrable functions are continuous. -/
theorem continuous_overlap {f : ℝ → ℝ} (hf : MemLp f 2) :
    Continuous (fun h : ℝ => ∫ x, f x * f (x+h)) := by
  let tr : C(ℝ, C(ℝ, ℝ)) := (⟨fun z : ℝ × ℝ => z.2 + z.1,
    continuous_snd.add continuous_fst⟩ : C(ℝ × ℝ, ℝ)).curry
  have hp (h : ℝ) : MeasurePreserving (tr h) volume volume :=
    measurePreserving_add_right volume h
  let F := hf.toLp f
  have ht := (continuous_const (y := F)).compMeasurePreservingLp tr.continuous hp
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  have heq (h : ℝ) : inner ℝ F (Lp.compMeasurePreserving (tr h) (hp h) F) =
      ∫ x, f x * f (x+h) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving F (hp h), hf.coeFn_toLp,
      hf.coeFn_toLp.comp_tendsto (hp h).quasiMeasurePreserving.tendsto_ae] with x hx hy hz
    rw [Real.inner_apply, hx, hy]
    change f x * F (x+h) = _
    rw [show F (x+h) = f (x+h) from hz]
  simpa only [heq] using (continuous_const (y := F)).inner (𝕜 := ℝ) ht

/-- If a nonnegative continuous unit-mass overlap has a subadditive even
deficit with subsequential slope at most one, it equals the triangular
overlap at every frequency. The integral comparison is explicit. -/
theorem overlap_eq_tent_of_small_steps {g : ℝ → ℝ}
    (hg : Continuous g) (hgi : Integrable g) (hg0 : g 0 = 1)
    (hgpos : ∀ x, 0 ≤ g x) (heven : ∀ x, g (-x) = g x)
    (hadd : ∀ x y, 1-g (x+y) ≤ (1-g x)+(1-g y))
    {d c : ℕ → ℝ} {L : ℝ} (hpos : ∀ j, 0 < d j) (hd : Tendsto d atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 L)) (hL : L ≤ 1) (hstep : ∀ j, 1-g (d j) ≤ c j * d j)
    (hti : Integrable (fun x : ℝ => max 0 (1-|x|)))
    (hmass : (∫ x : ℝ, max 0 (1-|x|)) = ∫ x, g x) :
    ∀ x, g x = max 0 (1-|x|) := by
  have hle (x : ℝ) : max 0 (1-|x|) ≤ g x := by
    apply max_le (hgpos x)
    have h := subadditive_le_of_small_steps (continuous_const.sub hg)
      (by simpa using sub_eq_zero.mpr hg0.symm) hadd hpos hd hc hstep (abs_nonneg x)
    have h' := mul_le_mul_of_nonneg_right hL (abs_nonneg x)
    have hs : g |x| = g x := by
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_neg hx, heven]
    change 1 - g |x| ≤ L * |x| at h
    rw [hs] at h
    linarith
  have hae := (integral_eq_iff_of_ae_le hti hgi (Eventually.of_forall hle)).mp hmass
  have eqn := Measure.eq_of_ae_eq hae (continuous_const.max (continuous_const.sub continuous_abs)) hg
  intro x
  exact (congrFun eqn x).symm


/-- A subsequential slope at most one for the regular structure factor of a
unit-mass spectral multiplier forces the global triangular covariogram. -/
theorem overlap_triangle_of_subsequential_slope {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hmass : (∫ t, f t) = 1)
    {d : ℕ → ℝ} {L : ℝ} (hdpos : ∀ j, 0 < d j) (hd : Tendsto d atTop (𝓝 0))
    (hslope : Tendsto (fun j => structureFactor f (d j) / d j) atTop (𝓝 L)) (hL : L ≤ 1) :
    ∀ h : ℝ, (∫ t, f t * f (t+h)) = max (1-|h|) 0 := by
  have hbnd : ∀ᵐ t, ‖f t‖ ≤ (1 : ℝ) := by
    filter_upwards [hb] with t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hf2 : MemLp f 2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa [pow_two] using hf.mul_bdd hf.aestronglyMeasurable hbnd)
  let g := fun h : ℝ => ∫ t, f t * f (t+h)
  have hg : Continuous g := continuous_overlap hf2
  have hc : Continuous (structureFactor f) := continuous_const.sub hg
  have hsmall : Tendsto (fun j => structureFactor f (d j)) atTop (𝓝 0) := by
    have hp : Tendsto (fun j => (structureFactor f (d j) / d j) * d j) atTop (𝓝 (L * 0)) :=
      hslope.mul hd
    simpa only [mul_zero] using hp.congr' (Eventually.of_forall
      (fun j => div_mul_cancel₀ (structureFactor f (d j)) (hdpos j).ne'))
  have hzero : structureFactor f 0 = 0 :=
    tendsto_nhds_unique (hc.continuousAt.tendsto.comp hd) hsmall
  have h01 := binary_of_structureFactor_zero hf hb hmass hzero
  have hgi := integrable_overlap_integral hf
  have hgpos (h : ℝ) : 0 ≤ g h := by
    apply integral_nonneg_of_ae
    filter_upwards [hb, (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hb]
      with t hp hq
    exact mul_nonneg hp.1 hq.1
  have hgeven (h : ℝ) : g (-h) = g h := by
    have hv := structureFactor_even f h
    change 1 - g (-h) = 1 - g h at hv
    linarith
  have hg0 : g 0 = 1 := by
    change 1 - g 0 = 0 at hzero
    linarith
  have htri := overlap_eq_tent_of_small_steps hg hgi.1 hg0 hgpos hgeven
    (structureFactor_subadditive hf hmass h01) hdpos hd hslope hL
    (fun j => le_of_eq (div_mul_cancel₀ _ (hdpos j).ne').symm)
    (by simpa [max_comm] using unitTent_integrable)
    (by rw [show (∫ x : ℝ, max 0 (1 - |x|)) = 1 from by simpa [max_comm] using integral_unitTent,
            hgi.2, hmass, one_pow])
  intro h
  simpa [g, max_comm] using htri h

/-- The full sine pair density follows from the same single positive sequence. -/
theorem sine_pair_of_subsequential_slope {f : ℝ → ℝ} (hf : Integrable f)
    (hb : ∀ᵐ t, 0 ≤ f t ∧ f t ≤ 1) (hmass : (∫ t, f t) = 1)
    {d : ℕ → ℝ} {L : ℝ} (hdpos : ∀ j, 0 < d j) (hd : Tendsto d atTop (𝓝 0))
    (hslope : Tendsto (fun j => structureFactor f (d j) / d j) atTop (𝓝 L)) (hL : L ≤ 1)
    (x : ℝ) :
    1 - ‖𝓕 (fun t => (f t : ℂ)) (-x)‖ ^ 2 = 1 - Real.sinc (Real.pi*x)^2 :=
  fourier_pair_of_triangle_ae hf (Eventually.of_forall
    (overlap_triangle_of_subsequential_slope hf hb hmass hdpos hd hslope hL)) x

end RiemannResearch.DPPSpectral

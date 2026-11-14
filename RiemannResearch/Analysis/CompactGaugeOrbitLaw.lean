import RiemannResearch.Analysis.InfiniteTorusCharacters
import RiemannResearch.Probability.CompactMomentConvergence
import RiemannResearch.Analysis.CompactGaugeOrbit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite-character convergence transfers to the infinite Hilbert orbit

The character limits are explicit hypotheses. Compactness constructs a unique
positive probability measure, including non-Haar laws, and norm continuity of
CompactGaugeOrbit.primeOrbit transfers weak convergence to the Hilbert space.
Fixed uncentered and centered covariance pairings converge. Positivity and a
concrete contraction bound are proved for the uncentered quadratic form.
No actual-zero character convergence, trace-norm theorem, DPP identification,
or arithmetic signed-measure extension is asserted by this module.

Analytic motivation and normalization distinction:
Ford--Zaharescu (2005), https://arxiv.org/abs/math/0405459, equations (1.3)--(1.7);
Ford--Meng--Zaharescu (2017), https://arxiv.org/abs/1511.06814,
Theorem 1 and Corollary 1.1. These references motivate the application; their
analytic conclusions are not imported as axioms. The elementary normalization
identity retains the signed correction before taking a limit.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.Analysis.CompactGaugeOrbitLaw
open CompactGaugeOrbit
open CompactCharacter
abbrev PrimeTorus := Nat.Primes → Circle
abbrev HilbertSpace := SampledGauge.Space (Nat.Primes × ℕ)
local instance : MeasurableSpace PrimeTorus := borel PrimeTorus
local instance : BorelSpace PrimeTorus := ⟨rfl⟩
local instance : MeasurableSpace HilbertSpace := borel HilbertSpace
local instance : BorelSpace HilbertSpace := ⟨rfl⟩

def orbitLaw (h : HilbertSpace) (μ : ProbabilityMeasure PrimeTorus) :
    ProbabilityMeasure HilbertSpace :=
  μ.map (primeOrbit_continuous h).measurable.aemeasurable

theorem tendsto_of_character_integrals {I : Type*} {l : Filter I}
    (μ : I → ProbabilityMeasure PrimeTorus) (ν : ProbabilityMeasure PrimeTorus)
    (hchar : ∀ s : List (Nat.Primes × ℤ),
      Tendsto (fun i => ∫ z, character s z ∂(μ i)) l
        (𝓝 (∫ z, character s z ∂ν))) :
    Tendsto μ l (𝓝 ν) :=
  ProbabilityMeasure.tendsto_of_dense_test_integrals character characters_dense μ ν hchar

theorem exists_limit_of_character_integrals {I : Type*} {l : Filter I} [NeBot l]
    (μ : I → ProbabilityMeasure PrimeTorus) (c : List (Nat.Primes × ℤ) → ℂ)
    (hchar : ∀ s, Tendsto (fun i => ∫ z, character s z ∂(μ i)) l (𝓝 (c s))) :
    ∃ ν : ProbabilityMeasure PrimeTorus,
      (∀ s, ∫ z, character s z ∂ν = c s) ∧ Tendsto μ l (𝓝 ν) :=
  ProbabilityMeasure.exists_limit_of_dense_test_integrals character characters_dense μ c hchar

theorem tendsto_orbitLaw_of_character_integrals {I : Type*} {l : Filter I}
    (h : HilbertSpace)
    (μ : I → ProbabilityMeasure PrimeTorus) (ν : ProbabilityMeasure PrimeTorus)
    (hchar : ∀ s : List (Nat.Primes × ℤ),
      Tendsto (fun i => ∫ z, character s z ∂(μ i)) l
        (𝓝 (∫ z, character s z ∂ν))) :
    Tendsto (fun i => orbitLaw h (μ i)) l (𝓝 (orbitLaw h ν)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν
    (tendsto_of_character_integrals μ ν hchar) (primeOrbit_continuous h)

theorem tendsto_continuous_observable {I : Type*} {l : Filter I}
    (h : HilbertSpace)
    (μ : I → ProbabilityMeasure PrimeTorus) (ν : ProbabilityMeasure PrimeTorus)
    (hchar : ∀ s : List (Nat.Primes × ℤ),
      Tendsto (fun i => ∫ z, character s z ∂(μ i)) l
        (𝓝 (∫ z, character s z ∂ν)))
    (F : HilbertSpace → ℂ) (hF : Continuous F) :
    Tendsto (fun i => ∫ z, F (primeOrbit h z) ∂(μ i)) l
      (𝓝 (∫ z, F (primeOrbit h z) ∂ν)) := by
  let f : C(PrimeTorus, ℂ) := ⟨fun z => F (primeOrbit h z), hF.comp (primeOrbit_continuous h)⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (tendsto_of_character_integrals μ ν hchar)
    (ContinuousMap.equivBoundedOfCompact PrimeTorus ℂ f)

theorem tendsto_covariance_pairing {I : Type*} {l : Filter I}
    (h : HilbertSpace)
    (μ : I → ProbabilityMeasure PrimeTorus) (ν : ProbabilityMeasure PrimeTorus)
    (hchar : ∀ s : List (Nat.Primes × ℤ),
      Tendsto (fun i => ∫ z, character s z ∂(μ i)) l
        (𝓝 (∫ z, character s z ∂ν)))
    (u v : HilbertSpace) :
    Tendsto (fun i => ∫ z,
      inner ℂ u (primeOrbit h z) * inner ℂ (primeOrbit h z) v ∂(μ i)) l
      (𝓝 (∫ z, inner ℂ u (primeOrbit h z) * inner ℂ (primeOrbit h z) v ∂ν)) :=
  tendsto_continuous_observable h μ ν hchar
    (fun x => inner ℂ u x * inner ℂ x v)
    ((continuous_const.inner continuous_id).mul (continuous_id.inner continuous_const))



/-- Centering retains both mean factors for a possibly non-Haar law. -/
def centeredCovariance (h : HilbertSpace) (μ : ProbabilityMeasure PrimeTorus)
    (u v : HilbertSpace) : ℂ :=
  (∫ z, inner ℂ u (primeOrbit h z) * inner ℂ (primeOrbit h z) v ∂μ) -
    (∫ z, inner ℂ u (primeOrbit h z) ∂μ) *
      (∫ z, inner ℂ (primeOrbit h z) v ∂μ)

theorem tendsto_centeredCovariance {I : Type*} {l : Filter I}
    (h : HilbertSpace)
    (μ : I → ProbabilityMeasure PrimeTorus) (ν : ProbabilityMeasure PrimeTorus)
    (hchar : ∀ s : List (Nat.Primes × ℤ),
      Tendsto (fun i => ∫ z, character s z ∂(μ i)) l
        (𝓝 (∫ z, character s z ∂ν)))
    (u v : HilbertSpace) :
    Tendsto (fun i => centeredCovariance h (μ i) u v) l
      (𝓝 (centeredCovariance h ν u v)) := by
  exact (tendsto_covariance_pairing h μ ν hchar u v).sub
    ((tendsto_continuous_observable h μ ν hchar (fun x => inner ℂ u x)
      (continuous_const.inner continuous_id)).mul
    (tendsto_continuous_observable h μ ν hchar (fun x => inner ℂ x v)
      (continuous_id.inner continuous_const)))

/-- Positivity and the exact uniform bound for the uncentered quadratic form.
This is not a construction of a DPP on the zero ordinates. -/
theorem covariance_quadratic_bounds (h : HilbertSpace)
    (μ : ProbabilityMeasure PrimeTorus) (u : HilbertSpace) :
    0 ≤ ∫ z, ‖inner ℂ u (primeOrbit h z)‖ ^ 2 ∂μ ∧
      (∫ z, ‖inner ℂ u (primeOrbit h z)‖ ^ 2 ∂μ) ≤ ‖h‖ ^ 2 * ‖u‖ ^ 2 := by
  let f : C(PrimeTorus, ℝ) :=
    ⟨fun z => ‖inner ℂ u (primeOrbit h z)‖ ^ 2,
      ((continuous_const.inner (primeOrbit_continuous h)).norm.pow 2)⟩
  have hf : Integrable (fun z => ‖inner ℂ u (primeOrbit h z)‖ ^ 2) (μ : Measure _) :=
    (ContinuousMap.equivBoundedOfCompact PrimeTorus ℝ f).integrable _
  refine ⟨integral_nonneg (fun _ => sq_nonneg _), ?_⟩
  calc
    _ ≤ ∫ _ : PrimeTorus, ‖h‖ ^ 2 * ‖u‖ ^ 2 ∂μ := by
      apply integral_mono hf (integrable_const _)
      intro z
      have hn := norm_inner_le_norm (𝕜 := ℂ) u (primeOrbit h z)
      rw [primeOrbit_norm] at hn
      calc
        _ ≤ (‖u‖ * ‖h‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by ring
    _ = _ := by simp

/-- A concrete scale proves the positive-contraction quadratic bound without
postulating positivity of the arithmetic signed correction. -/
theorem normalized_covariance_quadratic_bounds (h : HilbertSpace)
    (μ : ProbabilityMeasure PrimeTorus) (u : HilbertSpace) :
    0 ≤ (∫ z, ‖inner ℂ u (primeOrbit h z)‖ ^ 2 ∂μ) / (1 + ‖h‖ ^ 2) ∧
      (∫ z, ‖inner ℂ u (primeOrbit h z)‖ ^ 2 ∂μ) / (1 + ‖h‖ ^ 2) ≤ ‖u‖ ^ 2 := by
  have hb := covariance_quadratic_bounds h μ u
  refine ⟨div_nonneg hb.1 (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < 1 + ‖h‖ ^ 2)).mpr
  nlinarith [sq_nonneg ‖u‖]

/-- The limiting torus law is constructed, with no candidate law, independence,
or positivity hypothesis supplied by the caller. -/
theorem existsUnique_orbit_limit {I : Type*} {l : Filter I} [NeBot l]
    (h : HilbertSpace)
    (μ : I → ProbabilityMeasure PrimeTorus) (c : List (Nat.Primes × ℤ) → ℂ)
    (hchar : ∀ s, Tendsto (fun i => ∫ z, character s z ∂(μ i)) l (𝓝 (c s))) :
    ∃! ν : ProbabilityMeasure PrimeTorus,
      (∀ s, ∫ z, character s z ∂ν = c s) ∧
      Tendsto μ l (𝓝 ν) ∧
      Tendsto (fun i => orbitLaw h (μ i)) l (𝓝 (orbitLaw h ν)) := by
  obtain ⟨ν, hm, hconv⟩ := exists_limit_of_character_integrals μ c hchar
  refine ⟨ν, ⟨hm, hconv, ?_⟩, ?_⟩
  · exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν
      hconv (primeOrbit_continuous h)
  · intro η hη
    exact tendsto_nhds_unique hη.2.1 hconv

/-- Exact identity separating a probability average from its centered correction. -/
theorem normalized_centered_identity (a n t m : ℂ) (hn : n ≠ 0) (ht : t ≠ 0) :
    a / n = m + (t / n) * ((a - n * m) / t) := by
  field_simp [hn, ht]
  ring

/-- An order-scale signed correction disappears at probability normalization
when the scale/count ratio tends to zero. The correction limit may be nonzero. -/
theorem normalized_limit_of_centered_limit {I : Type*} {l : Filter I}
    (a n t : I → ℂ) (m b : ℂ)
    (hn : ∀ᶠ i in l, n i ≠ 0) (ht : ∀ᶠ i in l, t i ≠ 0)
    (hratio : Tendsto (fun i => t i / n i) l (𝓝 0))
    (hcenter : Tendsto (fun i => (a i - n i * m) / t i) l (𝓝 b)) :
    Tendsto (fun i => a i / n i) l (𝓝 m) := by
  have h : Tendsto (fun i => m + (t i / n i) * ((a i - n i * m) / t i)) l
      (𝓝 (m + 0 * b)) := tendsto_const_nhds.add (hratio.mul hcenter)
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [hn, ht] with i hni hti
  exact (normalized_centered_identity (a i) (n i) (t i) m hni hti).symm

end RiemannResearch.Analysis.CompactGaugeOrbitLaw

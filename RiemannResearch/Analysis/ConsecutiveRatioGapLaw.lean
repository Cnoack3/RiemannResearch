import RiemannResearch.Analysis.ConsecutiveRatioOrbitLaw
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Order.Interval.Set.Infinite

/-! # The law of encoded gaps and the image of the real orbit

Two backward ratios at a shared displacement are a Borel encoding of one
real gap. This also gives a Borel encoding of an entire labeled gap sequence.
Every actual encoded law can be recovered from its pushforward. The image for
one common real displacement has zero product Haar mass in the two-torus.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus
open RatioChainHaar
open scoped RiemannResearch.Analysis.RatioChainHaar

def encodeGap (p q r : Nat.Primes) (t : ℝ) : Circle × Circle :=
  (backwardPhase p q t, backwardPhase q r t)

theorem continuous_encodeGap (p q r : Nat.Primes) : Continuous (encodeGap p q r) := by
  change Continuous (fun t : ℝ => (backwardPhase p q t, backwardPhase q r t))
  simp only [backwardPhase_eq_exp]
  exact (Circle.exp.continuous.comp ((continuous_const.mul continuous_id).neg)).prodMk
    (Circle.exp.continuous.comp ((continuous_const.mul continuous_id).neg))

theorem measurableEmbedding_encodeGap {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) : MeasurableEmbedding (encodeGap p q r) :=
  (continuous_encodeGap p q r).measurableEmbedding (backwardTriple_injective hpq hqr)

theorem encoded_gap_law_eq_iff {p q r : Nat.Primes} (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r)
    (μ ν : Measure ℝ) : μ.map (encodeGap p q r) = ν.map (encodeGap p q r) ↔ μ = ν :=
  (measurableEmbedding_encodeGap hpq hqr).map_injective.eq_iff

theorem denseRange_consecutive_encodeGap (n : ℕ) :
    DenseRange (encodeGap (orderedPrime n) (orderedPrime (n+1)) (orderedPrime (n+2))) := by
  let f := fun y : Chain => (y n, y (n+1))
  have hf : Continuous f := (continuous_apply n).prodMk (continuous_apply (n+1))
  have hsurj : Function.Surjective f := by
    rintro ⟨a,b⟩
    exact ⟨fun j => if j = n then a else b, by simp [f]⟩
  exact hsurj.denseRange.comp dense_primeRatio_orbit hf

/-- Each site observes one real length using its specified consecutive triple. -/
def encodeGapSequence (n : ℕ → ℕ) (g : ℕ → ℝ) (j : ℕ) : Circle × Circle :=
  encodeGap (orderedPrime (n j)) (orderedPrime (n j+1)) (orderedPrime (n j+2)) (g j)

theorem measurableEmbedding_encodeGapSequence (n : ℕ → ℕ) :
    MeasurableEmbedding (encodeGapSequence n) := by
  have hc : Continuous (encodeGapSequence n) :=
    continuous_pi fun j => (continuous_encodeGap _ _ _).comp (continuous_apply j)
  apply hc.measurableEmbedding
  intro g h he
  funext j
  exact backwardTriple_injective (orderedPrime_next (n j)).1 (orderedPrime_next (n j+1)).1
    (congrFun he j)

theorem encoded_gap_sequence_law_eq_iff (n : ℕ → ℕ) (μ ν : Measure (ℕ → ℝ)) :
    μ.map (encodeGapSequence n) = ν.map (encodeGapSequence n) ↔ μ = ν :=
  (measurableEmbedding_encodeGapSequence n).map_injective.eq_iff

theorem circleHaar_nullSingleton : NullSingletonClass circleHaar := by
  have : circleHaar.IsHaarMeasure := by unfold circleHaar; infer_instance
  have : Infinite (Ioc (-Real.pi) Real.pi) :=
    (Ioc_infinite (show -Real.pi < Real.pi by linarith [Real.pi_pos])).to_subtype
  have : Infinite Circle :=
    Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective
  constructor
  intro x
  by_contra hx
  have h := (infinite_univ : (univ : Set Circle).Infinite).meas_eq_top
    (μ := circleHaar) ⟨_, hx, fun y _ => ((Measure.haar_singleton circleHaar x).trans
      (Measure.haar_singleton circleHaar y).symm).le⟩
  simp at h

/-- The curve supporting a common real displacement has countable vertical
sections even though the real prime orbit is dense. -/
theorem encoded_gap_range_haar_null {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    circleHaar.prod circleHaar (range (encodeGap p q r)) = 0 := by
  have := circleHaar_nullSingleton
  apply Measure.measure_prod_null_of_ae_null
    (measurableEmbedding_encodeGap hpq hqr).measurableSet_range
  apply Filter.Eventually.of_forall
  intro a
  apply Set.Countable.measure_zero
  let s := logPrimeStep p q
  let f := fun k : ℤ => backwardPhase q r (-((a:ℂ).arg + (k:ℝ)*(2*Real.pi)) / s)
  apply (countable_range f).mono
  rintro b ⟨t, ht⟩
  have h₁ : Circle.exp (-(s*t)) = a := by
    rw [← backwardPhase_eq_exp]
    exact congrArg Prod.fst ht
  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp (h₁.trans (Circle.exp_arg a).symm)
  have ht' : -((a:ℂ).arg + (k:ℝ)*(2*Real.pi)) / s = t :=
    (div_eq_iff (logPrimeStep_pos hpq).ne').2 (by rw [← hk]; ring)
  exact ⟨k, by simpa only [f, ht', encodeGap] using (congrArg Prod.snd ht)⟩

/-- Every law of a real gap is singular to independent circle angles after
encoding. It retains all its mass on the real orbit at each finite height. -/
theorem encoded_gap_law_singular {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) (μ : Measure ℝ) :
    (circleHaar.prod circleHaar).MutuallySingular (μ.map (encodeGap p q r)) := by
  have h := measurableEmbedding_encodeGap hpq hqr
  refine ⟨range _, h.measurableSet_range, encoded_gap_range_haar_null hpq hqr, ?_⟩
  rw [Measure.map_apply h.measurable h.measurableSet_range.compl]
  simp

end RiemannResearch.Analysis.ActualInfinitePrimeTorus

import RiemannResearch.Analysis.SampledGaugeCompleteness
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
/-!
# Compact prime-torus Hilbert orbit
Source: V_vector_space_RH.pdf, Section 3.
This constructs the infinite orbit and proves norm continuity and compactness
in l2, not merely coordinatewise continuity. Arithmetic equidistribution of
actual zero ordinates is not assumed or asserted here.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.CompactGaugeOrbit
open SampledGauge
variable {ι X : Type*} [TopologicalSpace X]
def orbit (h : Space ι) (phase : X → ι → ℂ)
    (hphase : ∀ x i, ‖phase x i‖ = 1) (x : X) : Space ι :=
  ⟨fun i => h i * phase x i, by
    apply Memℓp.of_norm
    simpa only [norm_mul, hphase, mul_one] using (lp.memℓp h).norm⟩

theorem continuous_orbit (h : Space ι) (phase : X → ι → ℂ)
    (hphase : ∀ x i, ‖phase x i‖ = 1)
    (hc : ∀ i, Continuous (fun x => phase x i)) :
    Continuous (orbit h phase hphase) := by
  have hdom : ∀ (i : ι) (x : X × X),
      ‖‖h i * phase x.1 i - h i * phase x.2 i‖ ^ 2‖ ≤ 4 * ‖h i‖ ^ 2 := by
    intro i x
    have hn := norm_sub_le (h i * phase x.1 i) (h i * phase x.2 i)
    simp only [norm_mul, hphase, mul_one] at hn
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (h i * phase x.1 i - h i * phase x.2 i), norm_nonneg (h i)]
  have hc' : Continuous (fun x : X × X =>
      ∑' i, ‖h i * phase x.1 i - h i * phase x.2 i‖ ^ 2) :=
    continuous_tsum
      (fun i => (((hc i).comp continuous_fst).const_mul (h i) |>.sub
        (((hc i).comp continuous_snd).const_mul (h i))).norm.pow 2)
      ((summable_norm_sq h).mul_left 4) hdom
  apply continuous_iff_continuous_dist.mpr
  have hs := Real.continuous_sqrt.comp hc'
  convert hs using 1
  funext x
  have he := norm_sq_eq_tsum (orbit h phase hphase x.1 - orbit h phase hphase x.2)
  change ‖orbit h phase hphase x.1 - orbit h phase hphase x.2‖ ^ 2 =
    ∑' i, ‖h i * phase x.1 i - h i * phase x.2 i‖ ^ 2 at he
  dsimp only [Function.comp_def]
  rw [dist_eq_norm, ← he, Real.sqrt_sq_eq_abs, abs_norm]

def primePhase (z : Nat.Primes → Circle) (q : Nat.Primes × ℕ) : ℂ :=
  (z q.1 : ℂ) ^ (q.2 + 1)

theorem primePhase_norm (z : Nat.Primes → Circle) (q : Nat.Primes × ℕ) :
    ‖primePhase z q‖ = 1 := by simp [primePhase, norm_pow, Circle.norm_coe]

def primeOrbit (h : Space (Nat.Primes × ℕ)) (z : Nat.Primes → Circle) :=
  orbit h primePhase primePhase_norm z

theorem primeOrbit_continuous (h : Space (Nat.Primes × ℕ)) :
    Continuous (primeOrbit h) := by
  exact continuous_orbit h primePhase primePhase_norm (fun q =>
    (continuous_subtype_val.comp (continuous_apply q.1)).pow (q.2 + 1))

theorem primeOrbit_isCompact (h : Space (Nat.Primes × ℕ)) :
    IsCompact (Set.range (primeOrbit h)) :=
  by
  simpa only [Set.image_univ] using isCompact_univ.image (primeOrbit_continuous h)

theorem primeOrbit_norm (h : Space (Nat.Primes × ℕ)) (z : Nat.Primes → Circle) :
    ‖primeOrbit h z‖ = ‖h‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  apply tsum_congr
  intro q
  simp [primeOrbit, orbit, norm_mul, primePhase_norm]
end RiemannResearch.Analysis.CompactGaugeOrbit

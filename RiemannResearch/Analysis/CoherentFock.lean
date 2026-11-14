import RiemannResearch.Analysis.SampledGaugeCompleteness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
/-!
# Coherent Fock vectors in an explicit Hilbert space
Source: V_vector_space_RH.pdf, Section 5.1.
Ordered words give the tensor-sector coordinates; division by sqrt(n!) gives
the coherent exponential. Square summability and the mixed inner-product
identity are proved, including the infinite sum over all sectors.
The symmetric coherent space is the closed span of these vectors.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.CoherentFock
open SampledGauge

def Word (ι : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => ι × Word ι n

def wordProd {ι R : Type*} [Monoid R] (u : ι → R) :
    (n : ℕ) → Word ι n → R
  | 0, _ => 1
  | n + 1, q => u q.1 * wordProd u n q.2

theorem wordProd_nonneg {ι : Type*} {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) :
    ∀ n (q : Word ι n), 0 ≤ wordProd u n q := by
  intro n
  induction n with
  | zero => intro q; exact zero_le_one
  | succ n ih => intro q; exact mul_nonneg (hu q.1) (ih q.2)

theorem wordProd_norm {ι : Type*} (u : ι → ℂ) :
    ∀ n (q : Word ι n), ‖wordProd u n q‖ = wordProd (fun i => ‖u i‖) n q := by
  intro n
  induction n with
  | zero => intro q; simp [wordProd]
  | succ n ih => intro q; simp [wordProd, norm_mul, ih]

theorem wordProd_norm_sq {ι : Type*} (u : ι → ℂ) :
    ∀ n (q : Word ι n), ‖wordProd u n q‖ ^ 2 = wordProd (fun i => ‖u i‖ ^ 2) n q := by
  intro n
  induction n with
  | zero => intro q; simp [wordProd]
  | succ n ih => intro q; simp [wordProd, norm_mul, mul_pow, ih]

theorem wordProd_hasSum_nonneg {ι : Type*} {u : ι → ℝ} {s : ℝ}
    (hu : HasSum u s) (hn : ∀ i, 0 ≤ u i) :
    ∀ n, HasSum (wordProd u n) (s ^ n) := by
  intro n
  induction n with
  | zero =>
    change HasSum (fun _ : PUnit => (1 : ℝ)) (s ^ 0)
    simpa using hasSum_fintype (fun _ : PUnit => (1 : ℝ))
  | succ n ih =>
    simpa only [Word, wordProd, pow_succ'] using
      hu.mul ih (hu.summable.mul_of_nonneg ih.summable hn (wordProd_nonneg hn n))

theorem wordProd_hasSum {ι : Type*} {u : ι → ℂ} {s : ℂ}
    (hu : HasSum u s) (hn : Summable (fun i => ‖u i‖)) :
    ∀ n, HasSum (wordProd u n) (s ^ n) := by
  intro n
  induction n with
  | zero =>
    change HasSum (fun _ : PUnit => (1 : ℂ)) (s ^ 0)
    simpa using hasSum_fintype (fun _ : PUnit => (1 : ℂ))
  | succ n ih =>
    have hn' : Summable (fun q => ‖wordProd u n q‖) := by
      simpa only [wordProd_norm] using
        (wordProd_hasSum_nonneg hn.hasSum (fun i => norm_nonneg _) n).summable
    simpa only [Word, wordProd, pow_succ'] using
      hu.mul ih (summable_mul_of_summable_norm hn hn')

def coefficient {ι : Type*} (u : Space ι) (q : Σ n, Word ι n) : ℂ :=
  wordProd (fun i => u i) q.1 q.2 / (Real.sqrt (q.1.factorial : ℝ) : ℂ)

theorem coefficient_norm_sq {ι : Type*} (u : Space ι) (q : Σ n, Word ι n) :
    ‖coefficient u q‖ ^ 2 =
      wordProd (fun i => ‖u i‖ ^ 2) q.1 q.2 / (q.1.factorial : ℝ) := by
  rw [coefficient, norm_div, div_pow, wordProd_norm_sq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _)]

theorem coefficient_hasSum_sq {ι : Type*} (u : Space ι) :
    HasSum (fun q => ‖coefficient u q‖ ^ 2) (Real.exp (‖u‖ ^ 2)) := by
  have hu : HasSum (fun i => ‖u i‖ ^ 2) (‖u‖ ^ 2) := by
    rw [norm_sq_eq_tsum]
    exact (summable_norm_sq u).hasSum
  have hf : ∀ n, HasSum (fun q : Word ι n => ‖coefficient u ⟨n,q⟩‖ ^ 2)
      ((‖u‖ ^ 2) ^ n / (n.factorial : ℝ)) := by
    intro n
    simpa only [coefficient_norm_sq] using
      (wordProd_hasSum_nonneg hu (fun i => sq_nonneg _) n).div_const (n.factorial : ℝ)
  have he : HasSum (fun n => (‖u‖ ^ 2) ^ n / (n.factorial : ℝ))
      (Real.exp (‖u‖ ^ 2)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (‖u‖ ^ 2)
  apply he.sigma_of_hasSum hf
  apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun n => (hf n).summable, ?_⟩
  simpa only [(hf _).tsum_eq] using he.summable

def vector {ι : Type*} (u : Space ι) : Space (Σ n, Word ι n) :=
  ⟨coefficient u, by
    apply memℓp_gen
    simpa using (coefficient_hasSum_sq u).summable⟩

theorem vector_norm_sq {ι : Type*} (u : Space ι) :
    ‖vector u‖ ^ 2 = Real.exp (‖u‖ ^ 2) := by
  rw [norm_sq_eq_tsum]
  exact (coefficient_hasSum_sq u).tsum_eq

theorem wordProd_pair {ι : Type*} (u v : ι → ℂ) :
    ∀ n (q : Word ι n),
      star (wordProd u n q) * wordProd v n q =
        wordProd (fun i => star (u i) * v i) n q := by
  intro n
  induction n with
  | zero => intro q; simp [wordProd]
  | succ n ih =>
    intro q
    simp only [wordProd, star_mul]
    rw [← ih]
    ring

theorem coefficient_pair {ι : Type*} (u v : Space ι) (q : Σ n, Word ι n) :
    star (coefficient u q) * coefficient v q =
      wordProd (fun i => star (u i) * v i) q.1 q.2 / (q.1.factorial : ℂ) := by
  simp only [coefficient, Complex.star_def, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  have hd : (Real.sqrt (q.1.factorial : ℝ) : ℂ) *
      (Real.sqrt (q.1.factorial : ℝ) : ℂ) = (q.1.factorial : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [hd]
  congr 1
  exact wordProd_pair (fun i => u i) (fun i => v i) q.1 q.2

theorem vector_inner {ι : Type*} (u v : Space ι) :
    inner ℂ (vector u) (vector v) = Complex.exp (inner ℂ u v) := by
  have hu : HasSum (fun i => star (u i) * v i) (inner ℂ u v) := by
    simpa only [RCLike.inner_apply', Complex.star_def] using lp.hasSum_inner (𝕜 := ℂ) u v
  have hn : Summable (fun i => ‖star (u i) * v i‖) := by
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _
      (((summable_norm_sq u).add (summable_norm_sq v)).div_const 2)
    intro i
    simp only [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]
  have hf : ∀ n, HasSum
      (fun q : Word ι n => star (coefficient u ⟨n,q⟩) * coefficient v ⟨n,q⟩)
      ((inner ℂ u v)^n / (n.factorial : ℂ)) := by
    intro n
    simpa only [coefficient_pair] using (wordProd_hasSum hu hn n).div_const (n.factorial : ℂ)
  have ha : HasSum (fun q => star (coefficient u q) * coefficient v q)
      (inner ℂ (vector u) (vector v)) := by
    simpa only [RCLike.inner_apply', Complex.star_def, vector] using
      lp.hasSum_inner (𝕜 := ℂ) (vector u) (vector v)
  have he : HasSum (fun n => (inner ℂ u v)^n / (n.factorial : ℂ))
      (Complex.exp (inner ℂ u v)) := by
    simpa only [Complex.exp_eq_exp_ℂ] using
      NormedSpace.expSeries_div_hasSum_exp (inner ℂ u v)
  exact (ha.sigma hf).unique he

/-- The symmetric coherent subspace of the ordered-word Hilbert model. -/
def symmetricSpace (ι : Type*) : Submodule ℂ (Space (Σ n, Word ι n)) :=
  (Submodule.span ℂ (Set.range (vector (ι := ι)))).topologicalClosure

theorem vector_mem_symmetricSpace {ι : Type*} (u : Space ι) :
    vector u ∈ symmetricSpace ι :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨u, rfl⟩)
end RiemannResearch.Analysis.CoherentFock

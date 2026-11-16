import RiemannResearch.Analysis.FiniteTranslationEnergy
import RiemannResearch.RH.ScrewPrimePart
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith

/-!
# Sharp prime cutoff symbols and exact local stabilization

Source: user-provided `v_prime_side_factorization_A_F_audited.pdf`,
Theorems 11.7--11.8 and Tracks E/F4/F5.
The sharp scalar-repair equivalence strengthens the asymptotic obstruction:
it holds at each cutoff and needs neither PNT nor RH.
The stabilization theorem permits any compactly supported kernel and arbitrary
finite windows of shifts, not only prime-power logarithms.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.WeilPrimeCutoff
open RiemannResearch.Analysis.FiniteTranslationEnergy

def primeMass (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, primePowerWeight n

def primeSymbol (N : ℕ) (t : ℝ) : ℝ :=
  cosineSymbol (Finset.range N) primePowerWeight (fun n => Real.log n) t

theorem primeSymbol_lower_bound (N : ℕ) (t : ℝ) :
    -2 * primeMass N ≤ primeSymbol N t :=
  cosineSymbol_lower_bound _ _ _ (fun n _ => primePowerWeight_nonneg n) t

@[simp] theorem primeSymbol_zero (N : ℕ) :
    primeSymbol N 0 = -2 * primeMass N :=
  cosineSymbol_zero _ _ _

theorem primeSymbol_scalar_repair_iff (N : ℕ) (b : ℝ) :
    (∀ t, 0 ≤ primeSymbol N t + b) ↔ 2 * primeMass N ≤ b :=
  scalar_repair_iff _ _ _ (fun n _ => primePowerWeight_nonneg n) b

def kernelTerm (C : ℝ → ℂ) (d : ℝ) (n : ℕ) : ℂ :=
  (primePowerWeight n : ℂ) * (C (Real.log n - d) + C (-Real.log n - d))

def primeKernel (C : ℝ → ℂ) (d : ℝ) : ℂ :=
  -∑' n : ℕ, kernelTerm C d n

def cutoffKernel (N : ℕ) (C : ℝ → ℂ) (d : ℝ) : ℂ :=
  -∑ n ∈ Finset.range N, kernelTerm C d n

theorem kernelTerm_eq_zero_of_cutoff {C : ℝ → ℂ} {B D d : ℝ}
    (hC : ∀ u, B < |u| → C u = 0) (hd : |d| ≤ D)
    {N n : ℕ} (hN : Real.exp (D + B) < N) (hn : N ≤ n) :
    kernelTerm C d n = 0 := by
  have hne : Real.exp (D + B) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hnp : 0 < (n : ℝ) := lt_trans (Real.exp_pos _) hne
  have hlog : D + B < Real.log n := (Real.lt_log_iff_exp_lt hnp).2 hne
  have hd' := abs_le.mp hd
  have hp : C (Real.log n - d) = 0 := by
    apply hC
    exact lt_of_lt_of_le (by linarith : B < Real.log n - d) (le_abs_self _)
  have hm : C (-Real.log n - d) = 0 := by
    apply hC
    exact lt_of_lt_of_le (by linarith : B < -(-Real.log n - d)) (neg_le_abs _)
  simp [kernelTerm, hp, hm]

/-- Exact equality with the infinite prime sum at an explicit local cutoff. -/
theorem primeKernel_eq_cutoff {C : ℝ → ℂ} {B D d : ℝ}
    (hC : ∀ u, B < |u| → C u = 0) (hd : |d| ≤ D)
    (N : ℕ) (hN : Real.exp (D + B) < N) :
    primeKernel C d = cutoffKernel N C d := by
  unfold primeKernel cutoffKernel
  congr 1
  apply tsum_eq_sum
  intro n hn
  exact kernelTerm_eq_zero_of_cutoff hC hd hN
    (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn))

theorem kernelTerm_summable {C : ℝ → ℂ} {B D d : ℝ}
    (hC : ∀ u, B < |u| → C u = 0) (hd : |d| ≤ D) :
    Summable (kernelTerm C d) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (D + B))
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  exact kernelTerm_eq_zero_of_cutoff hC hd hN
    (Nat.le_of_not_lt (by simpa only [Finset.mem_range] using hn))

/-- Uniform equality for every entry of a prescribed finite Galerkin window. -/
theorem finite_window_stabilization {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {C : ℝ → ℂ} {B D : ℝ}
    (hC : ∀ u, B < |u| → C u = 0)
    (hD : ∀ i ∈ s, ∀ j ∈ s, |x i - x j| ≤ D)
    (N M : ℕ) (hN : Real.exp (D + B) < N) (hM : Real.exp (D + B) < M) :
    ∀ i ∈ s, ∀ j ∈ s,
      cutoffKernel N C (x i - x j) = cutoffKernel M C (x i - x j) := by
  intro i hi j hj
  rw [← primeKernel_eq_cutoff hC (hD i hi j hj) N hN,
    ← primeKernel_eq_cutoff hC (hD i hi j hj) M hM]

end RiemannResearch.RH.WeilPrimeCutoff

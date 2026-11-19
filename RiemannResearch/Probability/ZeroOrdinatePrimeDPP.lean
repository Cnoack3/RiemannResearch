import RiemannResearch.Probability.ZeroOrdinateFiberDPP
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.FunProp

/-!
# Saturation using prime frequencies alone

If frequencies approximate every large real argument with an error tending
to zero, shifted copies of a finite Fourier cardinal interpolant approximate
exactly one ordinate fibre in a unit shell. All approximants belong to a
fixed finite-dimensional coordinate window, so the fibre indicator lies in
the algebraic feature span. The repository's prime number theorem supplies
the required frequency approximation by logarithms of primes.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate

private theorem phase_add_frequency (a b t : ℝ) :
    harmonicPhase (a + b) t = harmonicPhase a t * harmonicPhase b t := by
  unfold harmonicPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_phase (a t : ℝ) : ‖harmonicPhase a t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phase_zero_left (t : ℝ) : harmonicPhase 0 t = 1 := by simp [harmonicPhase]

private theorem phase_continuous (t : ℝ) : Continuous (fun a : ℝ => harmonicPhase a t) := by
  unfold harmonicPhase
  fun_prop

private theorem phase_modulate (u t τ : ℝ) :
    harmonicPhase u (t - τ) = harmonicPhase (-u) τ * harmonicPhase u t := by
  unfold harmonicPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def unitSites (n : ℕ) : Finset Site :=
  (bounded_sites_finite ((n : ℝ) + 1)).toFinset.filter (fun i => (n : ℝ) < ordinate i)

private theorem mem_unitSites {n : ℕ} {j : Site} :
    j ∈ unitSites n ↔ (n : ℝ) < ordinate j ∧ ordinate j ≤ (n : ℝ) + 1 := by
  simp only [unitSites, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact and_comm

private theorem shell_sum_eq_cutoff_difference (n : ℕ) (f : ℝ → ℝ) :
    (∑ j ∈ unitSites n, f (ordinate j) • coordinate j) =
      cutoffVector (n + 1 : ℕ) f - cutoffVector n f := by
  apply coordinate_ext
  intro j
  rw [inner_sum, inner_sub_right, cutoffVector_coordinate, cutoffVector_coordinate]
  simp only [inner_smul_right, coordinate_inner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Nat.cast_add, Nat.cast_one, mem_unitSites]
  by_cases hl : ordinate j ≤ (n : ℝ)
  · have hh : ordinate j ≤ (n : ℝ) + 1 := by linarith
    simp [hl, hh, not_lt.mpr hl]
  · by_cases hh : ordinate j ≤ (n : ℝ) + 1 <;> simp [hl, hh, lt_of_not_ge hl]

private theorem cutoff_complex_fourier_mem (q : ℕ → ℝ) (n : ℕ) (F : Finset ℕ)
    (a : ℕ → ℂ) (k : ℕ → ℕ) :
    cutoffVector n (fun t => (∑ m ∈ F, a m * harmonicPhase (q (k m)) t).re) ∈
      Submodule.span ℝ (Set.range (feature q)) := by
  classical
  let S := Submodule.span ℝ (Set.range (feature q))
  induction F using Finset.induction_on with
  | empty => simp [cutoffVector]
  | @insert m F hm hF =>
    have hcos : cutoffVector n (fun t => Real.cos (q (k m) * t)) ∈ S :=
      Submodule.subset_span ⟨(n, k m, false), rfl⟩
    have hsin : cutoffVector n (fun t => Real.sin (q (k m) * t)) ∈ S :=
      Submodule.subset_span ⟨(n, k m, true), rfl⟩
    have he : cutoffVector n (fun t => (∑ u ∈ insert m F, a u * harmonicPhase (q (k u)) t).re) =
        (a m).re • cutoffVector n (fun t => Real.cos (q (k m) * t)) +
        (-(a m).im) • cutoffVector n (fun t => Real.sin (q (k m) * t)) +
        cutoffVector n (fun t => (∑ u ∈ F, a u * harmonicPhase (q (k u)) t).re) := by
      unfold cutoffVector
      simp only [Finset.sum_insert hm, Complex.add_re, Complex.mul_re, harmonicPhase_re,
        harmonicPhase_im, sub_eq_add_neg, ← neg_mul, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum, smul_smul]
    rw [he]
    exact S.add_mem (S.add_mem (S.smul_mem _ hcos) (S.smul_mem _ hsin)) hF

/-- Asymptotic additive density of frequencies suffices for exact algebraic
interpolation in every unit height shell. -/
theorem fiberVector_mem_span_of_frequency_mesh (q : ℕ → ℝ) (k : ℝ → ℕ)
    (hmesh : Tendsto (fun s => q (k s) - s) atTop (𝓝 0)) (i : Site) :
    fiberVector i ∈ Submodule.span ℝ (Set.range (feature q)) := by
  classical
  let n := ⌈ordinate i⌉₊ - 1
  have hp : 0 < ⌈ordinate i⌉₊ := Nat.ceil_pos.mpr i.1.property.2
  have hn : n + 1 = ⌈ordinate i⌉₊ := by dsimp [n]; omega
  have hceil : (n : ℝ) + 1 = (⌈ordinate i⌉₊ : ℝ) := by exact_mod_cast hn
  let A := unitSites n
  have hi : i ∈ A := mem_unitSites.mpr ⟨Nat.lt_ceil.mp (by omega),
    hceil.symm ▸ Nat.le_ceil (ordinate i)⟩
  obtain ⟨F, a, hcard⟩ := exists_shell_cardinal_fourier n A i hi
    (fun j hj => mem_unitSites.mp hj)
  let err := fun (s : ℝ) (m : ℕ) => q (k (s + m)) - (s + m)
  have herr (m : ℕ) : Tendsto (fun s => err s m) atTop (𝓝 0) :=
    hmesh.comp (tendsto_atTop_add_const_right _ (m : ℝ) tendsto_id)
  let B := fun (s t : ℝ) => ∑ m ∈ F, a m * harmonicPhase (m : ℝ) t * harmonicPhase (err s m) t
  let G := fun (s t : ℝ) => harmonicPhase s (t - ordinate i) * B s t
  have hB (j : Site) (hj : j ∈ A) : Tendsto (fun s => B s (ordinate j)) atTop
      (𝓝 (if ordinate j = ordinate i then (1 : ℂ) else 0)) := by
    rw [← hcard j hj]
    apply tendsto_finsetSum
    intro m _
    have h := ((phase_continuous (ordinate j)).tendsto 0).comp (herr m)
    simpa only [Function.comp_apply, phase_zero_left, mul_one] using h.const_mul (a m * harmonicPhase (m : ℝ) (ordinate j))
  have hG (j : Site) (hj : j ∈ A) : Tendsto (fun s => G s (ordinate j)) atTop
      (𝓝 (if ordinate j = ordinate i then (1 : ℂ) else 0)) := by
    have h := hB j hj
    by_cases he : ordinate j = ordinate i
    · simpa [G, he, harmonicPhase] using h
    · rw [if_neg he] at h ⊢
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [G, norm_mul, norm_phase, one_mul, norm_zero] using h.norm
  have hrep (s t : ℝ) : G s t =
      ∑ m ∈ F, (a m * harmonicPhase (-s) (ordinate i)) * harmonicPhase (q (k (s + m))) t := by
    dsimp only [G, B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hq : q (k (s + m)) = s + m + err s m := by dsimp only [err]; ring
    rw [hq, phase_add_frequency, phase_add_frequency, phase_modulate]
    ring
  let V := Submodule.span ℝ (Set.range (feature q))
  let W := Submodule.span ℝ (coordinate '' (A : Set Site))
  let : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (A.finite_toSet.image coordinate)
  let : FiniteDimensional ℝ (V ⊓ W : Submodule ℝ Space) :=
    FiniteDimensional.of_injective (Submodule.inclusion (show V ⊓ W ≤ W from inf_le_right))
      (Submodule.inclusion_injective _)
  let v := fun s : ℝ => ∑ j ∈ A, (G s (ordinate j)).re • coordinate j
  have hv (s : ℝ) : v s ∈ V ⊓ W := by
    constructor
    · change (∑ j ∈ unitSites n, (G s (ordinate j)).re • coordinate j) ∈ V
      rw [shell_sum_eq_cutoff_difference n (fun t => (G s t).re)]
      simp_rw [hrep]
      exact V.sub_mem (cutoff_complex_fourier_mem q (n + 1) F _ _)
        (cutoff_complex_fourier_mem q n F _ _)
    · apply Submodule.sum_mem
      intro j hj
      exact W.smul_mem _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  let δ := fun j : Site => if ordinate j = ordinate i then (1 : ℝ) else 0
  have ht : Tendsto v atTop (𝓝 (∑ j ∈ A, δ j • coordinate j)) := by
    apply tendsto_finsetSum
    intro j hj
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (hG j hj)
    have hreal : (if ordinate j = ordinate i then (1 : ℂ) else 0).re = δ j := by
      by_cases he : ordinate j = ordinate i <;> simp [δ, he]
    rw [hreal] at hh
    exact hh.smul_const (coordinate j)
  have hf : (∑ j ∈ A, δ j • coordinate j) = fiberVector i := by
    apply coordinate_ext
    intro j
    rw [inner_sum, inner_coordinate_fiberVector]
    simp only [inner_smul_right, coordinate_inner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    by_cases hj : j ∈ A
    · simp [hj, δ]
    · have hne : ordinate j ≠ ordinate i := by
        intro he
        apply hj
        exact mem_unitSites.mpr (he.symm ▸ mem_unitSites.mp hi)
      simp [hj, hne]
  rw [hf] at ht
  exact ((V ⊓ W).closed_of_finiteDimensional.mem_of_tendsto ht
    (Eventually.of_forall hv)).1

private theorem prime_above_exists (x : ℝ) : ∃ p : ℕ, p.Prime ∧ x ≤ (p : ℝ) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes ⌈x⌉₊
  exact ⟨p, hprime, (Nat.le_ceil x).trans (by exact_mod_cast hp)⟩

/-- The least prime at least a prescribed real threshold. -/
def firstPrimeAbove (x : ℝ) : ℕ := Nat.find (prime_above_exists x)

private theorem firstPrimeAbove_spec (x : ℝ) :
    (firstPrimeAbove x).Prime ∧ x ≤ (firstPrimeAbove x : ℝ) := Nat.find_spec (prime_above_exists x)

/-- The first prime at or above exp(s) approximates s on the logarithmic scale. -/
theorem prime_log_mesh_tendsto :
    Tendsto (fun s : ℝ => Real.log (firstPrimeAbove (Real.exp s)) - s) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with s
    have h := Real.log_le_log (Real.exp_pos s) (firstPrimeAbove_spec (Real.exp s)).2
    rw [Real.log_exp] at h
    linarith
  · intro δ hδ
    have hε : 0 < Real.exp δ - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hδ)
    have h := Real.tendsto_exp_atTop.eventually
      (RiemannResearch.NumberTheory.PrimeNumberTheorem.prime_between hε)
    filter_upwards [h] with s hs
    obtain ⟨p, hp, hp₁, hp₂⟩ := hs
    have hmin : firstPrimeAbove (Real.exp s) ≤ p :=
      Nat.find_min' (prime_above_exists _) ⟨hp, hp₁.le⟩
    have hlt : (firstPrimeAbove (Real.exp s) : ℝ) < Real.exp (s + δ) := by
      apply (show (firstPrimeAbove (Real.exp s) : ℝ) ≤ p by exact_mod_cast hmin).trans_lt
      calc
        (p : ℝ) < (1 + (Real.exp δ - 1)) * Real.exp s := hp₂
        _ = Real.exp (s + δ) := by rw [Real.exp_add]; ring
    have hlog := Real.log_lt_log ((Real.exp_pos s).trans_le (firstPrimeAbove_spec _).2) hlt
    rw [Real.log_exp] at hlog
    linarith

/-- Every dictionary containing the logarithms of all primes has each
actual ordinate indicator in its algebraic finite-feature span. -/
theorem fiberVector_mem_span_of_all_prime_logs (q : ℕ → ℝ)
    (hq : ∀ p : ℕ, p.Prime → ∃ k : ℕ, q k = Real.log p) (i : Site) :
    fiberVector i ∈ Submodule.span ℝ (Set.range (feature q)) := by
  choose k hk using fun s : ℝ => hq (firstPrimeAbove (Real.exp s)) (firstPrimeAbove_spec _).1
  apply fiberVector_mem_span_of_frequency_mesh q k _ i
  simpa only [hk] using prime_log_mesh_tendsto

/-- Prime frequencies alone give the same complete limiting DPP as all log integers. -/
theorem limitingLaw_eq_logarithmic_of_all_prime_logs (q : ℕ → ℝ)
    (hq : ∀ p : ℕ, p.Prime → ∃ k : ℕ, q k = Real.log p) :
    limitingLaw q = limitingLaw (fun k => Real.log ((k : ℝ) + 1)) :=
  limitingLaw_eq_logarithmic_of_fiber_mem q (fun i => (Submodule.le_topologicalClosure _)
    (fiberVector_mem_span_of_all_prime_logs q hq i))

/-- Frequencies consisting exclusively of the logarithms of successive primes. -/
def primeFrequencies (k : ℕ) : ℝ := Real.log (Nat.nth Nat.Prime k)

private theorem primeFrequencies_cover (p : ℕ) (hp : p.Prime) :
    ∃ k : ℕ, primeFrequencies k = Real.log p := by
  obtain ⟨k, hk⟩ := Nat.subset_range_nth (p := Nat.Prime) hp
  exact ⟨k, congrArg (fun n : ℕ => Real.log (n : ℝ)) hk⟩

theorem primeFrequencies_limitingLaw :
    limitingLaw primeFrequencies = limitingLaw (fun k => Real.log ((k : ℝ) + 1)) :=
  limitingLaw_eq_logarithmic_of_all_prime_logs _ primeFrequencies_cover

/-- The explicit prime-only inclusion kernel on all actual multiplicity labels. -/
theorem primeFrequencies_limitingKernel (i j : Site) :
    limitingKernel primeFrequencies i j =
      if ordinate j = ordinate i then ((ordinateFiber i).card : ℝ)⁻¹ else 0 := by
  rw [limitingKernel_eq_logarithmic_of_fiber_mem primeFrequencies (fun a =>
    (Submodule.le_topologicalClosure _) (fiberVector_mem_span_of_all_prime_logs _
      primeFrequencies_cover a))]
  exact logarithmic_limitingKernel i j

/-- Every fixed finite marginal of the pure-prime feature prefix eventually
equals the full log-integer limiting marginal, including mixed patterns. -/
theorem primeFrequencies_finite_marginal_eventually_eq (I : Finset Site) :
    ∀ᶠ n : ℕ in atTop, (finiteLaw primeFrequencies n).map I.restrict =
      (limitingLaw (fun k => Real.log ((k : ℝ) + 1))).map I.restrict := by
  rw [← primeFrequencies_limitingLaw]
  exact finite_marginal_eventually_eq_of_fiber_span _ I
    (fun i _ => fiberVector_mem_span_of_all_prime_logs _ primeFrequencies_cover i)

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

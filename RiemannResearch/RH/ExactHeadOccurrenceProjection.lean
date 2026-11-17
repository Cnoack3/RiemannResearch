import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.Analysis.FiniteWeightedNormal
import RiemannResearch.Analysis.FiniteWeightedSpan

/-!
# Exact occurrence relaxation and atom-reuse energy

Source: Christian Noack, `sdf_modified.pdf`, 21 July 2026, section 14.9,
equations (122)--(127), Drive file 1RWvDfQdERH8uDRS9PwGhK2eOKJxyfvO6.
The finite projection statements hold for every natural period and cutoff,
without squarefreeness, independence, or an asymptotic input. The target is
the repository's coprime count minus one, so the initial head is retained.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedNormal
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer

def freePositions (P x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (P - 1)).filter (fun n => x < Nat.gcd n P)

def step (n r : ℕ) : ℝ := if n ≤ r then 1 else 0

def fit (P x : ℕ) (c : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ n ∈ freePositions P x, c n * step n r

theorem atom_eq_sum_steps (P x d r : ℕ) (hxd : x < d) (hr : r < P) :
    atom P d r = ∑ n ∈ freePositions P x,
      (if Nat.gcd n P = d then 1 else 0) * step n r := by
  classical
  calc
    _ = ∑ n ∈ Finset.Icc 1 r,
        (if Nat.gcd n P = d then 1 else 0) * step n r := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [step, (Finset.mem_Icc.mp hn).2]
    _ = ∑ n ∈ Finset.Icc 1 (P - 1),
        (if Nat.gcd n P = d then 1 else 0) * step n r := by
      apply Finset.sum_subset
      · intro n hn
        obtain ⟨hn1,hnr⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨hn1, by omega⟩
      · intro n hn hnot
        have hnr : ¬ n ≤ r := by
          intro h
          exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,h⟩)
        simp [step, hnr]
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro n hn hnot
      have hg : Nat.gcd n P ≠ d := by
        intro he
        exact hnot (Finset.mem_filter.mpr ⟨hn, he ▸ hxd⟩)
      simp [hg]

theorem lift_synthesis (P x : ℕ) (u : ℕ → ℝ) (r : ℕ) (hr : r < P) :
    fit P x (fun n => u (Nat.gcd n P)) r =
      synthesis P (upperDivisors P x) u r := by
  classical
  symm
  unfold synthesis
  calc
    _ = ∑ d ∈ upperDivisors P x, ∑ n ∈ freePositions P x,
        u d * ((if Nat.gcd n P = d then 1 else 0) * step n r) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [atom_eq_sum_steps P x d r (Finset.mem_filter.mp hd).2 hr,
        Finset.mul_sum]
    _ = ∑ n ∈ freePositions P x, ∑ d ∈ upperDivisors P x,
        u d * ((if Nat.gcd n P = d then 1 else 0) * step n r) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hP : P ≠ 0 := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1)
        omega
      have hg : Nat.gcd n P ∈ upperDivisors P x :=
        Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n P,hP⟩,
          (Finset.mem_filter.mp hn).2⟩
      simp [mul_ite, ite_mul, hg]

def occurrenceCoefficients (P x : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_normal_finset (Finset.Icc 1 (P - 1))
    (freePositions P x) (progressionWeight P)
    (fun r _ => progressionWeight_nonneg P r) step (target P))

def occurrenceResidual (P x r : ℕ) : ℝ :=
  target P r - fit P x (occurrenceCoefficients P x) r

def occurrenceEnergy (P x : ℕ) : ℝ :=
  energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (occurrenceResidual P x)

def reuseResidual (P x : ℕ) : ℕ → ℝ :=
  atomResidual P x - occurrenceResidual P x

def reuseEnergy (P x : ℕ) : ℝ :=
  energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (reuseResidual P x)

theorem occurrence_normal_step (P x n : ℕ) (hn : n ∈ freePositions P x) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (step n) = 0 := by
  have h := (Classical.choose_spec (exists_normal_finset
    (Finset.Icc 1 (P - 1)) (freePositions P x) (progressionWeight P)
    (fun r _ => progressionWeight_nonneg P r) step (target P))).2 n hn
  simpa only [pairing, occurrenceResidual, occurrenceCoefficients, fit,
    mul_comm, mul_left_comm, mul_assoc] using h

theorem occurrence_normal_fit (P x : ℕ) (c : ℕ → ℝ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (fit P x c) = 0 := by
  calc
    _ = ∑ n ∈ freePositions P x, c n *
        pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
          (occurrenceResidual P x) (step n) := by
      unfold pairing fit
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [occurrence_normal_step P x n hn, mul_zero]

theorem occurrence_normal_synthesis (P x : ℕ) (u : ℕ → ℝ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (synthesis P (upperDivisors P x) u) = 0 := by
  rw [← occurrence_normal_fit P x (fun n => u (Nat.gcd n P))]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lift_synthesis P x u r (by have := Finset.mem_Icc.mp hr; omega)]

theorem occurrence_normal_reuse (P x : ℕ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (occurrenceResidual P x) (reuseResidual P x) = 0 := by
  have heq : reuseResidual P x = fun r =>
      fit P x (occurrenceCoefficients P x) r -
        synthesis P (upperDivisors P x) (atomNormalCoefficients P x) r := by
    funext r
    simp [reuseResidual, atomResidual, occurrenceResidual, synthesis]
  rw [heq]
  change (∑ r ∈ Finset.Icc 1 (P - 1), progressionWeight P r *
    occurrenceResidual P x r *
      (fit P x (occurrenceCoefficients P x) r -
        synthesis P (upperDivisors P x) (atomNormalCoefficients P x) r)) = 0
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((occurrence_normal_fit P x _).trans
    (occurrence_normal_synthesis P x _).symm)

/-- The actual optimized error splits exactly; every signed term is retained. -/
theorem atomEnergy_eq_occurrence_add_reuse (P x : ℕ) :
    atomEnergy P x = occurrenceEnergy P x + reuseEnergy P x := by
  have heq : atomResidual P x = occurrenceResidual P x + reuseResidual P x := by
    unfold reuseResidual
    abel
  unfold atomEnergy occurrenceEnergy reuseEnergy
  rw [heq, energy_add_exact, occurrence_normal_reuse, mul_zero, add_zero]

theorem occurrenceEnergy_nonneg (P x : ℕ) : 0 ≤ occurrenceEnergy P x :=
  energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)

theorem reuseEnergy_nonneg (P x : ℕ) : 0 ≤ reuseEnergy P x :=
  energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)

theorem occurrenceEnergy_le_atomEnergy (P x : ℕ) :
    occurrenceEnergy P x ≤ atomEnergy P x := by
  rw [atomEnergy_eq_occurrence_add_reuse]
  exact le_add_of_nonneg_right (reuseEnergy_nonneg P x)

theorem synthesis_mem_upperSpan (P x : ℕ) (u : ℕ → ℝ) :
    synthesis P (upperDivisors P x) u ∈ upperSpan P x (atom P) := by
  have heq : synthesis P (upperDivisors P x) u =
      ∑ d ∈ upperDivisors P x, u d • atom P d := by
    funext r
    simp [synthesis]
  rw [heq]
  exact Submodule.sum_mem _ (fun d hd =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨d,hd,rfl⟩))

theorem atom_normal_synthesis (P x : ℕ) (u : ℕ → ℝ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (atomResidual P x) (synthesis P (upperDivisors P x) u) = 0 :=
  atomResidual_normal P x _ (synthesis_mem_upperSpan P x u)

theorem reuse_normal_synthesis (P x : ℕ) (u : ℕ → ℝ) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (reuseResidual P x) (synthesis P (upperDivisors P x) u) = 0 := by
  have heq : pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (reuseResidual P x) (synthesis P (upperDivisors P x) u) =
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (atomResidual P x) (synthesis P (upperDivisors P x) u) -
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (occurrenceResidual P x) (synthesis P (upperDivisors P x) u) := by
    simp [pairing, reuseResidual, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [heq, atom_normal_synthesis, occurrence_normal_synthesis, sub_self]

/-- Every trial atom vector has an exact nonnegative excess over the reuse minimum. -/
theorem reuse_trial_identity (P x : ℕ) (u : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) =
      reuseEnergy P x + energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) -
          synthesis P (upperDivisors P x) u) := by
  have heq : fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u =
      reuseResidual P x +
        (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) -
          synthesis P (upperDivisors P x) u) := by
    funext r
    simp [reuseResidual, atomResidual, occurrenceResidual, synthesis]
  have hz : pairing (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (reuseResidual P x)
        (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) -
          synthesis P (upperDivisors P x) u) = 0 := by
    change (∑ r ∈ Finset.Icc 1 (P - 1), progressionWeight P r * reuseResidual P x r *
      (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) r -
        synthesis P (upperDivisors P x) u r)) = 0
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((reuse_normal_synthesis P x _).trans
      (reuse_normal_synthesis P x _).symm)
  rw [heq, energy_add_exact, hz, mul_zero, add_zero]
  rfl

theorem reuseEnergy_le_trial (P x : ℕ) (u : ℕ → ℝ) :
    reuseEnergy P x ≤ energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
      (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) := by
  rw [reuse_trial_identity]
  exact le_add_of_nonneg_right
    (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r))

def greenKernel (P n m : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (P - 1), progressionWeight P r * step n r * step m r

/-- Exact signed Green quadratic form for arbitrary occurrence coefficients. -/
theorem fit_energy_eq_green (P x : ℕ) (c : ℕ → ℝ) :
    energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (fit P x c) =
      ∑ n ∈ freePositions P x, ∑ m ∈ freePositions P x,
        c n * c m * greenKernel P n m := by
  unfold energy fit greenKernel
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Equation (127), including the exact excess term for every trial coefficient vector. -/
theorem reuse_green_identity (P x : ℕ) (u : ℕ → ℝ) :
    (∑ n ∈ freePositions P x, ∑ m ∈ freePositions P x,
      (occurrenceCoefficients P x n - u (Nat.gcd n P)) *
      (occurrenceCoefficients P x m - u (Nat.gcd m P)) * greenKernel P n m) =
      reuseEnergy P x + energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) -
          synthesis P (upperDivisors P x) u) := by
  rw [← fit_energy_eq_green]
  rw [← reuse_trial_identity P x u]
  apply Finset.sum_congr rfl
  intro r hr
  have hfit : fit P x (fun n => occurrenceCoefficients P x n - u (Nat.gcd n P)) r =
      fit P x (occurrenceCoefficients P x) r - synthesis P (upperDivisors P x) u r := by
    rw [← lift_synthesis P x u r (by have := Finset.mem_Icc.mp hr; omega)]
    simp [fit, sub_mul, Finset.sum_sub_distrib]
  simp only [Pi.sub_apply, hfit]

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection

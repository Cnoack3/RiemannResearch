import RiemannResearch.RH.ExactHeadAtomCoercivity
import RiemannResearch.Analysis.FiniteNormalDefect
import Mathlib.Tactic

/-!
# Complete a posteriori energy bounds for the actual atom optimizer
For any trial coefficients, the excess energy is exactly a normal-defect
pairing and is at most 4(sum d^2)(sum defect_d^2). No inverse or numerical
condition-number premise is used. All complete progression weights are retained.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open ExactHeadAtomCoercivity

def trialResidual (P x : ℕ) (u : ℕ → ℝ) (r : ℕ) : ℝ :=
  target P r - synthesis P (properUpperDivisors P x) u r

def trialEnergy (P x : ℕ) (u : ℕ → ℝ) : ℝ :=
  energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (trialResidual P x u)

def normalDefect (P x : ℕ) (u : ℕ → ℝ) (d : ℕ) : ℝ :=
  pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (trialResidual P x u) (atom P d)

theorem trial_decomposition_on (P x : ℕ) (u : ℕ → ℝ) (r : ℕ) (hr : r < P) :
    trialResidual P x u r = atomResidual P x r +
      synthesis P (properUpperDivisors P x) (fun d => atomNormalCoefficients P x d - u d) r := by
  unfold trialResidual atomResidual
  change target P r - synthesis P (properUpperDivisors P x) u r =
    target P r - synthesis P (upperDivisors P x) (atomNormalCoefficients P x) r + _
  rw [synthesis_upper_eq_proper P x (atomNormalCoefficients P x) r hr]
  unfold synthesis
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

private theorem normal_proper (P x : ℕ) (d : ℕ) (hd : d ∈ properUpperDivisors P x) :
    pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) (atom P d) = 0 :=
  atomResidual_normal P x (atom P d)
    (Submodule.subset_span ⟨d,(Finset.mem_filter.mp hd).1,rfl⟩)

theorem trial_energy_split (P x : ℕ) (u : ℕ → ℝ) :
    trialEnergy P x u = atomEnergy P x +
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (synthesis P (properUpperDivisors P x) (fun d => atomNormalCoefficients P x d - u d)) := by
  calc
    trialEnergy P x u = energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
        (atomResidual P x +
          synthesis P (properUpperDivisors P x) (fun d => atomNormalCoefficients P x d - u d)) := by
      unfold trialEnergy energy
      apply Finset.sum_congr rfl
      intro r hr
      rw [trial_decomposition_on P x u r (by
        have hh := Finset.mem_Icc.mp hr; omega)]
      rfl
    _ = _ := normal_synthesis_completion _ _ _ _ _ _ (normal_proper P x)

theorem trial_energy_gap_eq_normal_defect (P x : ℕ) (u : ℕ → ℝ) :
    trialEnergy P x u - atomEnergy P x =
      ∑ d ∈ properUpperDivisors P x,
        (atomNormalCoefficients P x d - u d) * normalDefect P x u d := by
  rw [trial_energy_split, add_sub_cancel_left]
  unfold synthesis
  rw [normal_defect_energy_identity _ _ _ _ _ _ (normal_proper P x)]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  unfold pairing normalDefect
  apply Finset.sum_congr rfl
  intro r hr
  rw [trial_decomposition_on P x u r (by
    have hh := Finset.mem_Icc.mp hr; omega)]
  rfl

/-- An inverse-free, fully actual enclosure for the optimized Green energy. -/
theorem trial_energy_enclosure (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    atomEnergy P x ≤ trialEnergy P x u ∧
      trialEnergy P x u ≤ atomEnergy P x +
        (4 * ∑ d ∈ properUpperDivisors P x, (d : ℝ) ^ 2) *
          ∑ d ∈ properUpperDivisors P x, normalDefect P x u d ^ 2 := by
  let c : ℕ → ℝ := fun d => atomNormalCoefficients P x d - u d
  let E := energy (Finset.Icc 1 (P - 1)) (progressionWeight P)
    (synthesis P (properUpperDivisors P x) c)
  have hs : trialEnergy P x u = atomEnergy P x + E := trial_energy_split P x u
  have hn : 0 ≤ E := energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)
  have hd : E = ∑ d ∈ properUpperDivisors P x, c d * normalDefect P x u d := by
    have hh := trial_energy_gap_eq_normal_defect P x u
    rw [hs,add_sub_cancel_left] at hh
    exact hh
  have hc := coefficient_energy_bound P hP (properUpperDivisors P x) c
    (properUpperDivisors_properties P x)
  have hb := energy_le_of_dual_coercivity (properUpperDivisors P x) c
    (normalDefect P x u) E (4 * ∑ d ∈ properUpperDivisors P x, (d : ℝ) ^ 2)
    hn (by positivity) hd hc
  constructor <;> linarith

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer

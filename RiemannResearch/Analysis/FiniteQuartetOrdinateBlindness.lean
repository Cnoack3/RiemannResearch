/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConjugatePairHankel
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
A finite spectral obstruction to deducing horizontal-energy vanishing from
ordinate data alone. Lists retain multiplicity: the critical-line comparison
has each of its two nodes twice; the displaced quartet has four atoms.

This is an artificial spectrum, not a list of actual zeta zeros. In particular,
no prime-side explicit formula is asserted for either spectrum. The theorem
does not refute RH or an arithmetic route to it. It separates exactly the
information preserved by ordinate observables from the horizontal obstruction.

Source: independently developed finite algebra auditing the ordinate-based
argument in the user-provided `Ordinate_Harmonic_Theory_20261010(1).md`.
-/

noncomputable section

namespace RiemannResearch.Analysis.FiniteQuartetOrdinateBlindness

/-- Both horizontal partners and both ordinate signs, with multiplicity. -/
def quartet (d g : ℝ) : List ℂ :=
  [⟨1 / 2 + d, g⟩, ⟨1 / 2 - d, g⟩,
   ⟨1 / 2 + d, -g⟩, ⟨1 / 2 - d, -g⟩]

/-- The same fourth-order weight used for the actual-zero obstruction. -/
def atomEnergy (z : ℂ) : ℝ :=
  (z.re - 1 / 2) ^ 2 / (1 + z.im ^ 2) ^ 2

/-- Repeated list entries encode analytic multiplicity in this finite model. -/
def energy (s : List ℂ) : ℝ := (s.map atomEnergy).sum

/-- Every ordinate-only observable, including exact cutoff counts. -/
def ordinateObservable (f : ℝ → ℝ) (s : List ℂ) : ℝ :=
  (s.map (fun z => f z.im)).sum

/-- The exact tail, without a limiting or asymptotic convention. -/
noncomputable def energyTail (T : ℝ) (s : List ℂ) : ℝ :=
  (s.map (fun z => if T < |z.im| then atomEnergy z else 0)).sum

theorem quartet_ordinates (d g : ℝ) :
    (quartet d g).map Complex.im = (quartet 0 g).map Complex.im := by
  simp [quartet]

theorem ordinateObservable_quartet (f : ℝ → ℝ) (d g : ℝ) :
    ordinateObservable f (quartet d g) =
      ordinateObservable f (quartet 0 g) := by
  simp [ordinateObservable, quartet]

theorem energy_quartet (d g : ℝ) :
    energy (quartet d g) = 4 * d ^ 2 / (1 + g ^ 2) ^ 2 := by
  simp only [energy, quartet, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, atomEnergy]
  ring

theorem energy_line_quartet (g : ℝ) : energy (quartet 0 g) = 0 := by
  rw [energy_quartet]
  simp

theorem energy_quartet_pos {d : ℝ} (hd : d ≠ 0) (g : ℝ) :
    0 < energy (quartet d g) := by
  rw [energy_quartet]
  have hdpos := sq_pos_of_ne_zero hd
  positivity

theorem quartet_in_strip {d g : ℝ} (hd : |d| < 1 / 2) :
    ∀ z ∈ quartet d g, 0 < z.re ∧ z.re < 1 := by
  have hbounds := abs_lt.mp hd
  intro z hz
  simp only [quartet, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    dsimp only <;> constructor <;> linarith

theorem energyTail_quartet_zero {T g : ℝ} (hg : 0 ≤ g) (hT : g ≤ T)
    (d : ℝ) : energyTail T (quartet d g) = 0 := by
  have h : ¬ T < g := not_lt.mpr hT
  simp [energyTail, quartet, abs_of_nonneg hg, abs_neg, h]

/-- Even an exactly zero tail and identical ordinate data leave a positive core. -/
theorem same_ordinates_positive_energy_zero_tail
    {d g T : ℝ} (hd : d ≠ 0) (hg : 0 ≤ g) (hT : g ≤ T) :
    (∀ f : ℝ → ℝ, ordinateObservable f (quartet d g) =
      ordinateObservable f (quartet 0 g)) ∧
    energy (quartet 0 g) = 0 ∧
    0 < energy (quartet d g) ∧ energyTail T (quartet d g) = 0 :=
  ⟨fun f => ordinateObservable_quartet f d g, energy_line_quartet g,
    energy_quartet_pos hd g, energyTail_quartet_zero hg hT d⟩

/-- A concrete open-strip example at height 15; no actual-zero claim is made. -/
theorem concrete_quartet :
    (∀ z ∈ quartet (1 / 4) 15, 0 < z.re ∧ z.re < 1) ∧
    energy (quartet (1 / 4) 15) = 1 / 204304 ∧
    energyTail 15 (quartet (1 / 4) 15) = 0 := by
  refine ⟨quartet_in_strip (by norm_num), ?_, ?_⟩
  · rw [energy_quartet]
    norm_num
  · exact energyTail_quartet_zero (by norm_num) le_rfl _

/-- Rotated centered coordinates; its square is the heat-derivative node. -/
def rotatedNode (d g : ℝ) : ℂ := ⟨g, -d⟩

/-- The two squared nodes aggregate all four atoms of the isolated quartet. -/
def heatMoment (a d g : ℝ) (k : ℕ) : ℝ :=
  ConjugatePairHankel.pairMoment
    (2 * Complex.exp (-(a : ℂ) * rotatedNode d g ^ 2))
    (rotatedNode d g ^ 2) k

/-- Off-line displacement is detected by an isolated heat Hankel determinant. -/
theorem heatMoment_determinant_neg (a : ℝ) {d g : ℝ}
    (hd : d ≠ 0) (hg : g ≠ 0) :
    heatMoment a d g 0 * heatMoment a d g 2 -
      heatMoment a d g 1 ^ 2 < 0 := by
  have hv : 2 * Complex.exp (-(a : ℂ) * rotatedNode d g ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
  have him : (rotatedNode d g ^ 2).im = -2 * g * d := by
    simp only [rotatedNode, pow_two, Complex.mul_im]
    ring
  have hz : (rotatedNode d g ^ 2).im ≠ 0 := by
    rw [him]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hg) hd
  exact ConjugatePairHankel.pairMoment_determinant_neg hv hz

/-- A full infinite background needs separate control to retain this direction. -/
theorem heatMoment_negative_witness (a : ℝ) {d g : ℝ}
    (hd : d ≠ 0) (hg : g ≠ 0) :
    ∃ x y : ℝ,
      heatMoment a d g 0 * x ^ 2 +
        2 * heatMoment a d g 1 * x * y +
        heatMoment a d g 2 * y ^ 2 < 0 :=
  HankelMomentPositivity.exists_negative_direction_of_det_neg
    (heatMoment_determinant_neg a hd hg)

end RiemannResearch.Analysis.FiniteQuartetOrdinateBlindness

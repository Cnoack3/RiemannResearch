import RiemannResearch.RH.ExactHeadPhysicalReturn
import RiemannResearch.RH.ExactHeadAtomReturnMoments
import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.ExactHeadGreenProfile
import RiemannResearch.Analysis.FiniteProfileEnergy
import RiemannResearch.Analysis.FiniteWeightedSpan
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Signed three-label moment bounds with complete return geometry

Source: the user-provided audited A1--A2 manuscript, sections 22--23,
https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view,
for the signed numerator and physical-window identification.
The finite quantitative consequences here are derived from the repository's
exact atom normality, physical return, and Gram remainder identities.
No bound on the actual optimizer energy or inverse tail Gram is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadSignedMomentBounds
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.ExactHeadAtomReturnMoments
open RiemannResearch.RH.ExactHeadPhysicalReturn
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer

def tripleProfile (P x p q r : ℕ) : ℕ → ℝ :=
  (p * ((r : ℝ) - q)) • upperDivisorSignal P x p -
  (q * ((r : ℝ) - p)) • upperDivisorSignal P x q +
  (r * ((q : ℝ) - p)) • upperDivisorSignal P x r

def tripleMoment (P x Y p q r : ℕ) (w h : ℕ → ℝ) : ℝ :=
  (p : ℝ) * ((r : ℝ) - q) * activatedMoment P x Y p w h -
  (q : ℝ) * ((r : ℝ) - p) * activatedMoment P x Y q w h +
  (r : ℝ) * ((q : ℝ) - p) * activatedMoment P x Y r w h

def floorTriple (p q r n : ℕ) : ℝ :=
  (p : ℝ) * ((r : ℝ) - q) * (grid p n - 1) -
  (q : ℝ) * ((r : ℝ) - p) * (grid q n - 1) +
  (r : ℝ) * ((q : ℝ) - p) * (grid r n - 1)

theorem tripleProfile_mem (P x p q r : ℕ) :
    tripleProfile P x p q r ∈ upperSpan P x (atom P) := by
  exact Submodule.add_mem _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ (upperDivisorSignal_mem P x p))
    (Submodule.smul_mem _ _ (upperDivisorSignal_mem P x q)))
    (Submodule.smul_mem _ _ (upperDivisorSignal_mem P x r))

theorem tripleMoment_eq_prefix (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h =
      pairing (Finset.Icc 1 Y) w h (tripleProfile P x p q r) := by
  unfold tripleMoment
  rw [← upperDivisorSignal_prefix P x Y p w h,
    ← upperDivisorSignal_prefix P x Y q w h,
    ← upperDivisorSignal_prefix P x Y r w h]
  unfold tripleProfile pairing
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem tripleMoment_eq_physical_pairing (P x Y p q r : ℕ) (w h : ℕ → ℝ) :
    tripleMoment P x Y p q r w h =
      pairing (Finset.Icc (x + 1) Y) w h (tripleProfile P x p q r) := by
  unfold tripleMoment
  rw [← physical_pairing_upper P x Y p w h,
    ← physical_pairing_upper P x Y q w h,
    ← physical_pairing_upper P x Y r w h]
  unfold tripleProfile pairing
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Both the linear position term and the constant term cancel exactly. -/
theorem floorTriple_eq_residues (p q r n : ℕ) :
    floorTriple p q r n =
      -((r : ℝ) - q) * (n % p : ℕ) +
       ((r : ℝ) - p) * (n % q : ℕ) -
       ((q : ℝ) - p) * (n % r : ℕ) := by
  have hp := grid_residue_identity p n
  have hq := grid_residue_identity q n
  have hr := grid_residue_identity r n
  unfold floorTriple
  nlinarith only [
    congrArg (fun z : ℝ => ((r : ℝ) - q)*z) hp,
    congrArg (fun z : ℝ => ((r : ℝ) - p)*z) hq,
    congrArg (fun z : ℝ => ((q : ℝ) - p)*z) hr]

/-- A position-independent bound obtained after signed cancellation.
No primality or coprimality is needed for this arithmetic estimate. -/
theorem abs_floorTriple_le (p q r n : ℕ) (hp : 0 < p)
    (hpq : p ≤ q) (hqr : q ≤ r) :
    |floorTriple p q r n| ≤ ((q : ℝ) - 1) * ((r : ℝ) - p) := by
  have hq : 0 < q := hp.trans_le hpq
  have hr : 0 < r := hq.trans_le hqr
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hqr' : (q : ℝ) ≤ r := by exact_mod_cast hqr
  have hpr' : (p : ℝ) ≤ r := hpq'.trans hqr'
  have hmp : ((n % p : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
    have hh : n % p + 1 ≤ p := Nat.mod_lt n hp
    have hh' : ((n % p : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hh
    linarith
  have hmq : ((n % q : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
    have hh : n % q + 1 ≤ q := Nat.mod_lt n hq
    have hh' : ((n % q : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast hh
    linarith
  have hmr : ((n % r : ℕ) : ℝ) ≤ (r : ℝ) - 1 := by
    have hh : n % r + 1 ≤ r := Nat.mod_lt n hr
    have hh' : ((n % r : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast hh
    linarith
  have lp := mul_nonneg (sub_nonneg.mpr hqr') (Nat.cast_nonneg (n % p) : (0:ℝ) ≤ _)
  have lq := mul_nonneg (sub_nonneg.mpr hpr') (Nat.cast_nonneg (n % q) : (0:ℝ) ≤ _)
  have lr := mul_nonneg (sub_nonneg.mpr hpq') (Nat.cast_nonneg (n % r) : (0:ℝ) ≤ _)
  have up := mul_le_mul_of_nonneg_left hmp (sub_nonneg.mpr hqr')
  have uq := mul_le_mul_of_nonneg_left hmq (sub_nonneg.mpr hpr')
  have ur := mul_le_mul_of_nonneg_left hmr (sub_nonneg.mpr hpq')
  rw [floorTriple_eq_residues, abs_le]
  constructor <;> nlinarith

theorem tripleProfile_eq_floorTriple (P x Y p q r n : ℕ)
    (hP : P ≠ 0) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≤ q) (hqr : q ≤ r) (hrx : r ≤ x) (hhalf : x < 2 * p)
    (hcover : ∀ l, Nat.Prime l → l ≤ r → l ∣ P)
    (hY : Y < p * p) (hn : n ∈ Finset.Icc (x + 1) Y) :
    tripleProfile P x p q r n = floorTriple p q r n := by
  have hxn : x < n := (Finset.mem_Icc.mp hn).1
  have hnY := (Finset.mem_Icc.mp hn).2
  have hpr := hpq.trans hqr
  simp only [tripleProfile, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [upperDivisorSignal_eq_grid_sub_one P x p n hP hp
    (fun l hl hlp => hcover l hl (hlp.trans hpr)) (hpr.trans hrx) hhalf hxn
    (hnY.trans_lt hY)]
  rw [upperDivisorSignal_eq_grid_sub_one P x q n hP hq
    (fun l hl hlq => hcover l hl (hlq.trans hqr)) (hqr.trans hrx)
    (by omega) hxn (by nlinarith)]
  rw [upperDivisorSignal_eq_grid_sub_one P x r n hP hr hcover hrx
    (by omega) hxn (by nlinarith)]
  rfl

/-- Prefix Cauchy--Schwarz is applied to the signed profile as a whole. -/
theorem tripleMoment_sq_le_prefix (P x Y p q r : ℕ) (w h : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Icc (x + 1) Y, 0 ≤ w n) :
    tripleMoment P x Y p q r w h ^ 2 ≤
      energy (Finset.Icc (x + 1) Y) w h *
      energy (Finset.Icc (x + 1) Y) w (tripleProfile P x p q r) := by
  rw [tripleMoment_eq_physical_pairing]
  exact pairing_sq_le _ _ _ _ hw

/-- Explicit finite physical-window estimate; the signal energy remains present. -/
theorem tripleMoment_sq_le_window_mass (P x Y p q r : ℕ) (w h : ℕ → ℝ)
    (hP : P ≠ 0) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≤ q) (hqr : q ≤ r) (hrx : r ≤ x) (hhalf : x < 2 * p)
    (hcover : ∀ l, Nat.Prime l → l ≤ r → l ∣ P)
    (hY : Y < p * p) (hw : ∀ n ∈ Finset.Icc (x + 1) Y, 0 ≤ w n) :
    tripleMoment P x Y p q r w h ^ 2 ≤
      energy (Finset.Icc (x + 1) Y) w h *
      mass (Finset.Icc (x + 1) Y) w * (((q : ℝ) - 1) * ((r : ℝ) - p))^2 := by
  have he : energy (Finset.Icc (x + 1) Y) w (tripleProfile P x p q r) ≤
      mass (Finset.Icc (x + 1) Y) w * (((q : ℝ) - 1) * ((r : ℝ) - p))^2 := by
    unfold energy mass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (hw n hn)
    rw [tripleProfile_eq_floorTriple P x Y p q r n hP hp hq hr hpq hqr hrx
      hhalf hcover hY hn]
    have h := abs_floorTriple_le p q r n hp.pos hpq hqr
    have hs := mul_self_le_mul_self (abs_nonneg (floorTriple p q r n)) h
    nlinarith [sq_abs (floorTriple p q r n)]
  exact (tripleMoment_sq_le_prefix P x Y p q r w h hw).trans
    (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left he (energy_nonneg _ _ _ hw))

theorem atomResidual_tripleMoment_eq_tail (P x Y p q r : ℕ) (hYP : Y < P) :
    tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x) =
      -pairing (Finset.Icc (Y + 1) (P - 1)) (progressionWeight P)
        (atomResidual P x) (tripleProfile P x p q r) := by
  rw [tripleMoment_eq_prefix]
  have hnormal := atomResidual_normal P x _ (tripleProfile_mem P x p q r)
  have hd : Disjoint (Finset.Icc 1 Y) (Finset.Icc (Y + 1) (P - 1)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Icc] at hn hm
    omega
  have hu : Finset.Icc 1 Y ∪ Finset.Icc (Y + 1) (P - 1) = Finset.Icc 1 (P - 1) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hs : pairing (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x)
      (tripleProfile P x p q r) +
      pairing (Finset.Icc (Y + 1) (P - 1)) (progressionWeight P) (atomResidual P x)
      (tripleProfile P x p q r) = 0 := by
    unfold pairing
    rw [← Finset.sum_union hd, hu]
    exact hnormal
  linarith

/-- The actual optimizer bound retains q = atomEnergy explicitly. -/
theorem atomResidual_tripleMoment_sq_le_window_mass (P x Y p q r : ℕ)
    (hP : P ≠ 0) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≤ q) (hqr : q ≤ r) (hrx : r ≤ x) (hhalf : x < 2 * p)
    (hcover : ∀ l, Nat.Prime l → l ≤ r → l ∣ P)
    (hY : Y < p * p) (hYP : Y < P) :
    tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x) ^ 2 ≤
      atomEnergy P x * mass (Finset.Icc (x + 1) Y) (progressionWeight P) *
        (((q : ℝ) - 1) * ((r : ℝ) - p)) ^ 2 := by
  have he : energy (Finset.Icc (x + 1) Y) (progressionWeight P) (atomResidual P x) ≤
      atomEnergy P x := by
    unfold atomEnergy energy
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro n hn hnot
      exact mul_nonneg (progressionWeight_nonneg P n) (sq_nonneg _)
  have hm : 0 ≤ mass (Finset.Icc (x + 1) Y) (progressionWeight P) :=
    Finset.sum_nonneg (fun n _ => progressionWeight_nonneg P n)
  exact (tripleMoment_sq_le_window_mass P x Y p q r (progressionWeight P)
    (atomResidual P x) hP hp hq hr hpq hqr hrx hhalf hcover hY
    (fun n _ => progressionWeight_nonneg P n)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hm) (sq_nonneg _))

/-- The physical determinant is the signed activated moment in the safe window. -/
theorem physical_triple_eq_moment (P x Y p q r : ℕ) (w h : ℕ → ℝ)
    (hP : P ≠ 0) (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hpq : p ≤ q) (hqr : q ≤ r) (hrx : r ≤ x) (hhalf : x < 2 * p)
    (hcover : ∀ l, Nat.Prime l → l ≤ r → l ∣ P) (hY : Y < p * p) :
    ((r : ℝ) - q) * physicalSignal x Y p w h -
      ((r : ℝ) - p) * physicalSignal x Y q w h +
      ((q : ℝ) - p) * physicalSignal x Y r w h =
        tripleMoment P x Y p q r w h := by
  have hpr := hpq.trans hqr
  rw [physicalSignal_eq_activatedMoment P x Y p w h hP hp
    (fun l hl hlp => hcover l hl (hlp.trans hpr)) (hpr.trans hrx) hhalf hY]
  rw [physicalSignal_eq_activatedMoment P x Y q w h hP hq
    (fun l hl hlq => hcover l hl (hlq.trans hqr)) (hqr.trans hrx)
    (by omega) (by nlinarith)]
  rw [physicalSignal_eq_activatedMoment P x Y r w h hP hr hcover hrx
    (by omega) (by nlinarith)]
  unfold tripleMoment
  ring

end RiemannResearch.RH.ExactHeadSignedMomentBounds

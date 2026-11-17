import RiemannResearch.RH.RamanujanFinitePlancherel
import RiemannResearch.RH.ExactHeadGreenPrimitive
import RiemannResearch.RH.ExactHeadAtomOptimizer
import Mathlib.Tactic

/-!
# Corrected exact-head Ramanujan--Plancherel coordinates
Source: user-provided audited Exact-Head Green Profiles, section 8 and
supplement section 11.2. This file supplies the omitted internal definition
W(g) = <R,A_g>, verifies S(1) = beta, and specializes the arithmetic
Plancherel theorem to actual finite normal residuals.
PDF: https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadRamanujanPlancherel
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenPrimitive
open RiemannResearch.RH.Pareto.RamanujanFinitePlancherel

def gcdScore (P : ℕ) (s : Finset ℕ) (w R : ℕ → ℝ) (g : ℕ) : ℝ :=
  pairing s w R (atom P g)

def conductorScore (P : ℕ) (s : Finset ℕ) (w R : ℕ → ℝ) (a : ℕ) : ℝ :=
  transform P (gcdScore P s w R) a

theorem ramanujanSum_gcd_period (P a n : ℕ) (ha : a ∣ P) :
    ramanujanSum a (Nat.gcd n P) = ramanujanSum a n := by
  unfold ramanujanSum
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.dvd_gcd_iff, and_iff_left (dvd_trans (Nat.dvd_of_mem_divisors hd) ha)]

theorem atom_ramanujan_synthesis (P a r : ℕ) (hP : P ≠ 0) (ha : a ∣ P) :
    (∑ g ∈ P.divisors, atom P g r * ramanujanSum a g) =
      ∑ n ∈ Finset.Icc 1 r, ramanujanSum a n := by
  unfold atom
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hg : Nat.gcd n P ∈ P.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n P,hP⟩
  simpa only [ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq_of_mem _ _ _ hg] using ramanujanSum_gcd_period P a n ha

theorem conductorScore_prefix (P a : ℕ) (hP : P ≠ 0) (ha : a ∣ P)
    (s : Finset ℕ) (w R : ℕ → ℝ) :
    conductorScore P s w R a =
      pairing s w R (fun r => ∑ n ∈ Finset.Icc 1 r, ramanujanSum a n) := by
  unfold conductorScore transform gcdScore pairing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← atom_ramanujan_synthesis P a r hP ha, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  ring

theorem conductorScore_one (P : ℕ) (hP : P ≠ 0)
    (s : Finset ℕ) (w R : ℕ → ℝ) :
    conductorScore P s w R 1 = pairing s w R (fun r => (r : ℝ)) := by
  rw [conductorScore_prefix P 1 hP (one_dvd P)]
  congr 1
  funext r
  simp [ramanujanSum]

theorem conductorScore_nontrivial (P a : ℕ) (hP : P ≠ 0)
    (ha : a ∣ P) (ha1 : 1 < a) (s : Finset ℕ) (w R : ℕ → ℝ) :
    conductorScore P s w R a = -pairing s w R (ramanujanPacket a) := by
  rw [conductorScore_prefix P a hP ha]
  have he (r : ℕ) : (∑ n ∈ Finset.Icc 1 r, ramanujanSum a n) =
      -ramanujanPacket a r := by
    have hs : Finset.Ico 1 (r+1) = Finset.Icc 1 r := by
      ext n
      simp only [Finset.mem_Ico,Finset.mem_Icc]
      omega
    rw [ramanujanPacket_prefix a r ha1,hs,neg_neg]
  simp only [pairing,he,mul_neg,Finset.sum_neg_distrib]

/-- The repository's primitiveScore is minus the paper's theta. -/
theorem conductorScore_primitive (P a : ℕ) (hP : P ≠ 0)
    (ha : a ∣ P) (ha1 : 1 < a) (s : Finset ℕ) (w R : ℕ → ℝ) :
    conductorScore P s w R a =
      -primitiveScore s w R a - (a.totient : ℝ)/2 * pairing s w R (fun _ => 1) := by
  rw [conductorScore_nontrivial P a hP ha ha1]
  unfold primitiveScore pairing
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [mul_one]
  have he : (∑ i ∈ s, w i * R i * ((a.totient : ℝ)/2)) =
      ∑ i ∈ s, (a.totient : ℝ)/2 * (w i * R i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

theorem corrected_exact_head_plancherel
    (P x : ℕ) (hP : Squarefree P) (s : Finset ℕ) (w R : ℕ → ℝ)
    (hupper : ∀ g ∈ P.divisors, x < g → gcdScore P s w R g = 0) :
    (∑ a ∈ P.divisors, conductorScore P s w R a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ)/P.totient *
        ∑ g ∈ P.divisors.filter (fun g => g ≤ x), (g.totient : ℝ) * gcdScore P s w R g ^ 2 := by
  rw [show conductorScore P s w R = transform P (gcdScore P s w R) from rfl,
    corrected_plancherel P hP]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g hg hng
  have hxg : x < g := by
    by_contra! h
    exact hng (Finset.mem_filter.mpr ⟨hg,h⟩)
  rw [hupper g hg hxg]
  ring

theorem nontrivial_exact_head_energy
    (P x : ℕ) (hP : Squarefree P) (s : Finset ℕ) (w R : ℕ → ℝ)
    (hupper : ∀ g ∈ P.divisors, x < g → gcdScore P s w R g = 0) :
    (∑ a ∈ P.divisors.erase 1, conductorScore P s w R a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ)/P.totient *
        ∑ g ∈ P.divisors.filter (fun g => g ≤ x), (g.totient : ℝ) * gcdScore P s w R g ^ 2 -
          pairing s w R (fun r => (r : ℝ)) ^ 2 := by
  have he := Finset.sum_erase_add P.divisors
    (fun a => conductorScore P s w R a ^ 2 / (a.totient : ℝ))
    (Nat.one_mem_divisors.mpr hP.ne_zero)
  rw [corrected_exact_head_plancherel P x hP s w R hupper,
    conductorScore_one P hP.ne_zero] at he
  norm_num at he
  linarith


theorem lower_gcd_score_sum (P x : ℕ) (hP : P ≠ 0)
    (s : Finset ℕ) (w R : ℕ → ℝ)
    (hupper : ∀ g ∈ P.divisors, x < g → gcdScore P s w R g = 0) :
    pairing s w R (fun r => (r : ℝ)) =
      ∑ g ∈ P.divisors.filter (fun g => g ≤ x), gcdScore P s w R g := by
  rw [← conductorScore_one P hP s w R]
  change transform P (gcdScore P s w R) 1 = _
  rw [transform_one]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g hg hng
  apply hupper g hg
  by_contra! h
  exact hng (Finset.mem_filter.mpr ⟨hg,h⟩)

/-- The exact lower-support mass bound retains the actual arithmetic scores.
It does not insert the audit's unproved uniform bound on the residual energy. -/
theorem beta_sq_le_lower_score_energy (P x : ℕ) (hP : P ≠ 0)
    (s : Finset ℕ) (w R : ℕ → ℝ)
    (hupper : ∀ g ∈ P.divisors, x < g → gcdScore P s w R g = 0) :
    pairing s w R (fun r => (r : ℝ)) ^ 2 ≤
      (∑ g ∈ P.divisors.filter (fun g => g ≤ x), 1 / (g.totient : ℝ)) *
      (∑ g ∈ P.divisors.filter (fun g => g ≤ x),
        (g.totient : ℝ) * gcdScore P s w R g ^ 2) := by
  rw [lower_gcd_score_sum P x hP s w R hupper]
  exact weighted_mass_sq_le _ (fun g hg =>
    Nat.pos_of_mem_divisors (Finset.mem_filter.mp hg).1) _

theorem atomResidual_upper_score (P x g : ℕ) (hg : g ∈ P.divisors) (hxg : x < g) :
    gcdScore P (Finset.Icc 1 (P-1)) (progressionWeight P)
      (ExactHeadAtomOptimizer.atomResidual P x) g = 0 := by
  apply ExactHeadAtomOptimizer.atomResidual_normal
  exact Submodule.subset_span ⟨g,Finset.mem_filter.mpr ⟨hg,hxg⟩,rfl⟩

/-- The corrected identity for the actual optimizer, with no unproved bound
on q, beta, the coefficients, or the return operator. -/
theorem atomResidual_plancherel (P x : ℕ) (hP : Squarefree P) :
    (∑ a ∈ P.divisors, conductorScore P (Finset.Icc 1 (P-1)) (progressionWeight P)
      (ExactHeadAtomOptimizer.atomResidual P x) a ^ 2 / (a.totient : ℝ)) =
      (P : ℝ)/P.totient *
        ∑ g ∈ P.divisors.filter (fun g => g ≤ x), (g.totient : ℝ) *
          gcdScore P (Finset.Icc 1 (P-1)) (progressionWeight P)
            (ExactHeadAtomOptimizer.atomResidual P x) g ^ 2 := by
  exact corrected_exact_head_plancherel P x hP _ _ _
    (fun g hg hxg => atomResidual_upper_score P x g hg hxg)

end RiemannResearch.RH.ExactHeadRamanujanPlancherel

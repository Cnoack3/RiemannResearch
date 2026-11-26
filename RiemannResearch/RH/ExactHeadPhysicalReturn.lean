import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.ExactHeadGreenProfile
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.Analysis.FiniteProfileEnergy
import RiemannResearch.RH.ExactHeadAtomReturnMoments
import RiemannResearch.RH.ExactHeadAtomOptimizer
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Physical-window signals and complete gcd-atom returns

Source: user-provided "Best Nyman Beurling for RH - A1-A2 Audited Revision",
sections 22.2 and 23.5, especially (22.5)--(22.7) and (23.21)--(23.24).
https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view

This formalizes the missing arithmetic identification of the physical signal
with activated moments. The exact lower-class correction is retained at every
cutoff. Its vanishing requires Y < p*p, prime coverage, and x < 2*p.
The identities allow arbitrary real weights and signals; the actual-optimizer
tail theorem specializes to the complete periodized Pareto weight.
No uniform energy bound, large-sieve estimate, curvature decay, A1, A2, or RH
is asserted here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadPhysicalReturn
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.ExactHeadAtomReturnMoments
open RiemannResearch.Analysis.FiniteProfileEnergy

theorem gcd_eq_prime_iff_before_square (P p n : ℕ) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hn : 0 < n) (hnp : n < p * p) :
    Nat.gcd n P = p ↔ n = p := by
  constructor
  · intro hg
    have hpn : p ∣ n := hg ▸ Nat.gcd_dvd_left n P
    obtain ⟨k, rfl⟩ := hpn
    have hk0 : 0 < k := by nlinarith [hp.pos]
    have hkp : k < p := (Nat.mul_lt_mul_left hp.pos).mp hnp
    by_cases hk : k = 1
    · simp [hk]
    obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk
    have hqp : q < p := (Nat.le_of_dvd hk0 hqk).trans_lt hkp
    have hqn : q ∣ p * k := dvd_mul_of_dvd_right hqk p
    have hqd : q ∣ p := hg ▸ Nat.dvd_gcd hqn (hcover q hq hqp.le)
    rcases (Nat.dvd_prime hp).mp hqd with hq1 | hqe
    · exact (hq.ne_one hq1).elim
    · omega
  · intro he
    subst n
    exact Nat.gcd_eq_left (hcover p hp le_rfl)

theorem prime_atom_eq_one (P p r : ℕ) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hpr : p ≤ r) (hr : r < p * p) :
    atom P p r = 1 := by
  unfold atom
  calc
    _ = ∑ n ∈ Finset.Icc 1 r, if n = p then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [gcd_eq_prime_iff_before_square P p n hp hcover
        (Finset.mem_Icc.mp hn).1 ((Finset.mem_Icc.mp hn).2.trans_lt hr)]
    _ = 1 := by simp [hp.ne_zero, hpr]


/-- The lower p-class is the exact correction at every physical position. -/
theorem upperDivisorSignal_eq_grid_sub_atom (P x p r : ℕ)
    (hP : P ≠ 0) (hpP : p ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p) :
    upperDivisorSignal P x p r = grid p r - atom P p r := by
  have hpmem : p ∈ P.divisors := Nat.mem_divisors.mpr ⟨hpP, hP⟩
  have heq : upperDivisorSignal P x p r =
      ∑ g ∈ P.divisors.erase p, if p ∣ g then atom P g r else 0 := by
    unfold upperDivisorSignal synthesis
    simp_rw [ite_mul, one_mul, zero_mul]
    apply Finset.sum_subset
    · intro g hg
      obtain ⟨hg, hxg⟩ := Finset.mem_filter.mp hg
      exact Finset.mem_erase.mpr ⟨by omega, hg⟩
    · intro g hg hnot
      have hgm := (Finset.mem_erase.mp hg).2
      have hgne := (Finset.mem_erase.mp hg).1
      have hgpos := Nat.pos_of_mem_divisors hgm
      have hgx : g ≤ x := by
        by_contra! h
        exact hnot (Finset.mem_filter.mpr ⟨hgm, h⟩)
      have hnd : ¬ p ∣ g := by
        rintro ⟨k, rfl⟩
        have hk : 2 ≤ k := by
          by_contra! h
          interval_cases k <;> simp_all
        nlinarith
      simp [hnd]
  have hs := Finset.sum_erase_add P.divisors
    (fun g => if p ∣ g then atom P g r else 0) hpmem
  rw [← grid_eq_atom_sum P p r hP hpmem] at hs
  simp only [dvd_refl, if_true] at hs
  rw [heq]
  linarith

theorem upperDivisorSignal_zero_head (P x p r : ℕ) (hr : r ≤ x) :
    upperDivisorSignal P x p r = 0 := by
  unfold upperDivisorSignal synthesis
  apply Finset.sum_eq_zero
  intro g hg
  rw [atom_zero_of_lt P g r (hr.trans_lt (Finset.mem_filter.mp hg).2), mul_zero]

theorem upperDivisorSignal_eq_grid_sub_one (P x p r : ℕ)
    (hP : P ≠ 0) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p)
    (hxr : x < r) (hr : r < p * p) :
    upperDivisorSignal P x p r = grid p r - 1 := by
  rw [upperDivisorSignal_eq_grid_sub_atom P x p r hP
    (hcover p hp le_rfl) hpx hhalf,
    prime_atom_eq_one P p r hp hcover (hpx.trans hxr.le) hr]

/-- The paper's z_Y, with the integer physical interval and factor p explicit. -/
def physicalSignal (x Y p : ℕ) (w h : ℕ → ℝ) : ℝ :=
  (p : ℝ) * pairing (Finset.Icc (x + 1) Y) w h (fun n => grid p n - 1)

theorem physical_pairing_upper (P x Y p : ℕ) (w h : ℕ → ℝ) :
    pairing (Finset.Icc (x + 1) Y) w h (upperDivisorSignal P x p) =
      activatedMoment P x Y p w h := by
  rw [← upperDivisorSignal_prefix]
  apply Finset.sum_subset
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  · intro n hn hnot
    have hnx : n ≤ x := by
      by_contra! h
      exact hnot (Finset.mem_Icc.mpr ⟨h, (Finset.mem_Icc.mp hn).2⟩)
    rw [upperDivisorSignal_zero_head P x p n hnx, mul_zero]

/-- Exact correction beyond the safe window: the lower-class re-entries
cannot be discarded after the physical cutoff reaches p squared. -/
theorem physicalSignal_with_reentry (P x Y p : ℕ) (w h : ℕ → ℝ)
    (hP : P ≠ 0) (hpP : p ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p) :
    physicalSignal x Y p w h =
      (p : ℝ) * activatedMoment P x Y p w h +
      (p : ℝ) * pairing (Finset.Icc (x + 1) Y) w h (fun n => atom P p n - 1) := by
  rw [← physical_pairing_upper]
  unfold physicalSignal pairing
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [upperDivisorSignal_eq_grid_sub_atom P x p n hP hpP hpx hhalf]
  ring

/-- All lower gcd classes carrying the label, at an arbitrary head depth. -/
def lowerDivisorSignal (P x p n : ℕ) : ℝ :=
  ∑ g ∈ P.divisors.filter (fun g => g ≤ x), if p ∣ g then atom P g n else 0

theorem grid_eq_upper_add_lower (P x p n : ℕ) (hP : P ≠ 0) (hpP : p ∣ P) :
    grid p n = upperDivisorSignal P x p n + lowerDivisorSignal P x p n := by
  rw [grid_eq_atom_sum P p n hP (Nat.mem_divisors.mpr ⟨hpP, hP⟩)]
  simpa only [upperDivisorSignal, upperDivisors, synthesis, lowerDivisorSignal,
    ite_mul, one_mul, zero_mul, not_lt] using
    (Finset.sum_filter_add_sum_filter_not P.divisors (fun g : ℕ => x < g)
      (fun g : ℕ => if p ∣ g then atom P g n else 0)).symm

/-- The physical splitting for any head and cutoff, with all lower classes retained. -/
theorem physicalSignal_with_lower_classes (P x Y p : ℕ) (w h : ℕ → ℝ)
    (hP : P ≠ 0) (hpP : p ∣ P) :
    physicalSignal x Y p w h =
      (p : ℝ) * activatedMoment P x Y p w h +
      (p : ℝ) * pairing (Finset.Icc (x + 1) Y) w h
        (fun n => lowerDivisorSignal P x p n - 1) := by
  rw [← physical_pairing_upper]
  unfold physicalSignal pairing
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  change w n * h n * (grid p n - 1) =
    w n * h n * upperDivisorSignal P x p n + w n * h n * (lowerDivisorSignal P x p n - 1)
  rw [grid_eq_upper_add_lower P x p n hP hpP]
  ring

/-- Covering the primes below ℓ in the quotient period M delays the first
return of the lower class p to at least p * ℓ. The label p may be composite. -/
theorem gcd_eq_label_before_return {p M ℓ n : ℕ} (hp : 0 < p)
    (hcover : ∀ q, Nat.Prime q → q < ℓ → q ∣ M) (hn : 0 < n) (hlim : n < p * ℓ) :
    Nat.gcd n (p * M) = p ↔ n = p := by
  constructor
  · intro hg
    have hpn : p ∣ n := hg ▸ Nat.gcd_dvd_left n (p * M)
    obtain ⟨k, rfl⟩ := hpn
    have hkpos : 0 < k := by by_contra! hk; simp [Nat.eq_zero_of_le_zero hk] at hn
    have hklt := (Nat.mul_lt_mul_left hp).mp hlim
    have hcop : Nat.gcd k M = 1 := by
      rw [Nat.gcd_mul_left] at hg
      apply (Nat.mul_right_inj hp.ne').mp
      simpa only [Nat.mul_one] using hg
    by_cases hk : k = 1
    · simp [hk]
    obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk
    have hqM := hcover q hq ((Nat.le_of_dvd hkpos hqk).trans_lt hklt)
    exact (hq.not_dvd_one (hcop ▸ Nat.dvd_gcd hqk hqM)).elim
  · intro he
    subst n
    exact Nat.gcd_eq_left (dvd_mul_right p M)

theorem atom_one_before_return {p M ℓ n : ℕ} (hp : 0 < p)
    (hcover : ∀ q, Nat.Prime q → q < ℓ → q ∣ M) (hpn : p ≤ n) (hlim : n < p * ℓ) :
    atom (p * M) p n = 1 := by
  unfold atom
  calc
    _ = ∑ j ∈ Finset.Icc 1 n, if j = p then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hb := Finset.mem_Icc.mp hj
      simp only [gcd_eq_label_before_return hp hcover hb.1 (hb.2.trans_lt hlim)]
    _ = 1 := by simp [hp.ne', hpn]

/-- At the least prime omitted by M the cumulative lower atom increases to two. -/
theorem atom_two_at_first_return {p M ℓ : ℕ} (hp : 0 < p) (hℓ : Nat.Prime ℓ)
    (hcover : ∀ q, Nat.Prime q → q < ℓ → q ∣ M) (hmiss : ¬ ℓ ∣ M) :
    atom (p * M) p (p * ℓ) = 2 := by
  have hlt : p < p * ℓ := by
    simpa only [Nat.mul_one] using (Nat.mul_lt_mul_left hp).mpr hℓ.one_lt
  let m := p * ℓ - 1
  have hnext : m + 1 = p * ℓ := by dsimp [m]; omega
  have hfirst : atom (p * M) p m = 1 :=
    atom_one_before_return hp hcover (by dsimp [m]; omega) (by dsimp [m]; omega)
  have hlast : Nat.gcd (p * ℓ) (p * M) = p := by
    rw [Nat.gcd_mul_left, (hℓ.coprime_iff_not_dvd.mpr hmiss).gcd_eq_one, Nat.mul_one]
  have hset : Finset.Icc 1 (p * ℓ) = insert (p * ℓ) (Finset.Icc 1 m) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : p * ℓ ∉ Finset.Icc 1 m := by
    simp only [Finset.mem_Icc]; omega
  unfold atom at hfirst ⊢
  rw [hset, Finset.sum_insert hnot, if_pos hlast, hfirst]
  norm_num

theorem physicalSignal_eq_activatedMoment_before_return (p M ℓ x Y : ℕ) (w h : ℕ → ℝ)
    (hp : 0 < p) (hM : 0 < M) (hpx : p ≤ x) (hhalf : x < 2 * p)
    (hcover : ∀ q, Nat.Prime q → q < ℓ → q ∣ M) (hY : Y < p * ℓ) :
    physicalSignal x Y p w h = (p : ℝ) * activatedMoment (p * M) x Y p w h := by
  rw [physicalSignal_with_reentry (p * M) x Y p w h (Nat.mul_pos hp hM).ne'
    (dvd_mul_right p M) hpx hhalf]
  have hz : pairing (Finset.Icc (x + 1) Y) w h (fun n => atom (p * M) p n - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hb := Finset.mem_Icc.mp hn
    change w n * h n * (atom (p * M) p n - 1) = 0
    rw [atom_one_before_return hp hcover (by omega) (hb.2.trans_lt hY)]
    ring
  rw [hz]
  ring

/-- The period-specific cutoff is necessary and sufficient for the signed
physical signal to equal its activated moment for every input. -/
theorem all_physicalSignal_eq_activatedMoment_iff (p M ℓ x Y : ℕ)
    (hp : 0 < p) (hM : 0 < M) (hpx : p ≤ x) (hhalf : x < 2 * p)
    (hℓ : Nat.Prime ℓ) (hcover : ∀ q, Nat.Prime q → q < ℓ → q ∣ M)
    (hmiss : ¬ ℓ ∣ M) :
    (∀ w h : ℕ → ℝ, physicalSignal x Y p w h =
      (p : ℝ) * activatedMoment (p * M) x Y p w h) ↔ Y < p * ℓ := by
  constructor
  · intro hall
    by_contra! hn
    let w : ℕ → ℝ := fun n => if n = p * ℓ then 1 else 0
    have hloc : p * ℓ ∈ Finset.Icc (x + 1) Y := by
      have htwo : 2 * p ≤ p * ℓ := by
        simpa only [Nat.mul_comm 2 p] using Nat.mul_le_mul_left p hℓ.two_le
      exact Finset.mem_Icc.mpr ⟨by omega, hn⟩
    have hs := physicalSignal_with_reentry (p * M) x Y p w (fun _ => 1)
      (Nat.mul_pos hp hM).ne' (dvd_mul_right p M) hpx hhalf
    have he : pairing (Finset.Icc (x + 1) Y) w (fun _ => 1)
        (fun n => atom (p * M) p n - 1) = 1 := by
      simp [pairing, w, ite_mul, hloc, atom_two_at_first_return hp hℓ hcover hmiss]
      norm_num
    rw [hall w (fun _ => 1), he] at hs
    have hpos : (0 : ℝ) < p := by exact_mod_cast hp
    linarith
  · intro hY w h
    exact physicalSignal_eq_activatedMoment_before_return p M ℓ x Y w h hp hM hpx hhalf hcover hY

theorem physicalSignal_eq_activatedMoment (P x Y p : ℕ) (w h : ℕ → ℝ)
    (hP : P ≠ 0) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p) (hY : Y < p * p) :
    physicalSignal x Y p w h = (p : ℝ) * activatedMoment P x Y p w h := by
  rw [physicalSignal_with_reentry P x Y p w h hP (hcover p hp le_rfl) hpx hhalf]
  have hz : pairing (Finset.Icc (x + 1) Y) w h (fun n => atom P p n - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    change w n * h n * (atom P p n - 1) = 0
    rw [prime_atom_eq_one P p n hp hcover (by omega) (hn'.2.trans_lt hY)]
    ring
  rw [hz]
  ring

theorem primorial_physicalSignal_eq_activatedMoment (x Y p : ℕ) (w h : ℕ → ℝ)
    (hp : Nat.Prime p) (hpx : p ≤ x) (hhalf : x < 2 * p) (hY : Y < p * p) :
    physicalSignal x Y p w h = (p : ℝ) * activatedMoment (primorial x) x Y p w h := by
  exact physicalSignal_eq_activatedMoment (primorial x) x Y p w h
    (primorial_pos x).ne' hp (fun q hq hqp => hq.dvd_primorial_iff.mpr (hqp.trans hpx))
    hpx hhalf hY

/-- In a physical prime window the original signal equals the positive
endpoint covariance, including every tail return. -/
theorem physicalSignal_eq_endpoint (P x Y p : ℕ) (T : Finset ℕ)
    (w C u v : ℕ → ℝ)
    (hP : P ≠ 0) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p) (hY : Y < p * p)
    (hglobal : ∀ f ∈ upperSpan P x (atom P),
      pairing (Finset.Icc 1 Y) w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ upperSpan P x (atom P), pairing T w (C - v) f = 0) :
    physicalSignal x Y p w (C - u) =
      (p : ℝ) * pairing T w (u - v) (upperDivisorSignal P x p) := by
  rw [physicalSignal_eq_activatedMoment P x Y p w (C-u) hP hp hcover hpx hhalf hY,
    endpoint_divisor_signal P x Y p T w C u v hglobal htail]

/-- The actual optimizer supplies the global normal equations. This negative
tail formula uses the original residual, whereas the endpoint formula uses
the positive fitted drift u-v. -/
theorem atomResidual_physicalSignal_eq_tail (P x Y p : ℕ)
    (hP : P ≠ 0) (hp : Nat.Prime p)
    (hcover : ∀ q, Nat.Prime q → q ≤ p → q ∣ P)
    (hpx : p ≤ x) (hhalf : x < 2 * p)
    (hY : Y < p * p) (hYP : Y < P) :
    physicalSignal x Y p (Pareto.progressionWeight P)
      (Pareto.ExactHeadAtomOptimizer.atomResidual P x) =
      -(p : ℝ) * pairing (Finset.Icc (Y + 1) (P - 1)) (Pareto.progressionWeight P)
        (Pareto.ExactHeadAtomOptimizer.atomResidual P x)
        (upperDivisorSignal P x p) := by
  let w := Pareto.progressionWeight P
  let R := Pareto.ExactHeadAtomOptimizer.atomResidual P x
  let U := upperDivisorSignal P x p
  have hnormal : pairing (Finset.Icc 1 (P - 1)) w R U = 0 :=
    Pareto.ExactHeadAtomOptimizer.atomResidual_normal P x U (upperDivisorSignal_mem P x p)
  have hdis : Disjoint (Finset.Icc 1 Y) (Finset.Icc (Y + 1) (P - 1)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    omega
  have hunion : Finset.Icc 1 Y ∪ Finset.Icc (Y + 1) (P - 1) =
      Finset.Icc 1 (P - 1) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hsplit : pairing (Finset.Icc 1 Y) w R U +
      pairing (Finset.Icc (Y + 1) (P - 1)) w R U = 0 := by
    unfold pairing
    rw [← Finset.sum_union hdis, hunion]
    exact hnormal
  change physicalSignal x Y p w R =
    -(p : ℝ) * pairing (Finset.Icc (Y + 1) (P - 1)) w R U
  rw [physicalSignal_eq_activatedMoment P x Y p w R hP hp hcover hpx hhalf hY,
    ← upperDivisorSignal_prefix]
  change (p : ℝ) * pairing (Finset.Icc 1 Y) w R U = _
  nlinarith

/-- The first square is a genuine boundary, already at the paper's period 30.
This refutes extending the zero-correction formula to arbitrary cutoffs. -/
theorem square_cutoff_requires_reentry :
    upperDivisorSignal 30 5 3 9 = 1 ∧ grid 3 9 - 1 = 2 := by
  have hc : (Finset.Icc 1 9).filter (fun n => Nat.gcd n 30 = 3) = {3, 9} := by decide
  have ha : atom 30 3 9 = 2 := by
    have hh := congrArg (fun s : Finset ℕ => (s.card : ℝ)) hc
    simpa [atom] using hh
  constructor
  · rw [upperDivisorSignal_eq_grid_sub_atom 30 5 3 9 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), ha]
    norm_num [grid]
  · norm_num [grid]

end RiemannResearch.RH.ExactHeadPhysicalReturn

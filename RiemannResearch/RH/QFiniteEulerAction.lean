import RiemannResearch.RH.QFloorEulerCandidates
import RiemannResearch.RH.QFloorEulerOperators
import RiemannResearch.RH.PrimorialExtrapolationObstruction
import Mathlib.Tactic.Ring

/-!
# The finite prime Euler action equals the explicit divisor candidate

Source: user-directed finite Euler candidate research, 13 October 2026.
The prime recursion is proved from the existing exact Möbius divisor
regrouping. A recursive freshness condition simply records that no prime
is repeated. No infinite operator limit is asserted.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFloorEulerCandidates
open ZetaTwoHilbert QFloorDilation QFloorEulerOperators Pareto

theorem rough_count_prime_step (p P n : ℕ) (hp : p.Prime)
    (hP : 0 < P) (hpP : ¬ p ∣ P) :
    sieveRoughCount (p * P) n =
      sieveRoughCount P n - sieveRoughCount P (n / p) := by
  rw [← sieve_floor_count (p * P) n (Nat.mul_pos hp.pos hP),
    ← sieve_floor_count P n hP, ← sieve_floor_count P (n / p) hP]
  simpa only [Nat.div_div_eq_div_mul] using
    PrimorialExtrapolation.direct_prime_divisor_transform p P hp hP hpP
      (fun d => ((n / d : ℕ) : ℝ))

/-- Adding one new prime is exactly one bounded Euler factor. -/
theorem candidate_prime_step (p P m : ℕ) (hp : p.Prime)
    (hP : 0 < P) (hpP : ¬ p ∣ P) (hm : 0 < m) :
    candidate (p * P) m =
      (1 - floorDilation p hp.pos) (candidate P m) := by
  apply qSequence_injective
  change qSequence (candidate (p * P) m) =
    qSequenceLinear (candidate P m - floorDilation p hp.pos (candidate P m))
  rw [map_sub]
  funext n
  change qSequence (candidate (p * P) m) n = qSequence (candidate P m) n -
    qSequence (floorDilation p hp.pos (candidate P m)) n
  rw [floorDilation_sequence]
  dsimp only
  rw [candidate_rough_count _ _ _ (Nat.mul_pos hp.pos hP) hm,
    candidate_rough_count P m n hP hm,
    candidate_rough_count P m (n / p) hP hm,
    rough_count_prime_step p P n hp hP hpP,
    rough_count_prime_step p P (n / m) hp hP hpP]
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm m p]
  ring

def listConductor (ps : List {p : ℕ // p.Prime}) : ℕ :=
  (ps.map Subtype.val).prod

theorem listConductor_pos (ps : List {p : ℕ // p.Prime}) :
    0 < listConductor ps := by
  induction ps with
  | nil => simp [listConductor]
  | cons p ps ih =>
    simpa only [listConductor, List.map_cons, List.prod_cons] using
      Nat.mul_pos p.property.pos ih

/-- A transparent recursive record that each prime is new to the conductor. -/
def FreshPrimes : List {p : ℕ // p.Prime} → Prop
  | [] => True
  | p :: ps => (¬ p.val ∣ listConductor ps) ∧ FreshPrimes ps

/-- Complete arbitrary-length finite Euler expansion, as a legal residue sum. -/
theorem primeEulerProduct_qResidue (ps : List {p : ℕ // p.Prime})
    (hps : FreshPrimes ps) (m : ℕ) (hm : 0 < m) :
    primeEulerProduct ps (qResidue m) = candidate (listConductor ps) m := by
  induction ps with
  | nil => simp [primeEulerProduct, listConductor, candidate, qResidue_one]
  | cons p ps ih =>
    change (1 - floorDilation p.val p.property.pos)
      (primeEulerProduct ps (qResidue m)) = candidate (p.val * listConductor ps) m
    rw [ih hps.2]
    exact (candidate_prime_step p.val (listConductor ps) m p.property
      (listConductor_pos ps) hps.1 hm).symm

end RiemannResearch.RH.QFloorEulerCandidates

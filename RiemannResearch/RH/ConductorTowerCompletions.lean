import RiemannResearch.NumberTheory.ProfiniteCRT
import RiemannResearch.NumberTheory.PrimeResidueTopology
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Full and squarefree conductor towers

Source: the atom/carry CRT Stage 3 handoff, §14.7.2. The compatible-residue
CRT and p-adic product equivalence are in `NumberTheory.ProfiniteGeneralizedCRT`
and `NumberTheory.ProfiniteCRT`. We identify the actual two inverse systems
and the componentwise reduction between their limits.
-/

noncomputable section

namespace RiemannResearch.RH.ConductorTowerCompletions

open RiemannResearch.NumberTheory.GeneralizedCRT
open Pareto.SquarefreeStageExhaustion QFullDivisorProjection
open Filter

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- The inverse limit with its literal transition maps. -/
def towerRing (m : ℕ → PositiveModulus) : Subring ((j : ℕ) → ZMod (m j).val) where
  carrier := {a | ∀ i j (h : (m i).val ∣ (m j).val), ZMod.castHom h _ (a j) = a i}
  zero_mem' := fun _ _ h => map_zero (ZMod.castHom h _)
  one_mem' := fun _ _ h => map_one (ZMod.castHom h _)
  neg_mem' := by
    intro a ha i j h
    change ZMod.castHom h _ (-a j) = -a i
    rw [map_neg, ha i j h]
  add_mem' := by
    intro a b ha hb i j h
    change ZMod.castHom h _ (a j + b j) = a i + b i
    rw [map_add, ha i j h, hb i j h]
  mul_mem' := by
    intro a b ha hb i j h
    change ZMod.castHom h _ (a j * b j) = a i * b i
    rw [map_mul, ha i j h, hb i j h]

/-- Restriction of a full profinite integer to the chosen periods. -/
def towerRestriction (m : ℕ → PositiveModulus) : ProfiniteInt →+* towerRing m where
  toFun x := ⟨fun i => reduce (m i) x, fun _ _ h => reduce_compatible x h⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem continuous_towerRestriction (m : ℕ → PositiveModulus) :
    Continuous (towerRestriction m) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_reduce (m i)

/-- Every compatible tuple on a divisibility chain lifts to a profinite integer. -/
theorem towerRestriction_surjective (m : ℕ → PositiveModulus)
    (hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val) :
    Function.Surjective (towerRestriction m) := by
  intro a
  let r (i : ℕ) : ℤ := (a.val i).val
  have hr (i : ℕ) : (r i : ZMod (m i).val) = a.val i := by
    change (((a.val i).val : ℤ) : ZMod (m i).val) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hcast (i j : ℕ) (h : (m i).val ∣ (m j).val) :
      Int.ModEq ((m i).val : ℤ) (r i) (r j) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    have hc := congrArg (ZMod.castHom h (ZMod (m i).val)) (hr j)
    rw [map_intCast, a.property i j h] at hc
    exact (hr i).trans hc.symm
  obtain ⟨x, hx⟩ := (exists_profiniteInt_iff_pairwise m r).mpr (by
    intro i j
    rcases le_total i j with hij | hji
    · rw [Nat.gcd_eq_left (hm _ _ hij)]
      exact hcast i j (hm _ _ hij)
    · rw [Nat.gcd_eq_right (hm _ _ hji)]
      exact (hcast j i (hm _ _ hji)).symm)
  exact ⟨x, Subtype.ext (funext fun i => (hx i).trans (hr i))⟩

/-- A divisibility-cofinal chain retains every coordinate. -/
def cofinalTowerEquiv (m : ℕ → PositiveModulus)
    (hm : ∀ i j, i ≤ j → (m i).val ∣ (m j).val)
    (hc : ∀ n : PositiveModulus, ∃ i, n.val ∣ (m i).val) :
    ProfiniteInt ≃+* towerRing m := RingEquiv.ofBijective (towerRestriction m) ⟨by
  intro x y h
  apply profiniteInt_ext_of_lcm_cofinal m
  · intro n
    obtain ⟨i, hi⟩ := hc n
    exact ⟨{i}, by simpa using hi⟩
  · intro i
    exact congrArg (fun a : towerRing m => a.val i) h,
  towerRestriction_surjective m hm⟩

def lcmModulus (M : ℕ → ℕ) (j : ℕ) : PositiveModulus :=
  ⟨lcmPeriod (M j), (lcmPeriod (M j)).ne_zero⟩

/-- The full lcm-stage inverse limit, with every prime-power depth. -/
def lcmTowerPadicEquiv (M : ℕ → ℕ) (hmono : Monotone M) (hM : Tendsto M atTop atTop) :
    towerRing (lcmModulus M) ≃+* ((p : Nat.Primes) → PadicInt p.val) :=
  (cofinalTowerEquiv (lcmModulus M) (fun _ _ h => lcmPeriod_nested (hmono h)) (by
    intro n
    by_cases hn : 1 < n.val
    · exact lcmPeriod_exhausts M hM n.val hn
    · have hn1 : n.val = 1 := by have := n.property; omega
      exact ⟨0, hn1 ▸ one_dvd _⟩)).symm.trans profinitePadicEquiv

def primorialModulus (n : ℕ) : PositiveModulus :=
  ⟨primorialPeriod n, (primorialPeriod_pos n).ne'⟩

abbrev primeModulus (p : Nat.Primes) : PositiveModulus := ⟨p.val, p.property.ne_zero⟩

private theorem prime_dvd_stage (p : Nat.Primes) :
    p.val ∣ (primorialModulus p.val).val :=
  squarefree_dvd_primorialPeriod p.val p.val p.property.squarefree le_rfl

/-- Each prime can be read at a single primorial stage. -/
def primorialPrimeMap : towerRing primorialModulus →+* ((p : Nat.Primes) → ZMod p.val) where
  toFun a p := ZMod.castHom (prime_dvd_stage p) _ (a.val p.val)
  map_zero' := funext fun p => map_zero (ZMod.castHom (prime_dvd_stage p) _)
  map_one' := funext fun p => map_one (ZMod.castHom (prime_dvd_stage p) _)
  map_add' _ _ := funext fun p => map_add (ZMod.castHom (prime_dvd_stage p) _) _ _
  map_mul' _ _ := funext fun p => map_mul (ZMod.castHom (prime_dvd_stage p) _) _ _

theorem primorialPrimeMap_restrict (x : ProfiniteInt) (p : Nat.Primes) :
    primorialPrimeMap (towerRestriction primorialModulus x) p = reduce (primeModulus p) x :=
  reduce_compatible x (m := primeModulus p) (n := primorialModulus p.val) (prime_dvd_stage p)

/-- Depth-one p-adic reduction, with its codomain written as ZMod p. -/
def componentReduction (p : Nat.Primes) : PadicInt p.val →+* ZMod p.val :=
  (ZMod.castHom (by simp : p.val ∣ p.val ^ 1) _).comp (PadicInt.toZModPow 1)

theorem full_to_squarefree_apply (x : ProfiniteInt) (p : Nat.Primes) :
    primorialPrimeMap (towerRestriction primorialModulus x) p =
      componentReduction p (profinitePadicEquiv x p) := by
  rw [primorialPrimeMap_restrict]
  change _ = ZMod.castHom (by simp : p.val ∣ p.val ^ 1) (ZMod p.val)
    (PadicInt.toZModPow 1 (padicProjection p x))
  rw [padicProjection_toZModPow]
  exact (reduce_compatible x (m := primeModulus p) (n := primePowerModulus p 1)
    (by simp [primePowerModulus])).symm

private theorem residue_ext_squarefree (m : PositiveModulus) (hm : Squarefree m.val)
    (x y : ProfiniteInt)
    (h : ∀ p : Nat.Primes, reduce (primeModulus p) x = reduce (primeModulus p) y) :
    reduce m x = reduce m y := by
  let a : ℤ := (reduce m x).val
  let b : ℤ := (reduce m y).val
  have hx : (a : ZMod m.val) = reduce m x := by
    change (((reduce m x).val : ℤ) : ZMod m.val) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hy : (b : ZMod m.val) = reduce m y := by
    change (((reduce m y).val : ℤ) : ZMod m.val) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hdiv (p : ℕ) (hp : p ∈ m.val.primeFactors) : (p : ℤ) ∣ a - b := by
    let q : Nat.Primes := ⟨p, Nat.prime_of_mem_primeFactors hp⟩
    have hd : (primeModulus q).val ∣ m.val := (Nat.mem_primeFactors.mp hp).2.1
    have hx' := congrArg (ZMod.castHom hd (ZMod p)) hx
    have hy' := congrArg (ZMod.castHom hd (ZMod p)) hy
    rw [map_intCast] at hx' hy'
    have ha : (a : ZMod p) = reduce (primeModulus q) x :=
      hx'.trans (reduce_compatible x (m := primeModulus q) hd)
    have hb : (b : ZMod p) = reduce (primeModulus q) y :=
      hy'.trans (reduce_compatible y (m := primeModulus q) hd)
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, ha, hb, sub_eq_zero]
    exact h q
  have hcop : (m.val.primeFactors : Set ℕ).Pairwise (fun p q => IsCoprime (p : ℤ) (q : ℤ)) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq).isCoprime
  have hall := Finset.prod_dvd_of_coprime hcop hdiv
  have he : (∏ p ∈ m.val.primeFactors, (p : ℤ)) = (m.val : ℤ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℤ)) (Nat.prod_primeFactors_of_squarefree hm)
  rw [he] at hall
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) m.val).mpr hall
  simpa only [Int.cast_sub, sub_eq_zero, hx, hy] using hz

/-- The primorial inverse limit has one residue for each prime. -/
def primorialTowerEquiv : towerRing primorialModulus ≃+* ((p : Nat.Primes) → ZMod p.val) :=
  RingEquiv.ofBijective primorialPrimeMap ⟨by
    intro a b hab
    have hs := towerRestriction_surjective primorialModulus (fun _ _ h => primorialPeriod_nested h)
    obtain ⟨x, rfl⟩ := hs a
    obtain ⟨y, rfl⟩ := hs b
    apply Subtype.ext
    funext i
    apply residue_ext_squarefree _ (primorialPeriod_squarefree i)
    intro p
    exact (primorialPrimeMap_restrict x p).symm.trans
      ((congrFun hab p).trans (primorialPrimeMap_restrict y p)), by
    intro y
    let z : (p : Nat.Primes) → PadicInt p.val := fun p => ((y p).val : ℕ)
    refine ⟨towerRestriction primorialModulus (profinitePadicEquiv.symm z), funext fun p => ?_⟩
    rw [full_to_squarefree_apply, profinitePadicEquiv.apply_symm_apply]
    change componentReduction p ((y p).val : ℕ) = _
    rw [map_natCast]
    exact ZMod.natCast_zmod_val _⟩

section PrimeUniformity

local instance (p : Nat.Primes) : UniformSpace (ZMod p.val) := ⊥
local instance : UniformSpace {n : ℕ // 1 ≤ n} :=
  RiemannResearch.NumberTheory.PrimeResidueTopology.positiveCongruenceUniformity

/-- The completion of the positive integers for the prime-residue uniformity
identifies with the actual primorial inverse limit. -/
def positiveCompletionPrimorialEquiv :
    @UniformSpace.Completion {n : ℕ // 1 ≤ n}
      RiemannResearch.NumberTheory.PrimeResidueTopology.positiveCongruenceUniformity ≃
      towerRing primorialModulus :=
  RiemannResearch.NumberTheory.PrimeResidueTopology.positiveCRTCompletionEquiv.toEquiv.trans
    primorialTowerEquiv.symm.toEquiv

end PrimeUniformity

/-- Both limits have their inverse-limit topology; the primorial isomorphism
is continuous in both directions. -/
theorem primorialTowerEquiv_bicontinuous :
    Continuous primorialTowerEquiv.toEquiv ∧ Continuous primorialTowerEquiv.symm.toEquiv := by
  have hs := towerRestriction_surjective primorialModulus (fun _ _ h => primorialPeriod_nested h)
  let : CompactSpace (towerRing primorialModulus) :=
    hs.compactSpace (continuous_towerRestriction primorialModulus)
  have hc : Continuous primorialTowerEquiv.toEquiv := by
    apply continuous_pi
    intro p
    exact continuous_of_discreteTopology.comp ((continuous_apply p.val).comp continuous_subtype_val)
  exact ⟨hc, hc.continuous_symm_of_equiv_compact_to_t2⟩

/-- The isomorphism to the p-adic product for the cofinal lcm tower is a homeomorphism. -/
theorem lcmTowerPadicEquiv_bicontinuous (M : ℕ → ℕ) (hmono : Monotone M)
    (hM : Tendsto M atTop atTop) :
    Continuous (lcmTowerPadicEquiv M hmono hM).toEquiv ∧
      Continuous (lcmTowerPadicEquiv M hmono hM).symm.toEquiv := by
  let : CompactSpace ((p : Nat.Primes) → PadicInt p.val) :=
    profinitePadicEquiv.surjective.compactSpace isTopologicalRingCRT_profinitePadicEquiv.1
  let e := lcmTowerPadicEquiv M hmono hM
  have hi : Continuous e.symm.toEquiv :=
    (continuous_towerRestriction (lcmModulus M)).comp isTopologicalRingCRT_profinitePadicEquiv.2
  exact ⟨hi.continuous_symm_of_equiv_compact_to_t2, hi⟩

/-- This p-adic tuple has a single nonzero component, the integer 2 at 2. -/
def twoSupported (p : Nat.Primes) : PadicInt p.val := if p.val = 2 then 2 else 0

/-- Every prime residue of the witness vanishes, while its residue modulo four is two. -/
theorem prime_zero_mod_four_two :
    let x := profinitePadicEquiv.symm twoSupported
    towerRestriction primorialModulus x = 0 ∧
      reduce (primePowerModulus ⟨2, Nat.prime_two⟩ 2) x = 2 := by
  dsimp only
  constructor
  · apply primorialTowerEquiv.injective
    rw [map_zero]
    funext p
    change primorialPrimeMap (towerRestriction primorialModulus _) p = 0
    rw [full_to_squarefree_apply, profinitePadicEquiv.apply_symm_apply]
    by_cases hp : p.val = 2
    · have hp2 : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext hp
      subst p
      change componentReduction (⟨2, Nat.prime_two⟩ : Nat.Primes) (2 : PadicInt 2) = 0
      exact (map_ofNat _ 2).trans (by decide : (2 : ZMod 2) = 0)
    · simp [twoSupported, hp]
  · let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    let x := profinitePadicEquiv.symm twoSupported
    have he : padicProjection p x = twoSupported p :=
      congrFun (profinitePadicEquiv.apply_symm_apply twoSupported) p
    refine (padicProjection_toZModPow p 2 x).symm.trans ?_
    rw [he]
    change PadicInt.toZModPow 2 (2 : PadicInt 2) = 2
    exact map_ofNat _ _

theorem primorialRestriction_not_injective :
    ¬ Function.Injective (towerRestriction primorialModulus) := by
  intro hi
  obtain ⟨hzero, hfour⟩ := prime_zero_mod_four_two
  have he := hi (hzero.trans (map_zero (towerRestriction primorialModulus)).symm)
  rw [he, map_zero] at hfour
  exact (by decide : (0 : ZMod (2 ^ 2)) ≠ 2) hfour

end RiemannResearch.RH.ConductorTowerCompletions

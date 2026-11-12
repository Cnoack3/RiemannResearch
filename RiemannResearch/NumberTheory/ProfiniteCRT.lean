import RiemannResearch.NumberTheory.GeneralizedCRTDescentTargets
import RiemannResearch.NumberTheory.ProfiniteGeneralizedCRT
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Profinite Chinese remainder equivalence

The inverse limit over all positive moduli is canonically the product of
the p-adic integer rings. The prime-power reductions determine the forward
map. Generalized profinite lifting gives surjectivity.

See Gareth Wilkes, Profinite Groups and Group Cohomology, Theorem 2.2.1,
https://www.dpmms.cam.ac.uk/~grw46/LectureNotes.pdf, for the statement.
NYLL's PadicInverseLimit module gives the continuity argument via finite
p-adic reductions:
https://n-yamaguchi-0729.github.io/NYLL/modules/Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit/.
-/

noncomputable section

namespace RiemannResearch.NumberTheory.GeneralizedCRT

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- A prime-power modulus, including the trivial modulus at exponent zero. -/
def primePowerModulus (p : Nat.Primes) (k : ℕ) : PositiveModulus :=
  ⟨p.val ^ k, pow_ne_zero k p.property.ne_zero⟩

private theorem primePowers_cofinal (n : PositiveModulus) :
    ∃ s : Finset (Nat.Primes × ℕ),
      n.val ∣ s.lcm (fun q => (primePowerModulus q.1 q.2).val) := by
  classical
  let s := n.val.primeFactors.attach.image
    (fun p => ((⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩ : Nat.Primes),
      n.val.factorization p.val))
  refine ⟨s, (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr ?_⟩
  intro p k hp hpk
  cases k with
  | zero => simp
  | succ k =>
    have hpd : p ∣ n.val := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hpk
    have hpf : p ∈ n.val.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, n.property⟩
    have hk : k + 1 ≤ n.val.factorization p :=
      (hp.pow_dvd_iff_le_factorization n.property).mp hpk
    have hm : (⟨p, hp⟩, n.val.factorization p) ∈ s :=
      Finset.mem_image.mpr ⟨⟨p, hpf⟩, Finset.mem_attach _ _, rfl⟩
    have hdiv := Finset.dvd_lcm
      (f := fun q : Nat.Primes × ℕ => (primePowerModulus q.1 q.2).val) hm
    exact (pow_dvd_pow p hk).trans hdiv

/-- The canonical map from all-modulus compatible residues to one p-adic factor. -/
def padicProjection (p : Nat.Primes) : ProfiniteInt →+* PadicInt p.val :=
  PadicInt.lift (f := fun k => reduce (primePowerModulus p k)) (by
    intro k l h
    apply RingHom.ext
    intro x
    exact reduce_compatible x (m := primePowerModulus p k)
      (n := primePowerModulus p l) (pow_dvd_pow _ h))

theorem padicProjection_toZModPow (p : Nat.Primes) (k : ℕ) (x : ProfiniteInt) :
    PadicInt.toZModPow k (padicProjection p x) = reduce (primePowerModulus p k) x :=
  DFunLike.congr_fun (PadicInt.lift_spec _ k) x

private theorem continuous_padicProjection (p : Nat.Primes) :
    Continuous (padicProjection p) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p.val hε
  let r := reduce (primePowerModulus p k)
  have hr : {y | r y = r x} ∈ nhds x :=
    ((isOpen_discrete {r x}).preimage (continuous_reduce _)).mem_nhds rfl
  apply Filter.mem_of_superset hr
  intro y hy
  change padicProjection p y ∈ Metric.closedBall (padicProjection p x) ε
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply le_trans _ hk.le
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow k,
    RingHom.mem_ker, map_sub, sub_eq_zero, padicProjection_toZModPow, padicProjection_toZModPow]
  exact hy

private def toPadicProduct : ProfiniteInt →+* ((p : Nat.Primes) → PadicInt p.val) where
  toFun x p := padicProjection p x
  map_zero' := funext fun p => map_zero (padicProjection p)
  map_one' := funext fun p => map_one (padicProjection p)
  map_add' x y := funext fun p => map_add (padicProjection p) x y
  map_mul' x y := funext fun p => map_mul (padicProjection p) x y

private theorem toPadicProduct_injective : Function.Injective toPadicProduct := by
  intro x y hxy
  apply profiniteInt_ext_of_lcm_cofinal (fun q : Nat.Primes × ℕ =>
    primePowerModulus q.1 q.2) primePowers_cofinal
  rintro ⟨p, k⟩
  rw [← padicProjection_toZModPow, ← padicProjection_toZModPow]
  exact congrArg (PadicInt.toZModPow k) (congrFun hxy p)

private theorem toPadicProduct_surjective : Function.Surjective toPadicProduct := by
  intro y
  let m (q : Nat.Primes × ℕ) := primePowerModulus q.1 q.2
  let a (q : Nat.Primes × ℕ) : ℤ := ((PadicInt.toZModPow q.2 (y q.1)).val : ℤ)
  have ha (p : Nat.Primes) (k : ℕ) :
      (a (p, k) : ZMod (p.val ^ k)) = PadicInt.toZModPow k (y p) := by
    let : NeZero (p.val ^ k) := ⟨pow_ne_zero k p.property.ne_zero⟩
    change (((PadicInt.toZModPow k (y p)).val : ℤ) : ZMod (p.val ^ k)) = _
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  have hsame (p : Nat.Primes) {k l : ℕ} (hkl : k ≤ l) :
      Int.ModEq (Int.ofNat (p.val ^ k)) (a (p, k)) (a (p, l)) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    have h := congrArg (ZMod.castHom (pow_dvd_pow p.val hkl) (ZMod (p.val ^ k))) (ha p l)
    rw [map_intCast] at h
    rw [ha p k, h]
    exact (DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow k l hkl) (y p)).symm
  have hcompat : ∀ i j, Int.ModEq ((m i).val.gcd (m j).val : ℤ) (a i) (a j) := by
    rintro ⟨p, k⟩ ⟨q, l⟩
    change Int.ModEq (Int.ofNat ((p.val ^ k).gcd (q.val ^ l))) (a (p, k)) (a (q, l))
    by_cases hpq : p = q
    · subst q
      rcases le_total k l with hkl | hlk
      · rw [Nat.gcd_eq_left (pow_dvd_pow p.val hkl)]
        exact hsame p hkl
      · rw [Nat.gcd_eq_right (pow_dvd_pow p.val hlk)]
        exact (hsame p hlk).symm
    · have hcop := (Nat.coprime_primes p.property q.property).2
        (fun h => hpq (Subtype.ext h))
      have hpow : (p.val ^ k).gcd (q.val ^ l) = 1 := hcop.pow k l
      rw [hpow]
      simp [Int.ModEq]
  obtain ⟨x, hx⟩ := (exists_profiniteInt_iff_pairwise m a).mpr hcompat
  refine ⟨x, funext fun p => PadicInt.ext_of_toZModPow.mp (fun k => ?_)⟩
  change PadicInt.toZModPow k (padicProjection p x) = _
  rw [padicProjection_toZModPow]
  exact (hx (p, k)).trans (ha p k)

/-- The full Chinese remainder ring equivalence with all p-adic factors. -/
def profinitePadicEquiv : ProfiniteInt ≃+* ((p : Nat.Primes) → PadicInt p.val) :=
  RingEquiv.ofBijective toPadicProduct ⟨toPadicProduct_injective, toPadicProduct_surjective⟩

theorem profinitePadicEquiv_apply (x : ProfiniteInt) (p : Nat.Primes) :
    profinitePadicEquiv x p = padicProjection p x := rfl

/-- The canonical profinite CRT is continuous in both directions. -/
theorem isTopologicalRingCRT_profinitePadicEquiv : IsTopologicalRingCRT profinitePadicEquiv := by
  have h : Continuous profinitePadicEquiv.toEquiv :=
    continuous_pi fun p => continuous_padicProjection p
  exact ⟨h, h.continuous_symm_of_equiv_compact_to_t2⟩

open Filter
open scoped Topology

/-- The equivalent product criterion retains every prime-power depth. -/
theorem tendsto_iff_padicProjection {α : Type*} {l : Filter α}
    (f : α → ProfiniteInt) (x : ProfiniteInt) :
    Tendsto f l (𝓝 x) ↔
      ∀ p : Nat.Primes, Tendsto (fun i => padicProjection p (f i)) l (𝓝 (padicProjection p x)) := by
  constructor
  · intro h p
    exact ((continuous_apply p).comp
      isTopologicalRingCRT_profinitePadicEquiv.1).continuousAt.tendsto.comp h
  · intro h
    have hh : Tendsto (fun i => profinitePadicEquiv (f i)) l
        (𝓝 (profinitePadicEquiv x)) := tendsto_pi_nhds.mpr h
    have ht := isTopologicalRingCRT_profinitePadicEquiv.2.continuousAt.tendsto.comp hh
    simpa only [Function.comp_def, profinitePadicEquiv.symm_apply_apply] using ht

end RiemannResearch.NumberTheory.GeneralizedCRT

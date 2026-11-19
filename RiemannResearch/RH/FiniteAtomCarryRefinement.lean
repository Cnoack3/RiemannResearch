import RiemannResearch.RH.FiniteAtomCarryCRT
import RiemannResearch.RH.FiniteCarryRamanujanDictionary
import RiemannResearch.RH.UniversalCarryRamanujanSynthesis
import Mathlib.Data.ZMod.Basic

/-!
# Refinement of finite divisor-stage atom/carry coordinates

Source: user-provided atom/carry CRT agenda, §14.7.1. A divisor-stage inclusion
extends coefficients by zero. The canonical CRT rows and the actual coefficient
involution commute with this inclusion. Synthesis on residue classes commutes
with pullback along the quotient ring map. Nontrivial packet coordinates of the
same function at the larger period are uniquely determined by zero extension.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.FiniteAtomCarryCRT
open ArithmeticCumulative Pareto FiniteCarryRamanujanDictionary
open RiemannResearch.NumberTheory.PrimePowerCRT
open RiemannResearch.CategoryTheory.AtomCarryPresentation

variable {L M : ℕ+}

private theorem refineDivisor (h : (L : ℕ) ∣ (M : ℕ)) {d : ℕ}
    (hd : d ∈ (L : ℕ).divisors) : d ∈ (M : ℕ).divisors :=
  Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans h, M.ne_zero⟩

def primeEmbedding (h : (L : ℕ) ∣ (M : ℕ)) : PrimeIndex L ↪ PrimeIndex M where
  toFun i := ⟨i.val, Finset.mem_filter.mpr
    ⟨refineDivisor h (Finset.mem_filter.mp i.property).1, (Finset.mem_filter.mp i.property).2⟩⟩
  inj' _ _ hij := Subtype.ext (congrArg (fun k : PrimeIndex M => k.val) hij)

def mixedEmbedding (h : (L : ℕ) ∣ (M : ℕ)) : MixedIndex L ↪ MixedIndex M where
  toFun j := ⟨j.val, Finset.mem_filter.mpr
    ⟨refineDivisor h (Finset.mem_filter.mp j.property).1, (Finset.mem_filter.mp j.property).2⟩⟩
  inj' _ _ hij := Subtype.ext (congrArg (fun k : MixedIndex M => k.val) hij)

/-- Zero extension on a finite family of coefficient labels. -/
def extendCoefficients {ι κ : Type*} [Fintype ι] [DecidableEq κ] (e : ι ↪ κ)
    (x : ι → ℝ) (k : κ) : ℝ := ∑ i, if e i = k then x i else 0

private theorem extend_at {ι κ : Type*} [Fintype ι] [DecidableEq κ] (e : ι ↪ κ)
    (x : ι → ℝ) (i : ι) : extendCoefficients e x (e i) = x i := by
  classical
  simp [extendCoefficients, e.injective.eq_iff]

private theorem extend_outside {ι κ : Type*} [Fintype ι] [DecidableEq κ] (e : ι ↪ κ)
    (x : ι → ℝ) (k : κ) (hk : k ∉ Set.range e) : extendCoefficients e x k = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun he => hk ⟨i, he⟩)

private theorem sum_extend_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (e : ι ↪ κ) (x : ι → ℝ) (f : κ → ℝ) :
    ∑ k, extendCoefficients e x k * f k = ∑ i, x i * f (e i) := by
  classical
  simp only [extendCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

@[simp] theorem rowCoefficients_refine (h : (L : ℕ) ∣ (M : ℕ))
    (j : MixedIndex L) (i : PrimeIndex L) :
    rowCoefficients M (mixedEmbedding h j) (primeEmbedding h i) = rowCoefficients L j i := by
  unfold rowCoefficients
  apply Finset.sum_congr rfl
  intro p _
  have he : factorIndex M (mixedEmbedding h j) p = primeEmbedding h (factorIndex L j p) := rfl
  simp only [he, EmbeddingLike.apply_eq_iff_eq]
  rfl

theorem rowCoefficients_refine_outside (h : (L : ℕ) ∣ (M : ℕ)) (j : MixedIndex L)
    (k : PrimeIndex M) (hk : k ∉ Set.range (primeEmbedding h)) :
    rowCoefficients M (mixedEmbedding h j) k = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply if_neg
  intro he
  apply hk
  exact ⟨factorIndex L j p, he.symm⟩

abbrev StageCoefficients (L : ℕ+) := (PrimeIndex L → ℝ) × (MixedIndex L → ℝ)

def refineCoefficients (h : (L : ℕ) ∣ (M : ℕ)) (x : StageCoefficients L) :
    StageCoefficients M :=
  (extendCoefficients (primeEmbedding h) x.1, extendCoefficients (mixedEmbedding h) x.2)

theorem refineCoefficients_injective (h : (L : ℕ) ∣ (M : ℕ)) :
    Function.Injective (refineCoefficients h) := by
  intro x y he
  apply Prod.ext
  · funext i
    have hi := congrArg (fun z : StageCoefficients M => z.1 (primeEmbedding h i)) he
    simpa only [refineCoefficients, extend_at] using hi
  · funext j
    have hj := congrArg (fun z : StageCoefficients M => z.2 (mixedEmbedding h j)) he
    simpa only [refineCoefficients, extend_at] using hj

/-- The coefficient-side involution of the finite presentation is natural in the period. -/
theorem crtEquiv_refine (h : (L : ℕ) ∣ (M : ℕ)) (x : StageCoefficients L) :
    crtEquiv (coefficientSynthesis (rowCoefficients M)) (refineCoefficients h x) =
      refineCoefficients h (crtEquiv (coefficientSynthesis (rowCoefficients L)) x) := by
  classical
  apply Prod.ext
  · funext k
    change extendCoefficients (primeEmbedding h) x.1 k +
      (∑ j, extendCoefficients (mixedEmbedding h) x.2 j * rowCoefficients M j k) =
      extendCoefficients (primeEmbedding h)
        (fun i => x.1 i + ∑ j, x.2 j * rowCoefficients L j i) k
    rw [sum_extend_mul]
    by_cases hk : k ∈ Set.range (primeEmbedding h)
    · obtain ⟨i, rfl⟩ := hk
      simp only [extend_at, rowCoefficients_refine]
    · simp only [extend_outside _ _ _ hk, rowCoefficients_refine_outside h _ _ hk,
        mul_zero, Finset.sum_const_zero, add_zero]
  · funext k
    change -extendCoefficients (mixedEmbedding h) x.2 k =
      extendCoefficients (mixedEmbedding h) (fun j => -x.2 j) k
    by_cases hk : k ∈ Set.range (mixedEmbedding h)
    · obtain ⟨j, rfl⟩ := hk
      simp only [extend_at]
    · simp only [extend_outside _ _ _ hk, neg_zero]

/-- Pullback along the canonical quotient of residue rings. -/
def pullResidue (h : (L : ℕ) ∣ (M : ℕ)) (f : ZMod L → ℝ) (z : ZMod M) : ℝ :=
  f (ZMod.castHom h (ZMod L) z)

private theorem reduction_val (h : (L : ℕ) ∣ (M : ℕ)) (z : ZMod M) :
    (ZMod.castHom h (ZMod L) z).val = z.val % L := by
  have he := congrArg (ZMod.castHom h (ZMod L)) (ZMod.natCast_zmod_val z)
  rw [map_natCast] at he
  rw [← he, ZMod.val_natCast]

private theorem fraction_reduction (h : (L : ℕ) ∣ (M : ℕ)) {d : ℕ} (hd : d ∣ L)
    (z : ZMod M) :
    residueFraction d (ZMod.castHom h (ZMod L) z).val = residueFraction d z.val := by
  simp only [residueFraction, reduction_val, Nat.mod_mod_of_dvd _ hd]

private theorem carry_reduction (h : (L : ℕ) ∣ (M : ℕ)) {d : ℕ} (hd : d ∣ L)
    (z : ZMod M) : canonicalCarry d (ZMod.castHom h (ZMod L) z).val =
      canonicalCarry d z.val := by
  unfold canonicalCarry
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [fraction_reduction h ((modulus_dvd d p).trans hd)]

def residueAtomSynthesis (L : ℕ+) (x : StageCoefficients L) (z : ZMod L) : ℝ :=
  (∑ i, x.1 i * primeAtom L i z.val) + ∑ j, x.2 j * mixedAtom L j z.val

def residueCarrySynthesis (L : ℕ+) (x : StageCoefficients L) (z : ZMod L) : ℝ :=
  (∑ i, x.1 i * primeAtom L i z.val) + ∑ j, x.2 j * carryVector L j z.val

theorem residueAtomSynthesis_refine (h : (L : ℕ) ∣ (M : ℕ)) (x : StageCoefficients L) :
    residueAtomSynthesis M (refineCoefficients h x) =
      pullResidue h (residueAtomSynthesis L x) := by
  funext z
  dsimp only [residueAtomSynthesis, pullResidue, refineCoefficients]
  rw [sum_extend_mul, sum_extend_mul]
  simp only [primeAtom, mixedAtom]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    rw [fraction_reduction h (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp i.property).1)] <;> rfl

theorem residueCarrySynthesis_refine (h : (L : ℕ) ∣ (M : ℕ)) (x : StageCoefficients L) :
    residueCarrySynthesis M (refineCoefficients h x) =
      pullResidue h (residueCarrySynthesis L x) := by
  funext z
  dsimp only [residueCarrySynthesis, pullResidue, refineCoefficients]
  rw [sum_extend_mul, sum_extend_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change _ = _ * residueFraction i.val _
    rw [fraction_reduction h (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp i.property).1)]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    change _ = _ * (canonicalCarry j.val _ : ℝ)
    rw [carry_reduction h (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp j.property).1)]
    rfl

/-- Zero extension preserves the integrated-packet synthesis, including the
(invisible) coefficient at conductor one. -/
theorem packetSynthesis_refine (h : (L : ℕ) ∣ (M : ℕ)) (a : ℕ → ℝ) (n : ℕ) :
    (∑ q ∈ (L : ℕ).divisors, a q * ramanujanPacket q n) =
      ∑ q ∈ (M : ℕ).divisors, (if q ∣ (L : ℕ) then a q else 0) * ramanujanPacket q n := by
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have he : (M : ℕ).divisors.filter (fun t => t ∣ (L : ℕ)) = (L : ℕ).divisors := by
    ext t
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro ht
      exact ⟨ht.2, L.ne_zero⟩
    · intro ht
      exact ⟨⟨ht.1.trans h, M.ne_zero⟩, ht.1⟩
  rw [he]

/-- For any common expansion, uniqueness on one larger period forces the old
nontrivial packet coefficients to persist and the new ones to vanish. -/
theorem packetCoordinates_refine (h : (L : ℕ) ∣ (M : ℕ)) (a b : ℕ → ℝ)
    (hab : ∀ n < (M : ℕ), (∑ q ∈ (L : ℕ).divisors, a q * ramanujanPacket q n) =
      ∑ q ∈ (M : ℕ).divisors, b q * ramanujanPacket q n)
    {q : ℕ} (hq : q ∈ (M : ℕ).divisors) (h1 : 1 < q) :
    b q = if q ∣ (L : ℕ) then a q else 0 := by
  apply packet_coefficients_unique_on_period M M.pos b (fun t => if t ∣ (L : ℕ) then a t else 0)
    _ q hq h1
  intro n hn
  rw [← hab n hn]
  exact packetSynthesis_refine h a n

/-- The intrinsic divisor-stage row of a literal canonical carry, extended to
any larger period. In particular, a new divisor has zero coefficient even when
it is mixed. -/
theorem canonicalCarry_packetCoordinates_refine (d : ℕ+) (h : (d : ℕ) ∣ (M : ℕ))
    (b : ℕ → ℝ) (hb : ∀ n < (M : ℕ), (canonicalCarry d n : ℝ) =
      ∑ t ∈ (M : ℕ).divisors, b t * ramanujanPacket t n)
    {q : ℕ} (hq : q ∈ (M : ℕ).divisors) (h1 : 1 < q) :
    b q = if q ∣ (d : ℕ) then
      (∑ p ∈ (d : ℕ).primeFactors, if q ∣ modulus d p then
        (coefficient d p : ℝ) / (modulus d p : ℝ) else 0) - 1 / (d : ℝ) else 0 := by
  apply packetCoordinates_refine h _ _ _ hq h1
  intro n hn
  exact (CRTCarryRamanujan.canonicalCarry_packet_expansion d d.pos n).symm.trans (hb n hn)

/-- For a realized universal word with period supported at the old stage, even
an arbitrary packet expansion recovered from the larger stage has precisely the
old coordinates and zeros. The exceptional zero packet at one is excluded. -/
theorem word_packetCoordinates_refine (h : (L : ℕ) ∣ (M : ℕ))
    (w : UniversalAtomCarry.Word)
    (hperiod : ∀ d ∈ (UniversalAtomCarry.eliminate w).support, d.val ∣ (L : ℕ))
    (b : ℕ → ℝ) (hb : ∀ n < (M : ℕ), UniversalAtomCarry.synthesis w n =
      ∑ t ∈ (M : ℕ).divisors, b t * ramanujanPacket t n)
    {q : ℕ} (hq : q ∈ (M : ℕ).divisors) (h1 : 1 < q) :
    b q = if q ∣ (L : ℕ) then UniversalAtomCarry.wordPacketCoefficient w q else 0 := by
  apply packetCoordinates_refine h _ _ _ hq h1
  intro n hn
  exact (UniversalAtomCarry.word_packet_expansion w L L.pos hperiod n).symm.trans (hb n hn)

end RiemannResearch.RH.FiniteAtomCarryCRT

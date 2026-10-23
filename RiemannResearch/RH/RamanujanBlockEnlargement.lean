import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.Analysis.FiniteGramScreenedInverse
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary finite block enlargement in the integrated packet dictionary

Source: user-requested next ten Ramanujan transfers, 23 October 2026.
The complete screened-capacity and inverse-source identities are instantiated
with actual arithmetic packets. Independence of all distinct legal conductors
is proved; invertibility of the screened Gram matrix is not assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanBlock
open Pareto RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def family (q : ι → ℕ) : ι → ThresholdHilbert :=
  fun i => ramanujanPacketHilbert (q i)

/-- Any distinct finite legal conductors form an independent packet family. -/
theorem family_independent (q : ι → ℕ) (hq : ∀ i, 1 < q i)
    (hinj : Function.Injective q) : LinearIndependent ℝ (family q) := by
  classical
  let N : ℕ := Finset.univ.sup q
  let j : ι → Fin N := fun i => ⟨q i - 2, by
    have hi := hq i
    have hle : q i ≤ N := Finset.le_sup (Finset.mem_univ i)
    omega⟩
  have hj : Function.Injective j := by
    intro i k he
    apply hinj
    have hv := congrArg Fin.val he
    have hi := hq i
    have hk := hq k
    change q i - 2 = q k - 2 at hv
    omega
  have h := (finitePacket_independent N).comp j hj
  have he : (fun i : Fin N => ramanujanPacketHilbert (i.val + 2)) ∘ j = family q := by
    funext i
    change ramanujanPacketHilbert (q i - 2 + 2) = ramanujanPacketHilbert (q i)
    congr 1
    have hi := hq i
    omega
  rw [he] at h
  exact h

theorem joined_independent (q : ι → ℕ) (p : κ → ℕ)
    (hq : ∀ i, 1 < q i) (hp : ∀ j, 1 < p j)
    (hjoin : Function.Injective (Sum.elim q p)) :
    LinearIndependent ℝ (Sum.elim (family q) (family p)) := by
  have h := family_independent (Sum.elim q p)
    (by intro i; cases i with
        | inl i => exact hq i
        | inr j => exact hp j) hjoin
  have he : family (Sum.elim q p) = Sum.elim (family q) (family p) := by
    funext i
    cases i <;> rfl
  rwa [he] at h

def source (q : ι → ℕ) : ι → ℝ :=
  fun i => ArithmeticFunction.vonMangoldt (q i)

theorem source_eq_cross (q : ι → ℕ) : source q = cross (family q) hilbertOne := by
  funext i
  exact (packet_inner_one (q i)).symm

variable (q : ι → ℕ) (p : κ → ℕ)
  (hq : ∀ i, 1 < q i) (hp : ∀ j, 1 < p j)
  (hinj : Function.Injective q) (hjoin : Function.Injective (Sum.elim q p))

def screenedFamily : κ → ThresholdHilbert :=
  screened (family_independent q hq hinj) (family p)

include hp hjoin in
theorem screened_independent : LinearIndependent ℝ (screenedFamily q p hq hinj) :=
  screened_linearIndependent (family_independent q hq hinj) (family p)
    (joined_independent q p hq hp hjoin)

/-- The full Schur matrix, retaining all old/new mixed entries. -/
theorem screened_gram (i j : κ) :
    inner ℝ (screenedFamily q p hq hinj i) (screenedFamily q p hq hinj j) =
      inner ℝ (family p i) (family p j) -
        ∑ k, inverseCoeff (family_independent q hq hinj) (family p i) k *
          cross (family q) (family p j) k :=
  screened_gram_entry (family_independent q hq hinj) (family p) i j

include hp hjoin in
theorem screened_gram_det_pos [DecidableEq κ] :
    0 < (gramMatrix (screenedFamily q p hq hinj)).det :=
  gramMatrix_det_pos (screened_independent q p hq hp hinj hjoin)

/-- Both inverse coefficient blocks are explicit, including the signed change
to every old coefficient. Sources need not be constant-target means. -/
theorem coefficients_block_exact (b : ι → ℝ) (d : κ → ℝ) :
    inverseSource (joined_independent q p hq hp hjoin) (Sum.elim b d) =
      Sum.elim
        (inverseSource (family_independent q hq hinj) b -
          ∑ j, inverseSource (screened_independent q p hq hp hinj hjoin)
            (screenedSource (family_independent q hq hinj) (family p) b d) j •
              inverseCoeff (family_independent q hq hinj) (family p j))
        (inverseSource (screened_independent q p hq hp hinj hjoin)
          (screenedSource (family_independent q hq hinj) (family p) b d)) :=
  inverseSource_screened_sum (family_independent q hq hinj) (family p)
    (screened_independent q p hq hp hinj hjoin)
    (joined_independent q p hq hp hjoin) b d

theorem capacity_block_exact (b : ι → ℝ) (d : κ → ℝ) :
    capacity (joined_independent q p hq hp hjoin) (Sum.elim b d) =
      capacity (family_independent q hq hinj) b +
        capacity (screened_independent q p hq hp hinj hjoin)
          (screenedSource (family_independent q hq hinj) (family p) b d) :=
  capacity_screened_add (family_independent q hq hinj) (family p)
    (screened_independent q p hq hp hinj hjoin)
    (joined_independent q p hq hp hjoin) b d

/-- Strict gain is equivalent to the entire screened source being nonzero. -/
theorem capacity_block_strict_iff (b : ι → ℝ) (d : κ → ℝ) :
    capacity (family_independent q hq hinj) b <
      capacity (joined_independent q p hq hp hjoin) (Sum.elim b d) ↔
    screenedSource (family_independent q hq hinj) (family p) b d ≠ 0 := by
  rw [capacity_block_exact q p hq hp hinj hjoin]
  constructor
  · intro h hz
    simp [hz, capacity] at h
  · intro h
    have hg := capacity_pos (screened_independent q p hq hp hinj hjoin) _ h
    linarith

theorem constant_screened_source (j : κ) :
    screenedSource (family_independent q hq hinj) (family p) (source q) (source p) j =
      inner ℝ (family p j)
        (hilbertOne - minimumVector (family_independent q hq hinj) (source q)) := by
  rw [inner_sub_right]
  change source p j - _ = _
  rw [show inner ℝ (family p j) hilbertOne = source p j from packet_inner_one (p j)]

/-- Actual constant-target approximation error after the entire block is added. -/
theorem constant_error_block_exact :
    ‖hilbertOne - minimumVector (joined_independent q p hq hp hjoin)
        (Sum.elim (source q) (source p))‖ ^ 2 =
      1 - capacity (family_independent q hq hinj) (source q) -
        capacity (screened_independent q p hq hp hinj hjoin)
          (screenedSource (family_independent q hq hinj) (family p)
            (source q) (source p)) := by
  have hs : Sum.elim (source q) (source p) =
      cross (Sum.elim (family q) (family p)) hilbertOne := by
    funext i
    cases i with
    | inl i => exact (packet_inner_one (q i)).symm
    | inr j => exact (packet_inner_one (p j)).symm
  have he := residual_schur_value (joined_independent q p hq hp hjoin) hilbertOne
  unfold inverseCoeff at he
  rw [← hs] at he
  change ‖hilbertOne - minimumVector (joined_independent q p hq hp hjoin)
      (Sum.elim (source q) (source p))‖ ^ 2 =
    ‖hilbertOne‖ ^ 2 -
      capacity (joined_independent q p hq hp hjoin) (Sum.elim (source q) (source p)) at he
  rw [hilbertOne_norm_sq, capacity_block_exact q p hq hp hinj hjoin] at he
  linarith

end RiemannResearch.RH.RamanujanBlock

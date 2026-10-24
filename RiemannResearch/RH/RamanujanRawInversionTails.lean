import RiemannResearch.Analysis.SignedInverseTails
import RiemannResearch.RH.RamanujanCoefficientInversion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Raw packet coefficients: exact inversion and the missing infinite-tail condition

Source: the verified two-sided finite inversion, extended by a signed-tail
limit argument. A raw packet coefficient is not a continuous conductor
coefficient. Its prospective limit is an inverse multiple series, not -μ(d).
The ordered series is allowed to converge conditionally. No interchange of
an infinite inverse sum with the optimization limit is presumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanRawInversionTails
open Pareto RamanujanCoefficientInversion
open RiemannResearch.Analysis.SignedInverseTails

/-- Index `d` represents packet conductor `d+2`; coefficients absent from a
finite dictionary are extended by zero. -/
def rawCoefficient (a : (n : ℕ) → Fin n → ℝ) (n d : ℕ) : ℝ :=
  if h : d < n then a n ⟨d, h⟩ else 0

/-- The inverse has a divisor indicator and a reciprocal conductor factor.
There is no further Möbius factor in this inverse transform. -/
def inverseTerm (c : ℕ → ℝ) (d j : ℕ) : ℝ :=
  if d + 2 ∣ j + 2 then c (j + 2) / ((j + 2 : ℕ) : ℝ) else 0

/-- The actual finite inverse row, extended by zero beyond its dictionary. -/
def inverseRow (C : ℕ → ℕ → ℝ) (n d j : ℕ) : ℝ :=
  if j < n then inverseTerm (C n) d j else 0

/-- The entire omitted signed inverse sum, with no discarded conductors. -/
def inverseTail (C : ℕ → ℕ → ℝ) (n d K : ℕ) : ℝ :=
  ∑' j : {j : ℕ // j ∉ Finset.range K}, inverseRow C n d j

def TailCondition {α : Type*} (C : ℕ → ℕ → ℝ) (d : ℕ)
    (N : α → ℕ) (l : Filter α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ K : ℕ, J ≤ K →
    ∀ᶠ i in l, ‖inverseTail C (N i) d K‖ < ε

theorem inverseRow_summable (C : ℕ → ℕ → ℝ) (n d : ℕ) :
    Summable (inverseRow C n d) := by
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro j hj
  simp only [Finset.mem_range] at hj
  simp only [inverseRow, if_neg hj]

theorem inverseRow_tsum (C : ℕ → ℕ → ℝ) (n d : ℕ) :
    (∑' j, inverseRow C n d j) = ∑ j ∈ Finset.range n, inverseRow C n d j := by
  apply tsum_eq_sum
  intro j hj
  simp only [Finset.mem_range] at hj
  simp only [inverseRow, if_neg hj]

/-- In particular the complete tail is exactly the finite omitted multiple sum. -/
theorem inverseTail_eq_finite (C : ℕ → ℕ → ℝ) (n d K : ℕ) :
    inverseTail C n d K =
      ∑ j ∈ (Finset.range n).filter (fun j => K ≤ j), inverseTerm (C n) d j := by
  calc
    inverseTail C n d K =
        ∑' j, ({j : ℕ | j ∉ Finset.range K}.indicator (inverseRow C n d)) j :=
      tsum_subtype {j : ℕ | j ∉ Finset.range K} (inverseRow C n d)
    _ = ∑ j ∈ Finset.range n,
        ({j : ℕ | j ∉ Finset.range K}.indicator (inverseRow C n d)) j := by
      apply tsum_eq_sum
      intro j hj
      have hn : ¬j < n := by simpa only [Finset.mem_range] using hj
      simp [Set.indicator, inverseRow, hn]
    _ = ∑ j ∈ (Finset.range n).filter (fun j => K ≤ j), inverseTerm (C n) d j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Set.indicator, inverseRow, Finset.mem_range.mp hj, Finset.mem_range, not_lt]

/-- Any exact finite inverse remains exact after extending absent coefficients
by zero; this includes every cutoff and every packet conductor. -/
theorem rawCoefficient_eq_inverseRow (a : (n : ℕ) → Fin n → ℝ)
    (C : ℕ → ℕ → ℝ)
    (hinv : ∀ n (i : Fin n), a n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then C n (j.val + 2) / ((j.val + 2 : ℕ) : ℝ) else 0)
    (n d : ℕ) : rawCoefficient a n d = ∑' j, inverseRow C n d j := by
  rw [inverseRow_tsum]
  by_cases hd : d < n
  · rw [rawCoefficient, dif_pos hd, hinv]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [inverseRow, inverseTerm, if_pos j.isLt]
  · rw [rawCoefficient, dif_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have hnd : ¬d + 2 ∣ j + 2 := by
      intro h
      have hle := Nat.le_of_dvd (by omega : 0 < j + 2) h
      omega
    simp only [inverseRow, inverseTerm, if_pos hjn, if_neg hnd]

/-- Exact signed remainder; no approximation or limiting operation occurs. -/
theorem rawCoefficient_head_tail (a : (n : ℕ) → Fin n → ℝ)
    (C : ℕ → ℕ → ℝ)
    (hinv : ∀ n (i : Fin n), a n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then C n (j.val + 2) / ((j.val + 2 : ℕ) : ℝ) else 0)
    (n d K : ℕ) :
    rawCoefficient a n d = (∑ j ∈ Finset.range K, inverseRow C n d j) +
      inverseTail C n d K := by
  rw [rawCoefficient_eq_inverseRow a C hinv]
  exact ((inverseRow_summable C n d).sum_add_tsum_subtype_compl (Finset.range K)).symm

theorem inverseRow_tendsto (C : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hcoord : ∀ m : ℕ, 1 < m → Tendsto (fun n => C n m) atTop (𝓝 (c m)))
    (d j : ℕ) :
    Tendsto (fun n => inverseRow C n d j) atTop (𝓝 (inverseTerm c d j)) := by
  have ht : Tendsto (fun n => inverseTerm (C n) d j) atTop
      (𝓝 (inverseTerm c d j)) := by
    by_cases hd : d + 2 ∣ j + 2
    · simp only [inverseTerm, if_pos hd]
      exact (hcoord (j + 2) (by omega)).div_const _
    · simp only [inverseTerm, if_neg hd]
      exact tendsto_const_nhds
  apply ht.congr'
  filter_upwards [eventually_gt_atTop j] with n hn
  simp only [inverseRow, if_pos hn]

/-- The infinite inverse needs exactly the asymptotic complete signed-tail
condition, once the ordered candidate inverse series has a limit. -/
theorem rawCoefficient_tendsto_iff (a : (n : ℕ) → Fin n → ℝ)
    (C : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hinv : ∀ n (i : Fin n), a n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then C n (j.val + 2) / ((j.val + 2 : ℕ) : ℝ) else 0)
    (hcoord : ∀ m : ℕ, 1 < m → Tendsto (fun n => C n m) atTop (𝓝 (c m)))
    (d : ℕ) (L : ℝ)
    (hseries : Tendsto (fun K => ∑ j ∈ Finset.range K, inverseTerm c d j) atTop (𝓝 L))
    {α : Type*} {l : Filter α} (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => rawCoefficient a (N i) d) l (𝓝 L) ↔ TailCondition C d N l := by
  have he (i : α) (K : ℕ) : rawCoefficient a (N i) d -
      (∑ j ∈ Finset.range K, inverseRow C (N i) d j) = inverseTail C (N i) d K := by
    have h := rawCoefficient_head_tail a C hinv (N i) d K
    linarith
  have h := tendsto_iff_asymptoticTails (fun i => rawCoefficient a (N i) d)
    (fun i j => inverseRow C (N i) d j) (inverseTerm c d) L
    (fun j => (inverseRow_tendsto C c hcoord d j).comp hN) hseries
  simpa only [AsymptoticTails, TailCondition, he] using h

/-- A summable dominator is a sufficient alternative to checking signed tails.
This theorem assumes that dominator explicitly; it never infers it from
convergence of the individual continuous coefficients. -/
theorem rawCoefficient_tendsto_of_dominated (a : (n : ℕ) → Fin n → ℝ)
    (C : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hinv : ∀ n (i : Fin n), a n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then C n (j.val + 2) / ((j.val + 2 : ℕ) : ℝ) else 0)
    (hcoord : ∀ m : ℕ, 1 < m → Tendsto (fun n => C n m) atTop (𝓝 (c m)))
    (d : ℕ) (u : ℕ → ℝ) (hu : Summable u)
    (hbound : ∀ᶠ n in atTop, ∀ j, ‖inverseRow C n d j‖ ≤ u j) :
    Tendsto (fun n => rawCoefficient a n d) atTop (𝓝 (∑' j, inverseTerm c d j)) := by
  have ht := tendsto_tsum_of_dominated_convergence hu
    (inverseRow_tendsto C c hcoord d) hbound
  simpa only [rawCoefficient_eq_inverseRow a C hinv] using ht

private theorem pareto_finite_inverse (n : ℕ) (i : Fin n) :
    RamanujanCanonicalOptimizer.packetCoefficients n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then
        RamanujanCanonicalOptimizer.packetMultipleCoefficient n (j.val + 2) /
          ((j.val + 2 : ℕ) : ℝ) else 0 := by
  rw [canonical_packetCoefficient_formula]
  apply Finset.sum_congr rfl
  intro j _
  rw [RamanujanCanonicalOptimizer.packetMultipleCoefficient_eq n (j.val + 2) (by omega)]

private theorem q_finite_inverse (n : ℕ) (i : Fin n) :
    QRamanujanCanonicalOptimizer.packetCoefficients n i = ∑ j : Fin n,
      if i.val + 2 ∣ j.val + 2 then
        QRamanujanCanonicalOptimizer.packetCoordinate n (j.val + 2) /
          ((j.val + 2 : ℕ) : ℝ) else 0 := by
  rw [q_canonical_packetCoefficient_formula]
  apply Finset.sum_congr rfl
  intro j _
  rw [QRamanujanCanonicalOptimizer.residueCoefficients_eq_packetCoordinate]

theorem pareto_raw_head_tail (n d K : ℕ) :
    rawCoefficient RamanujanCanonicalOptimizer.packetCoefficients n d =
      (∑ j ∈ Finset.range K,
        inverseRow RamanujanCanonicalOptimizer.packetMultipleCoefficient n d j) +
      inverseTail RamanujanCanonicalOptimizer.packetMultipleCoefficient n d K :=
  rawCoefficient_head_tail _ _ pareto_finite_inverse n d K

theorem q_raw_head_tail (n d K : ℕ) :
    rawCoefficient QRamanujanCanonicalOptimizer.packetCoefficients n d =
      (∑ j ∈ Finset.range K,
        inverseRow QRamanujanCanonicalOptimizer.packetCoordinate n d j) +
      inverseTail QRamanujanCanonicalOptimizer.packetCoordinate n d K :=
  rawCoefficient_head_tail _ _ q_finite_inverse n d K

/-- Complete characterization of Pareto raw packet stabilization. The
continuous coefficient limit is unconditional; its infinite inversion is not. -/
theorem pareto_raw_tendsto_iff_tail (d : ℕ) (L : ℝ)
    (hseries : Tendsto (fun K => ∑ j ∈ Finset.range K,
      inverseTerm CoefficientStabilization.limitCoefficient d j) atTop (𝓝 L))
    {α : Type*} {l : Filter α} (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => rawCoefficient RamanujanCanonicalOptimizer.packetCoefficients (N i) d)
      l (𝓝 L) ↔ TailCondition RamanujanCanonicalOptimizer.packetMultipleCoefficient d N l :=
  rawCoefficient_tendsto_iff _ _ _ pareto_finite_inverse
    RamanujanCanonicalOptimizer.packetMultipleCoefficient_tendsto d L hseries N hN

theorem q_raw_tendsto_iff_tail (d : ℕ) (L : ℝ)
    (hseries : Tendsto (fun K => ∑ j ∈ Finset.range K,
      inverseTerm QRamanujanCanonicalOptimizer.limitCoordinate d j) atTop (𝓝 L))
    {α : Type*} {l : Filter α} (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => rawCoefficient QRamanujanCanonicalOptimizer.packetCoefficients (N i) d)
      l (𝓝 L) ↔ TailCondition QRamanujanCanonicalOptimizer.packetCoordinate d N l :=
  rawCoefficient_tendsto_iff _ _ _ q_finite_inverse
    QRamanujanCanonicalOptimizer.packetCoordinate_tendsto d L hseries N hN

/-- Direct sufficient criterion for the actual Pareto inverse-Gram coefficients. -/
theorem pareto_raw_tendsto_of_dominated (d : ℕ) (u : ℕ → ℝ) (hu : Summable u)
    (hbound : ∀ᶠ n in atTop, ∀ j,
      ‖inverseRow RamanujanCanonicalOptimizer.packetMultipleCoefficient n d j‖ ≤ u j) :
    Tendsto (fun n => rawCoefficient RamanujanCanonicalOptimizer.packetCoefficients n d)
      atTop (𝓝 (∑' j, inverseTerm CoefficientStabilization.limitCoefficient d j)) :=
  rawCoefficient_tendsto_of_dominated _ _ _ pareto_finite_inverse
    RamanujanCanonicalOptimizer.packetMultipleCoefficient_tendsto d u hu hbound

theorem q_raw_tendsto_of_dominated (d : ℕ) (u : ℕ → ℝ) (hu : Summable u)
    (hbound : ∀ᶠ n in atTop, ∀ j,
      ‖inverseRow QRamanujanCanonicalOptimizer.packetCoordinate n d j‖ ≤ u j) :
    Tendsto (fun n => rawCoefficient QRamanujanCanonicalOptimizer.packetCoefficients n d)
      atTop (𝓝 (∑' j, inverseTerm QRamanujanCanonicalOptimizer.limitCoordinate d j)) :=
  rawCoefficient_tendsto_of_dominated _ _ _ q_finite_inverse
    QRamanujanCanonicalOptimizer.packetCoordinate_tendsto d u hu hbound

end RiemannResearch.RH.RamanujanRawInversionTails

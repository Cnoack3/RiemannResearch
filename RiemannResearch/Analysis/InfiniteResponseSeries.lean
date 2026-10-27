import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Infinite assembly for signed projection-response updates.
The orthogonal part may vanish at arbitrary indices. `Summable` is the
unconditional, finite-subset-net notion. No ordered-series substitution occurs.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.InfiniteResponseSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Orthogonal summability tolerates zero vectors and hence masked innovations. -/
theorem orthogonal_part_summable
    (K : ℕ → Submodule ℝ H)
    (hK : OrthogonalFamily ℝ (fun n => K n) (fun n => (K n).subtypeₗᵢ))
    (s : ℕ → H) (hsK : ∀ n, s n ∈ K n)
    (hs : Summable (fun n => ‖s n‖ ^ 2)) : Summable s := by
  let f : ∀ n, K n := fun n => ⟨s n, hsK n⟩
  have hf (n : ℕ) : ‖f n‖ = ‖s n‖ := Submodule.coe_norm (f n)
  have hfs : Summable (fun n => ‖f n‖ ^ 2) := by simpa only [hf] using hs
  exact (hK.summable_iff_norm_sq_summable f).mpr hfs

/-- A Cauchy--Schwarz product is absolutely summable. The proof uses the
equivalent pointwise Young inequality so that no finite-tail limit is hidden. -/
theorem correction_norm_summable
    (a d : ℕ → ℝ) (t : ℕ → H)
    (ha : Summable (fun n => (a n) ^ 2))
    (hd : Summable (fun n => (d n) ^ 2))
    (ht : ∀ n, ‖t n‖ ≤ |a n| * d n) :
    Summable (fun n => ‖t n‖) := by
  have hmajor : Summable (fun n => ((a n) ^ 2 + (d n) ^ 2) / 2) :=
    (ha.add hd).div_const 2
  apply hmajor.of_nonneg_of_le (fun n => norm_nonneg (t n))
  intro n
  have hsq := sq_nonneg (|a n| - d n)
  have habs : |a n| ^ 2 = (a n) ^ 2 := sq_abs (a n)
  have ht' := ht n
  nlinarith

/-- Both signed update series converge unconditionally, with the correction
series converging absolutely in Hilbert norm. -/
theorem response_parts_summable
    (K : ℕ → Submodule ℝ H)
    (hK : OrthogonalFamily ℝ (fun n => K n) (fun n => (K n).subtypeₗᵢ))
    (s t : ℕ → H) (hsK : ∀ n, s n ∈ K n)
    (hs : Summable (fun n => ‖s n‖ ^ 2))
    (a d : ℕ → ℝ)
    (ha : Summable (fun n => (a n) ^ 2))
    (hd : Summable (fun n => (d n) ^ 2))
    (ht : ∀ n, ‖t n‖ ≤ |a n| * d n) :
    Summable s ∧ Summable (fun n => ‖t n‖) ∧
      Summable (fun n => s n - t n) := by
  have hso := orthogonal_part_summable K hK s hsK hs
  have htn := correction_norm_summable a d t ha hd ht
  exact ⟨hso, htn, hso.sub htn.of_norm⟩

/-- Every bounded signed version of the series also converges unconditionally. -/
theorem bounded_signed_parts_summable
    (K : ℕ → Submodule ℝ H)
    (hK : OrthogonalFamily ℝ (fun n => K n) (fun n => (K n).subtypeₗᵢ))
    (s t : ℕ → H) (hsK : ∀ n, s n ∈ K n)
    (hs : Summable (fun n => ‖s n‖ ^ 2))
    (ht : Summable (fun n => ‖t n‖))
    (ε : ℕ → ℝ) (hε : ∀ n, |ε n| ≤ 1) :
    Summable (fun n => ε n • s n) ∧
      Summable (fun n => ‖ε n • t n‖) ∧
      Summable (fun n => ε n • (s n - t n)) := by
  have hn (n : ℕ) (x : H) : ‖ε n • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hε n) (norm_nonneg x)
  have hss : Summable (fun n => ‖ε n • s n‖ ^ 2) := by
    apply hs.of_nonneg_of_le (fun n => sq_nonneg _)
    intro n
    exact pow_le_pow_left₀ (norm_nonneg _) (hn n (s n)) 2
  have hso := orthogonal_part_summable K hK (fun n => ε n • s n)
    (fun n => (K n).smul_mem _ (hsK n)) hss
  have htn : Summable (fun n => ‖ε n • t n‖) :=
    ht.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hn n (t n))
  refine ⟨hso, htn, ?_⟩
  simpa only [smul_sub] using hso.sub htn.of_norm

/-- A complete diagonal budget controls the infinite variation; no physical
coordinate truncation is present in either summability hypothesis. -/
theorem variation_summable_and_tsum_le
    (δ : ℕ → H) (d : ℕ → ℝ) (C D : ℝ) (hC : 0 ≤ C)
    (hd : Summable (fun n => (d n) ^ 2))
    (hD : (∑' n, (d n) ^ 2) ≤ D)
    (hδ : ∀ n, ‖δ n‖ ^ 2 ≤ C * (d n) ^ 2) :
    Summable (fun n => ‖δ n‖ ^ 2) ∧
      (∑' n, ‖δ n‖ ^ 2) ≤ C * D := by
  have hmajor : Summable (fun n => C * (d n) ^ 2) := hd.mul_left C
  have hs : Summable (fun n => ‖δ n‖ ^ 2) :=
    hmajor.of_nonneg_of_le (fun n => sq_nonneg _) hδ
  refine ⟨hs, ?_⟩
  calc
    (∑' n, ‖δ n‖ ^ 2) ≤ ∑' n, C * (d n) ^ 2 := Summable.tsum_le_tsum hδ hs hmajor
    _ = C * ∑' n, (d n) ^ 2 := tsum_mul_left
    _ ≤ C * D := mul_le_mul_of_nonneg_left hD hC

theorem sum_response_differences (b : ℕ → H) (N M : ℕ) :
    (∑ j ∈ Finset.range M, (b (j + N + 1) - b (j + N))) =
      b (M + N) - b N := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_right_comm M 1 N]
    abel

/-- Ordered telescoping identifies the sum only after unconditional
summability has independently been proved. -/
theorem response_tail_hasSum
    (b : ℕ → H) (bLimit : H)
    (hs : Summable (fun n => b (n + 1) - b n))
    (hb : Tendsto b atTop (𝓝 bLimit)) (N : ℕ) :
    HasSum (fun j => b (j + N + 1) - b (j + N)) (bLimit - b N) := by
  have hs' : Summable (fun j => b (j + N + 1) - b (j + N)) :=
    hs.comp_injective (i := fun j : ℕ => j + N)
      (fun i j h => Nat.add_right_cancel h)
  have ht : Tendsto
      (fun M => ∑ j ∈ Finset.range M, (b (j + N + 1) - b (j + N)))
      atTop (𝓝 (bLimit - b N)) := by
    simp_rw [sum_response_differences]
    exact (hb.comp (tendsto_add_atTop_nat N)).sub tendsto_const_nhds
  have he := tendsto_nhds_unique hs'.hasSum.tendsto_sum_nat ht
  exact he ▸ hs'.hasSum

end RiemannResearch.Analysis.InfiniteResponseSeries

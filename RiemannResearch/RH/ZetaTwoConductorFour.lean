import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Exact conductor-four finite dual arithmetic

Source: user-provided argument, `Exact_Optimizer_Cancellation_20261008.tex`,
finite Möbius dual and annihilator block sections. The sums are complete:
the witness is supported on `1,2,3,4`. Their inverse-square normalizations
are respectively `30/Z`, `10/Z`, and zero. The finite sums are also identified
with the literal complete infinite inverse-square pairings. The bundled
Hilbert projection connection is a separate assembly obligation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoConductorFour

def witness : Fin 4 → ℝ := ![1, -4, -9, 16]

def atom (d : ℕ) (i : Fin 4) : ℝ := (((i.val + 1) % d : ℕ) : ℝ) / (d : ℝ)

/-- The complete finite supported dual pairing at reciprocal power `s`. -/
def rawInner (s : ℕ) (x y : Fin 4 → ℝ) : ℝ :=
  ∑ i, x i * y i / ((i.val + 1 : ℕ) : ℝ) ^ (s + 2)

theorem witness_norm : rawInner 0 witness witness = 30 := by
  norm_num [rawInner, witness, Fin.sum_univ_succ]

theorem witness_reciprocal_energy : rawInner 1 witness witness = 10 := by
  norm_num [rawInner, witness, Fin.sum_univ_succ]

theorem witness_mean_zero : rawInner 0 witness (fun _ => 1) = 0 := by
  norm_num [rawInner, witness, Fin.sum_univ_succ]

theorem witness_reciprocal_mean : rawInner 1 witness (fun _ => 1) = 5 / 12 := by
  norm_num [rawInner, witness, Fin.sum_univ_succ]

theorem witness_atom_four : rawInner 0 witness (atom 4) = -1 := by
  norm_num [rawInner, witness, atom, Fin.sum_univ_succ]

theorem witness_atom_large (d : ℕ) (hd : 5 ≤ d) :
    rawInner 0 witness (atom d) = 0 := by
  have h1 : 1 < d := by omega
  have h2 : 2 < d := by omega
  have h3 : 3 < d := by omega
  have h4 : 4 < d := by omega
  norm_num [rawInner, witness, atom, Fin.sum_univ_succ,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] <;> ring

theorem witness_atom_annihilates (d : ℕ) (hd : 2 ≤ d) (hfour : d ≠ 4) :
    rawInner 0 witness (atom d) = 0 := by
  by_cases htwo : d = 2
  · subst d
    norm_num [rawInner, witness, atom, Fin.sum_univ_succ]
  by_cases hthree : d = 3
  · subst d
    norm_num [rawInner, witness, atom, Fin.sum_univ_succ]
  exact witness_atom_large d (by omega)

theorem witness_reciprocal_atom_large (d : ℕ) (hd : 5 ≤ d) :
    rawInner 1 witness (atom d) = 0 := by
  have h1 : 1 < d := by omega
  have h2 : 2 < d := by omega
  have h3 : 3 < d := by omega
  have h4 : 4 < d := by omega
  norm_num [rawInner, witness, atom, Fin.sum_univ_succ,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] <;> ring

theorem witness_reciprocal_atom (d : ℕ) (hd : 2 ≤ d) (hfour : d ≠ 4) :
    rawInner 1 witness (atom d) =
      if d = 2 then (1 / 3 : ℝ) else if d = 3 then 1 / 12 else 0 := by
  by_cases htwo : d = 2
  · subst d
    norm_num [rawInner, witness, atom, Fin.sum_univ_succ]
  by_cases hthree : d = 3
  · subst d
    norm_num [rawInner, witness, atom, Fin.sum_univ_succ]
  rw [if_neg htwo, if_neg hthree]
  exact witness_reciprocal_atom_large d (by omega)

theorem rawInner_const_smul_right (s : ℕ) (x y : Fin 4 → ℝ) (c : ℝ) :
    rawInner s x (fun i => c * y i) = c * rawInner s x y := by
  unfold rawInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rawInner_sub_right (s : ℕ) (x y z : Fin 4 → ℝ) :
    rawInner s x (fun i => y i - z i) = rawInner s x y - rawInner s x z := by
  unfold rawInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rawInner_sum_right (s : ℕ) (x : Fin 4 → ℝ)
    (S : Finset ℕ) (y : ℕ → Fin 4 → ℝ) :
    rawInner s x (fun i => ∑ d ∈ S, y d i) = ∑ d ∈ S, rawInner s x (y d) := by
  classical
  unfold rawInner
  simp_rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_comm

/-- Exact reciprocal dual row for any finite legal dictionary excluding
conductor four. Coefficients of all larger atoms cancel completely. -/
theorem witness_optimizer_row (S : Finset ℕ) (c : ℕ → ℝ)
    (htwo : 2 ∈ S) (hthree : 3 ∈ S)
    (hlegal : ∀ d ∈ S, 2 ≤ d ∧ d ≠ 4) :
    rawInner 1 witness (fun i => 1 - ∑ d ∈ S, c d * atom d i) =
      (5 - 4 * c 2 - c 3) / 12 := by
  classical
  rw [rawInner_sub_right, witness_reciprocal_mean, rawInner_sum_right]
  have hpair : (∑ d ∈ S, rawInner 1 witness (fun i => c d * atom d i)) =
      c 2 / 3 + c 3 / 12 := by
    simp_rw [rawInner_const_smul_right]
    have hreduce : (∑ d ∈ S, c d * rawInner 1 witness (atom d)) =
        ∑ d ∈ S, ((if d = 2 then c 2 / 3 else 0) +
          (if d = 3 then c 3 / 12 else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [witness_reciprocal_atom d (hlegal d hd).1 (hlegal d hd).2]
      by_cases h2 : d = 2
      · subst d
        norm_num <;> ring
      by_cases h3 : d = 3
      · subst d
        norm_num <;> ring
      simp [h2, h3]
    rw [hreduce, Finset.sum_add_distrib]
    simp [htwo, hthree]
  rw [hpair]
  ring

theorem witness_rayleigh (Z : ℝ) (hZ : Z ≠ 0) :
    (rawInner 1 witness witness / Z) / (rawInner 0 witness witness / Z) =
      (1 / 3 : ℝ) := by
  rw [witness_reciprocal_energy, witness_norm]
  field_simp [hZ] <;> ring

/-- The exact normalized dual row; the factor `Z` is retained. -/
theorem witness_optimizer_row_normalized (S : Finset ℕ) (c : ℕ → ℝ)
    (htwo : 2 ∈ S) (hthree : 3 ∈ S)
    (hlegal : ∀ d ∈ S, 2 ≤ d ∧ d ≠ 4) (Z : ℝ) :
    rawInner 1 witness (fun i => 1 - ∑ d ∈ S, c d * atom d i) / Z =
      (5 - 4 * c 2 - c 3) / (12 * Z) := by
  rw [witness_optimizer_row S c htwo hthree hlegal]
  ring

/-- The actual sequence dual, supported exactly at positive sites `1..4`. -/
def natWitness (n : ℕ) : ℝ :=
  if n = 1 then 1 else if n = 2 then -4 else if n = 3 then -9 else
    if n = 4 then 16 else 0

/-- The complete infinite inverse-square pairing of the dual with any
sequence. No truncation of the second sequence is performed. -/
def fullPair (s : ℕ) (Z : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, natWitness n * f n / (Z * (n : ℝ) ^ (s + 2))

theorem natWitness_eq_zero_of_five_le (n : ℕ) (hn : 5 ≤ n) :
    natWitness n = 0 := by
  simp only [natWitness, if_neg (show n ≠ 1 by omega),
    if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
    if_neg (show n ≠ 4 by omega)]

/-- Every complete dual pairing is genuinely summable by finite support. -/
theorem fullPair_summable (s : ℕ) (Z : ℝ) (f : ℕ → ℝ) :
    Summable (fun n : ℕ => natWitness n * f n / (Z * (n : ℝ) ^ (s + 2))) := by
  apply summable_of_ne_finset_zero (s := Finset.range 5)
  intro n hn
  have hlarge : 5 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
  rw [natWitness_eq_zero_of_five_le n hlarge]
  simp

/-- Exact finite-support reindexing of the literal infinite pairing. -/
theorem fullPair_eq_rawInner (s : ℕ) (Z : ℝ) (f : ℕ → ℝ) :
    fullPair s Z f = rawInner s witness (fun i => f (i.val + 1)) / Z := by
  by_cases hZ : Z = 0
  · simp [fullPair, hZ]
  unfold fullPair
  rw [tsum_eq_sum (s := Finset.range 5) (by
    intro n hn
    have hlarge : 5 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    rw [natWitness_eq_zero_of_five_le n hlarge]
    simp)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [rawInner, witness, natWitness, Fin.sum_univ_succ] <;>
    field_simp [hZ] <;> ring

theorem fullPair_norm (Z : ℝ) : fullPair 0 Z natWitness = 30 / Z := by
  rw [fullPair_eq_rawInner]
  have hsites : (fun i : Fin 4 => natWitness (i.val + 1)) = witness := by
    funext i
    fin_cases i <;> norm_num [natWitness, witness]
  rw [hsites, witness_norm]

theorem fullPair_reciprocal_energy (Z : ℝ) :
    fullPair 1 Z natWitness = 10 / Z := by
  rw [fullPair_eq_rawInner]
  have hsites : (fun i : Fin 4 => natWitness (i.val + 1)) = witness := by
    funext i
    fin_cases i <;> norm_num [natWitness, witness]
  rw [hsites, witness_reciprocal_energy]

theorem fullPair_mean_zero (Z : ℝ) : fullPair 0 Z (fun _ => 1) = 0 := by
  rw [fullPair_eq_rawInner, witness_mean_zero, zero_div]

theorem fullPair_atom_annihilates (d : ℕ) (hd : 2 ≤ d) (hfour : d ≠ 4)
    (Z : ℝ) :
    fullPair 0 Z (fun n => ((n % d : ℕ) : ℝ) / (d : ℝ)) = 0 := by
  rw [fullPair_eq_rawInner]
  change rawInner 0 witness (atom d) / Z = 0
  rw [witness_atom_annihilates d hd hfour, zero_div]

/-- Exact complete infinite dual row of the literal optimizer synthesis. -/
theorem fullPair_optimizer_row (S : Finset ℕ) (c : ℕ → ℝ)
    (htwo : 2 ∈ S) (hthree : 3 ∈ S)
    (hlegal : ∀ d ∈ S, 2 ≤ d ∧ d ≠ 4) (Z : ℝ) :
    fullPair 1 Z (fun n => 1 - ∑ d ∈ S, c d * ((n % d : ℕ) : ℝ) / (d : ℝ)) =
      (5 - 4 * c 2 - c 3) / (12 * Z) := by
  rw [fullPair_eq_rawInner]
  simpa only [atom, mul_div_assoc] using
    witness_optimizer_row_normalized S c htwo hthree hlegal Z

end RiemannResearch.RH.ZetaTwoConductorFour

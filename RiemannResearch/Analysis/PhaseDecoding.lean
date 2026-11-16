/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimePhaseTorus
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import RiemannResearch.Analysis.LagPhase
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact and finite-precision phase decoding

Source (statements and motivation): the user-supplied reports
*Empirical Phase Coding of Zeta Zero Ordinates by Prime Logarithm Moduli*,
pp. 3, 7, 9; https://drive.google.com/file/d/1quuQlmUyGYSn5E8FmkfbdOeg9fIfI_KR/view
and *Modular Phase Reconstruction of Zeta Zeros from Pole Lattices*, pp. 2, 4, 8;
https://drive.google.com/file/d/1opJNKzINIeBMDA_k6mr1jEtfW26_-2Cj/view.

The exact two-prime arithmetic is reused from PrimePhaseTorus. The new results
give a deterministic capacity bound, arbitrarily distant approximate collisions
for every fixed finite coordinate family, a nearest-neighbor certificate,
compact inverse stability, and a one-prime height-seed theorem.

The metric is the unit additive-circle distance; the product metric is the
sup metric. The reports also use Euclidean torus distances, whose numerical
constants must not be substituted without the appropriate norm conversion.
The collision theorem is about arbitrary real inputs; it does not assert that
the colliding inputs are zeta-zero ordinates. No RH, zero simplicity, Baker
bound, random-point model, or equidistribution premise is used.
-/

noncomputable section
namespace RiemannResearch.Analysis.PhaseDecoding
open PrimePhaseTorus

def bin (M : ℕ) (hM : 0 < M) (x : ℝ) : Fin M :=
  ⟨⌊(M : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt' (Nat.ne_of_gt hM)).mpr
    have hm : (0 : ℝ) < M := by exact_mod_cast hM
    nlinarith [Int.fract_lt_one x]⟩

theorem same_bin_fract_close (M : ℕ) (hM : 0 < M) (x y : ℝ)
    (h : bin M hM x = bin M hM y) :
    |Int.fract x - Int.fract y| < 1 / (M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (⌊(M : ℝ) * Int.fract x⌋₊ : ℝ) =
      (⌊(M : ℝ) * Int.fract y⌋₊ : ℝ) := by
    exact_mod_cast congrArg Fin.val h
  have hx := Nat.floor_le (mul_nonneg hm.le (Int.fract_nonneg x))
  have hy := Nat.floor_le (mul_nonneg hm.le (Int.fract_nonneg y))
  have hx' := Nat.lt_floor_add_one ((M : ℝ) * Int.fract x)
  have hy' := Nat.lt_floor_add_one ((M : ℝ) * Int.fract y)
  apply (abs_lt).mpr
  constructor
  · have hh : (M : ℝ) * (Int.fract y - Int.fract x) < 1 := by nlinarith
    have := (lt_div_iff₀ hm).mpr (by nlinarith : (Int.fract y - Int.fract x) * M < 1)
    linarith
  · apply (lt_div_iff₀ hm).mpr
    nlinarith

theorem same_bin_circle_close (M : ℕ) (hM : 0 < M) (x y : ℝ)
    (h : bin M hM x = bin M hM y) :
    dist (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) < 1 / (M : ℝ) := by
  have hd : dist ((Int.fract x : ℝ) : AddCircle (1 : ℝ))
      ((Int.fract y : ℝ) : AddCircle (1 : ℝ)) ≤ |Int.fract x - Int.fract y| := by
    simpa using LagPhase.scaled_addCircle_dist_le 1 1 (Int.fract x) (Int.fract y)
  rw [AddCircle.coe_fract, AddCircle.coe_fract] at hd
  exact hd.trans_lt (same_bin_fract_close M hM x y h)

theorem finite_phase_collision {κ ι : Type*} [Fintype κ] [Fintype ι]
    (angles : κ → ι → ℝ) (M : ℕ) (hM : 0 < M)
    (hcard : M ^ Fintype.card ι < Fintype.card κ) :
    ∃ i j : κ, i ≠ j ∧ ∀ k : ι,
      dist (angles i k : AddCircle (1 : ℝ)) (angles j k : AddCircle (1 : ℝ)) <
        1 / (M : ℝ) := by
  classical
  let c : κ → ι → Fin M := fun i k => bin M hM (angles i k)
  have hc : Fintype.card (ι → Fin M) < Fintype.card κ := by simpa using hcard
  obtain ⟨i,j,hij,hcij⟩ := Fintype.exists_ne_map_eq_of_card_lt c hc
  exact ⟨i,j,hij,fun k => same_bin_circle_close M hM _ _ (congrFun hcij k)⟩

theorem separated_card_le {κ ι : Type*} [Fintype κ] [Fintype ι]
    (angles : κ → ι → ℝ) (M : ℕ) (hM : 0 < M)
    (hsep : ∀ i j : κ, i ≠ j → ∃ k : ι,
      1 / (M : ℝ) ≤ dist (angles i k : AddCircle (1 : ℝ))
        (angles j k : AddCircle (1 : ℝ))) :
    Fintype.card κ ≤ M ^ Fintype.card ι := by
  by_contra h
  obtain ⟨i,j,hij,hclose⟩ := finite_phase_collision angles M hM (Nat.lt_of_not_ge h)
  obtain ⟨k,hk⟩ := hsep i j hij
  exact (not_lt_of_ge hk) (hclose k)

theorem arbitrarily_far_collisions {ι : Type*} [Finite ι]
    (angles : ℝ → ι → ℝ) (M : ℕ) (hM : 0 < M) (R : ℝ) (hR : 0 < R) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ R ≤ |s - t| ∧ ∀ k : ι,
      dist (angles s k : AddCircle (1 : ℝ)) (angles t k : AddCircle (1 : ℝ)) <
        1 / (M : ℝ) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i,j,hij,hclose⟩ := finite_phase_collision
    (fun i : Fin (M ^ Fintype.card ι + 1) => angles (R * i.val))
    M hM (by simp)
  refine ⟨R * i.val, R * j.val, by positivity, by positivity, ?_, hclose⟩
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hh : i.val + 1 ≤ j.val ∨ j.val + 1 ≤ i.val := by omega
  rcases hh with hh | hh
  · have hc : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hh
    have ha := neg_le_abs (R * (i.val : ℝ) - R * (j.val : ℝ))
    nlinarith
  · have hc : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hh
    have ha := le_abs_self (R * (i.val : ℝ) - R * (j.val : ℝ))
    nlinarith

theorem prime_phases_arbitrarily_far_close {ι : Type*} [Finite ι]
    (primes : ι → ℕ) (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ R ≤ |s - t| ∧ ∀ k : ι,
      dist (primePhase (primes k) s) (primePhase (primes k) t) < ε := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨s,t,hs,ht,hst,hclose⟩ := arbitrarily_far_collisions
    (fun t k => Real.log (primes k) / (2 * Real.pi) * t)
    (n+1) (by omega) R hR
  refine ⟨s,t,hs,ht,hst,fun k => (hclose k).trans ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hn

theorem unique_nearest_of_separation {κ X : Type*} [PseudoMetricSpace X]
    (code : κ → X) (i j : κ) (y : X) (η : ℝ)
    (hsep : ∀ j, j ≠ i → 2 * η < dist (code i) (code j))
    (hnoise : dist y (code i) ≤ η)
    (hbest : dist y (code j) ≤ dist y (code i)) : j = i := by
  by_contra hji
  have ht := dist_triangle (code i) y (code j)
  rw [dist_comm (code i) y] at ht
  have := hsep j hji
  linarith

theorem compact_inverse_modulus {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t : X, dist (f s) (f t) < δ → dist s t < ε := by
  let e : X ≃ Set.range f := Equiv.ofInjective f hinj
  have he : Continuous e := hf.subtype_mk (fun x => Set.mem_range_self x)
  let h : X ≃ₜ Set.range f := he.homeoOfEquivCompactToT2
  let : CompactSpace (Set.range f) := isCompact_iff_compactSpace.mp (isCompact_range hf)
  have hu : UniformContinuous h.symm := by
    simpa only [uniformContinuousOn_univ] using
      isCompact_univ.uniformContinuousOn_of_continuous h.symm.continuous.continuousOn
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ,hδ,fun s t hst => ?_⟩
  have hh := hd (a := h s) (b := h t) hst
  simpa only [Homeomorph.symm_apply_apply] using hh

theorem two_prime_compact_stability {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (K : Set ℝ) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ K, ∀ t ∈ K,
      dist (primePhase p s, primePhase q s) (primePhase p t, primePhase q t) < δ →
        |s - t| < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
    fun t => (primePhase p t, primePhase q t)
  have hf : Continuous f :=
    ((continuous_primePhase p).comp continuous_subtype_val).prodMk
      ((continuous_primePhase q).comp continuous_subtype_val)
  have hi : Function.Injective f := fun s t h =>
    Subtype.ext (two_prime_phase_injective hp hq hpq h)
  obtain ⟨δ,hδ,hd⟩ := compact_inverse_modulus f hf hi ε hε
  exact ⟨δ,hδ,fun s hs t ht hst => by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hd ⟨s,hs⟩ ⟨t,ht⟩ hst⟩

theorem one_phase_local_injective (a s t : ℝ) (ha : a ≠ 0)
    (hphase : ((a * s : ℝ) : AddCircle (1 : ℝ)) = ((a * t : ℝ) : AddCircle (1 : ℝ)))
    (hlocal : |a| * |s - t| < 1) : s = t := by
  have hz : ((a * (s - t) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [mul_sub, AddCircle.coe_sub]
    exact sub_eq_zero.mpr hphase
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  simp only [zsmul_eq_mul, mul_one] at hn
  have hna : |(n : ℝ)| < 1 := by rw [hn, abs_mul]; exact hlocal
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hna
  have hlo' : (-1 : ℤ) < n := by exact_mod_cast hlo
  have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
  have hn0 : n = 0 := by omega
  have hm : a * (s - t) = 0 := by rw [← hn, hn0]; simp
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left ha)

theorem one_prime_local_injective {p : ℕ} (hp : 1 < p) (s t : ℝ)
    (hphase : primePhase p s = primePhase p t)
    (hlocal : |s - t| < 2 * Real.pi / Real.log p) : s = t := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hd : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply one_phase_local_injective (Real.log p / (2 * Real.pi)) s t
    (div_ne_zero hl.ne' hd.ne') hphase
  rw [abs_of_pos (div_pos hl hd)]
  calc
    Real.log p / (2 * Real.pi) * |s - t| <
        Real.log p / (2 * Real.pi) * (2 * Real.pi / Real.log p) :=
      mul_lt_mul_of_pos_left hlocal (div_pos hl hd)
    _ = 1 := by field_simp

theorem one_prime_seed_unique {p : ℕ} (hp : 1 < p) (s t H : ℝ)
    (hphase : primePhase p s = primePhase p t)
    (hs : |s - H| < Real.pi / Real.log p)
    (ht : |t - H| < Real.pi / Real.log p) : s = t := by
  apply one_prime_local_injective hp s t hphase
  have htri := abs_sub_le s H t
  rw [abs_sub_comm H t] at htri
  calc
    |s - t| ≤ |s - H| + |t - H| := htri
    _ < 2 * (Real.pi / Real.log p) := by linarith
    _ = 2 * Real.pi / Real.log p := by ring

/-- The actual nearest-integer anchor algorithm recovers the correct lift
from a height seed strictly closer than half a period. No phase-range
convention on u is needed. -/
theorem anchor_round_recovers (L : ℝ) (hL : 0 < L) (u H : ℝ) (m : ℤ)
    (h : |(u + (m : ℝ)) * L - H| < L / 2) :
    ⌊H / L - u + 1 / 2⌋ = m := by
  obtain ⟨hl,hu⟩ := abs_lt.mp h
  have hlo : u + (m : ℝ) - 1 / 2 < H / L := by
    apply (lt_div_iff₀ hL).mpr
    nlinarith
  have hhi : H / L < u + (m : ℝ) + 1 / 2 := by
    apply (div_lt_iff₀ hL).mpr
    nlinarith
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

/-- The signed physical error of a correctly lifted noisy phase is exactly
the period times the phase error. -/
theorem noisy_anchor_error_identity (L u e : ℝ) (m : ℤ) :
    (u + e + (m : ℝ)) * L - (u + (m : ℝ)) * L = e * L := by
  ring

/-- A seed error plus phase error smaller than half a period certifies the
actual noisy rounding decoder, with its exact signed reconstruction error. -/
theorem noisy_anchor_reconstruction (L : ℝ) (hL : 0 < L) (u e H : ℝ) (m : ℤ)
    (hbudget : |(u + (m : ℝ)) * L - H| + L * |e| < L / 2) :
    ⌊H / L - (u + e) + 1 / 2⌋ = m ∧
      (u + e + (⌊H / L - (u + e) + 1 / 2⌋ : ℤ)) * L -
        (u + (m : ℝ)) * L = e * L := by
  have hlocal : |(u + e + (m : ℝ)) * L - H| < L / 2 := by
    calc
      _ = |((u + (m : ℝ)) * L - H) + e * L| := by congr 1; ring
      _ ≤ |(u + (m : ℝ)) * L - H| + |e * L| := abs_add_le _ _
      _ = |(u + (m : ℝ)) * L - H| + L * |e| := by
        rw [abs_mul, abs_of_pos hL]
        ring
      _ < L / 2 := hbudget
  have hm := anchor_round_recovers L hL (u + e) H m hlocal
  refine ⟨hm, ?_⟩
  rw [hm]
  exact noisy_anchor_error_identity L u e m

end RiemannResearch.Analysis.PhaseDecoding

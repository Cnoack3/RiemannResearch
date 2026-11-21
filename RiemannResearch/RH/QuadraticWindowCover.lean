import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.PrimePowerRamanujanLimits
import RiemannResearch.RH.MobiusDifferenceCLM
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite legal test covering a quadratic window
Source: the user-provided quadratic-window handoff. The integer rectangle below
gives explicit distinct divisors with odd floor quotient.
-/

open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open PrimePowerSchur

private theorem oddQuotientCount (H n : ℕ) (hH : 0 < H)
    (hn : 8*H ≤ n) (hx : n ≤ H^2) :
    H ≤ 4 * ((Finset.Ioc (2*H) (8*H)).filter (fun m => n/m % 2 = 1)).card := by
  let K := n/(8*H)
  let L := H/(2*K)
  have h8 : 0 < 8*H := by omega
  have hK : 0 < K := Nat.div_pos hn h8
  have hfloor : K*(8*H) ≤ n := Nat.div_mul_le_self ..
  have hnext : n < (K+1)*(8*H) := (Nat.div_lt_iff_lt_mul h8).mp (by dsimp [K]; omega)
  have hKH : 8*K ≤ H := by
    apply Nat.le_of_mul_le_mul_right (c := H)
    simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfloor.trans hx
    exact hH
  have hL : 0 < L := Nat.div_pos (by omega) (by omega)
  have hLfloor : L*(2*K) ≤ H := Nat.div_mul_le_self ..
  have hLnext : H < (L+1)*(2*K) := (Nat.div_lt_iff_lt_mul (by omega : 0<2*K)).mp (by dsimp [L]; omega)
  have hsize : H ≤ 4*(K*L) := by nlinarith [Nat.mul_le_mul_left K hL]
  let k (i : Fin K) := 2*K + 2*(i:ℕ) + 1
  let m (ij : Fin K × Fin L) := n/(k ij.1 + 1) + (ij.2:ℕ) + 1
  have hband (ij : Fin K × Fin L) :
      2*H < m ij ∧ m ij ≤ 8*H ∧ n/(m ij) = k ij.1 := by
    have hi : (ij.1:ℕ) < K := ij.1.isLt
    have hj : (ij.2:ℕ) < L := ij.2.isLt
    let t := k ij.1
    let b := n/(t+1)
    have htop : t+1 ≤ 4*K := by dsimp [t,k]; omega
    have hbot : K+1 ≤ t := by dsimp [t,k]; omega
    have hb : 2*H ≤ b := by
      apply (Nat.le_div_iff_mul_le (by omega : 0<t+1)).mpr
      calc
        2*H*(t+1) ≤ 2*H*(4*K) := Nat.mul_le_mul_left _ htop
        _ = K*(8*H) := by ring
        _ ≤ n := hfloor
    have hkm : t*((ij.2:ℕ)+1) ≤ b := by
      calc
        t*((ij.2:ℕ)+1) ≤ (4*K)*L := Nat.mul_le_mul (by omega) (by omega)
        _ = 2*(L*(2*K)) := by ring
        _ ≤ 2*H := Nat.mul_le_mul_left _ hLfloor
        _ ≤ b := hb
    have hmb : m ij = b + (ij.2:ℕ) + 1 := rfl
    have hlo : t * m ij ≤ n := by
      calc
        _ = t*b + t*((ij.2:ℕ)+1) := by rw [hmb]; ring
        _ ≤ t*b + b := Nat.add_le_add_left hkm _
        _ = b*(t+1) := by ring
        _ ≤ n := Nat.div_mul_le_self ..
    have hhi : n < (t+1) * m ij := by
      have h := (Nat.div_lt_iff_lt_mul (by omega : 0<t+1)).mp (show n/(t+1)<b+1 by dsimp [b]; omega)
      calc
        n < (b+1)*(t+1) := h
        _ = (t+1)*(b+1) := Nat.mul_comm _ _
        _ ≤ (t+1)*m ij := Nat.mul_le_mul_left _ (by omega)
    have hm : 0 < m ij := by omega
    refine ⟨by omega, ?_, le_antisymm ?_ ?_⟩
    · have h' := (Nat.mul_le_mul_right (8*H) hbot)
      by_contra! hc
      have h'' := Nat.mul_le_mul_left t (show 8*H ≤ m ij by omega)
      omega
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hm).mpr hhi)
    · exact (Nat.le_div_iff_mul_le hm).mpr hlo
  let S := (Finset.Ioc (2*H) (8*H)).filter (fun m => n/m % 2 = 1)
  let f (ij : Fin K × Fin L) : ↑S :=
    ⟨m ij, by
      obtain ⟨ha,hb,hq⟩ := hband ij
      simp only [S, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨ha,hb⟩, by rw [hq]; dsimp [k]; omega⟩⟩
  have hinj : Function.Injective f := by
    intro ij ij' he
    have he' : m ij = m ij' := congrArg Subtype.val he
    have hk : k ij.1 = k ij'.1 := (hband ij).2.2.symm.trans ((congrArg (fun x => n/x) he').trans (hband ij').2.2)
    have h1 : ij.1 = ij'.1 := Fin.ext (by dsimp [k] at hk; omega)
    have h2 : ij.2 = ij'.2 := by
      apply Fin.ext
      dsimp [m] at he'
      rw [h1] at he'
      omega
    exact Prod.ext h1 h2
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hcard
  exact hsize.trans (Nat.mul_le_mul_left 4 hcard)

private noncomputable def quadraticBit (m : ℕ) : ThresholdHilbert :=
  if hm : 0 < m then (m : ℝ)⁻¹ • hilbertDilation m hm (ramanujanPacketHilbert 2) else 0

private theorem quadraticBit_mem (m : ℕ) : quadraticBit m ∈ closedSpace := by
  unfold quadraticBit
  split_ifs with hm
  · exact closedSpace.smul_mem _ (closedSpace_dilation (packet_mem_closedSpace 2 (by norm_num)) m hm)
  · exact closedSpace.zero_mem

private theorem quadraticBit_sequence (m n : ℕ) :
    hilbertSequence (quadraticBit m) n = if n/m % 2 = 1 then 1 else 0 := by
  by_cases hm : 0 < m
  · have hr : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [quadraticBit, dif_pos hm, hilbertSequence_smul, Pi.smul_apply, smul_eq_mul,
      hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert]
    change (m:ℝ)⁻¹ * ((m:ℝ) * ramanujanPacket 2 (n/m)) = _
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
    change ((n/m % 2 : ℕ) : ℝ) = _
    have hmod := Nat.mod_lt (n/m) (by decide : 0 < 2)
    by_cases h : n/m % 2 = 1
    · simp [h]
    · simp [h, show n/m % 2 = 0 by omega]
  · have h : m = 0 := by omega
    subst m
    rw [quadraticBit, dif_neg (by decide : ¬ 0 < (0:ℕ)), ← anchoredEvaluationCLM_apply, map_zero] <;> simp

/-- A finite legal test, supported from H onwards and bounded from below on
every integer from H through H². Constants are independent of H. -/
theorem quadraticWindowTest_exists (H : ℕ) (hH : 0 < H) :
    ∃ q : ThresholdHilbert, q ∈ closedSpace ∧
      (∀ n : ℕ, 0 ≤ hilbertSequence q n ∧ hilbertSequence q n ≤ 4) ∧
      (∀ n : ℕ, n < H → hilbertSequence q n = 0) ∧
      (∀ n : ℕ, H ≤ n → n ≤ H^2 → 1/32 ≤ hilbertSequence q n) := by
  classical
  let S := Finset.Ioc (2*H) (8*H)
  let C (n : ℕ) := (S.filter (fun m => n/m % 2 = 1)).card
  let bit (m n : ℕ) : ℝ := if n/m % 2 = 1 then 1 else 0
  let q := quadraticBit H + quadraticBit (2*H) + quadraticBit (4*H) +
    (1/(8*(H:ℝ))) • (∑ m ∈ S, quadraticBit m)
  have hq (n : ℕ) : hilbertSequence q n = bit H n + bit (2*H) n + bit (4*H) n +
      (C n:ℝ)/(8*(H:ℝ)) := by
    rw [← anchoredEvaluationCLM_apply n q]
    dsimp only [q]
    rw [map_add, map_add, map_add, map_smul, map_sum]
    simp only [anchoredEvaluationCLM_apply, smul_eq_mul, quadraticBit_sequence]
    have hc : (∑ m ∈ S, if n/m % 2 = 1 then (1:ℝ) else 0) = (C n:ℝ) := by
      rw [← Finset.sum_filter]
      simp [C]
    rw [hc]
    simp [bit, div_eq_mul_inv, mul_comm]
  have hhr : (0:ℝ) < H := by exact_mod_cast hH
  have hden : 0 < 8*(H:ℝ) := by positivity
  have hb (m n : ℕ) : 0 ≤ bit m n ∧ bit m n ≤ 1 := by
    dsimp [bit]
    split_ifs <;> norm_num
  have hsmall {m n : ℕ} (h : n < m) : bit m n = 0 := by simp [bit, Nat.div_eq_of_lt h]
  have hone {m n : ℕ} (hm : 0<m) (hl : m≤n) (hu : n<2*m) : bit m n = 1 := by
    have ha : 1 ≤ n/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa)
    have hb' : n/m < 2 := (Nat.div_lt_iff_lt_mul hm).mpr hu
    simp [bit, show n/m = 1 by omega]
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact closedSpace.add_mem
      (closedSpace.add_mem (closedSpace.add_mem (quadraticBit_mem _) (quadraticBit_mem _)) (quadraticBit_mem _))
      (closedSpace.smul_mem _ (closedSpace.sum_mem fun m _ => quadraticBit_mem m))
  · intro n
    have hc : C n ≤ 8*H := by
      apply (Finset.card_filter_le S _).trans
      simp [S, Nat.card_Ioc]
    have hcr : (C n:ℝ) ≤ 8*(H:ℝ) := by exact_mod_cast hc
    have ha : (C n:ℝ)/(8*(H:ℝ)) ≤ 1 := (div_le_iff₀ hden).mpr (by simpa)
    have hp : 0 ≤ (C n:ℝ)/(8*(H:ℝ)) := by positivity
    rw [hq]
    constructor <;> linarith [(hb H n).1,(hb H n).2,(hb (2*H) n).1,(hb (2*H) n).2,
      (hb (4*H) n).1,(hb (4*H) n).2]
  · intro n hn
    have hc : C n = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hs,hodd⟩ := Finset.mem_filter.mp hm
      have hl := (Finset.mem_Ioc.mp hs).1
      simp [Nat.div_eq_of_lt (show n<m by omega)] at hodd
    rw [hq, hc, hsmall hn, hsmall (by omega : n<2*H), hsmall (by omega : n<4*H)]
    simp
  · intro n hn hx
    have hp : 0 ≤ (C n:ℝ)/(8*(H:ℝ)) := by positivity
    rw [hq]
    by_cases h1 : n < 2*H
    · rw [hone hH hn h1]
      linarith [(hb (2*H) n).1,(hb (4*H) n).1]
    by_cases h2 : n < 4*H
    · rw [hone (by omega : 0<2*H) (by omega) (by omega : n<2*(2*H))]
      linarith [(hb H n).1,(hb (4*H) n).1]
    by_cases h3 : n < 8*H
    · rw [hone (by omega : 0<4*H) (by omega) (by omega : n<2*(4*H))]
      linarith [(hb H n).1,(hb (2*H) n).1]
    have hc : H ≤ 4*C n := oddQuotientCount H n hH (by omega) hx
    have hcr : (H:ℝ) ≤ 4*(C n:ℝ) := by exact_mod_cast hc
    have hav : (1:ℝ)/32 ≤ (C n:ℝ)/(8*(H:ℝ)) := (le_div_iff₀ hden).mpr (by linarith)
    linarith [(hb H n).1,(hb (2*H) n).1,(hb (4*H) n).1]

end RiemannResearch.RH.Pareto.CoefficientStabilization

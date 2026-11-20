import RiemannResearch.RH.ParetoParity8192Head

/-! # Exact segmented divisor sieve for the Pareto parity head

Each block starts from the signed residue at its preceding site. An entry
receives one update for every conductor dividing its physical site. The
proof identifies each computed block with the defining sum of ceilings.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192

private def addAt {len : ℕ} (v : Vector ℤ len) (index : ℕ) (amount : ℤ) : Vector ℤ len :=
  if h : index < len then v.set index (v[index] + amount) else v

private theorem get_addAt {len : ℕ} (v : Vector ℤ len) (index j : ℕ) (hj : j < len)
    (amount : ℤ) :
    (addAt v index amount)[j] = v[j] + if index = j then amount else 0 := by
  by_cases h : index < len
  · simp only [addAt,dif_pos h,Vector.getElem_set]
    split_ifs with hsame
    · subst j
      rfl
    · simp
  · have hn : index ≠ j := by omega
    simp [addAt,h,hn]

private def site (lo d k : ℕ) := d*(lo/d+k+1)

private theorem lt_site (lo d k : ℕ) (hd : 0 < d) : lo < site lo d k := by
  have h := Nat.lt_mul_div_succ lo hd
  exact h.trans_le (Nat.mul_le_mul_left d (by omega))

/-- Apply a conductor's updates in reverse order. The recursion is tail-recursive. -/
private def mark {len : ℕ} (lo d : ℕ) (amount : ℤ) : ℕ → Vector ℤ len → Vector ℤ len
  | 0, v => v
  | k+1, v =>
    mark lo d amount k (addAt v (site lo d k - (lo+1)) amount)

private theorem get_mark {len : ℕ} (lo d j : ℕ) (hd : 0 < d) (hj : j<len)
    (amount : ℤ) (count : ℕ) (v : Vector ℤ len) :
    (mark lo d amount count v)[j] = v[j] +
      ∑ k ∈ Finset.range count, if site lo d k = lo+j+1 then amount else 0 := by
  induction count generalizing v with
  | zero => simp [mark]
  | succ k ih =>
    rw [mark,ih,get_addAt _ _ _ hj,Finset.sum_range_succ]
    have he : site lo d k - (lo+1) = j ↔ site lo d k = lo+j+1 := by
      have := lt_site lo d k hd
      omega
    simp only [he]
    ring

private theorem sum_hits (lo len d j : ℕ) (hd : 0 < d) (hj : j<len) (amount : ℤ) :
    (∑ k ∈ Finset.range ((lo+len)/d-lo/d),
      if site lo d k = lo+j+1 then amount else 0) =
        if d ∣ lo+j+1 then amount else 0 := by
  by_cases h : d ∣ lo+j+1
  · let m := (lo+j+1)/d
    have hm : d*m = lo+j+1 := Nat.mul_div_cancel' h
    have hlow : lo/d < m := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm,hm]; omega)
    have hhigh : m ≤ (lo+len)/d := Nat.div_le_div_right (by omega)
    let k := m-lo/d-1
    have hindex : lo/d+k+1 = m := by dsimp [k]; omega
    have hsite : site lo d k = lo+j+1 := by rw [site,hindex,hm]
    have hk : k ∈ Finset.range ((lo+len)/d-lo/d) := Finset.mem_range.mpr (by dsimp [k]; omega)
    rw [if_pos h,Finset.sum_eq_single_of_mem k hk]
    · simp [hsite]
    · intro t ht htk
      have hn : site lo d t ≠ lo+j+1 := by
        intro he
        have he' := Nat.eq_of_mul_eq_mul_left hd (he.trans hsite.symm)
        change lo/d+t+1 = lo/d+k+1 at he'
        omega
      simp [hn]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hn : site lo d k ≠ lo+j+1 := by
      intro he
      apply h
      rw [← he]
      exact dvd_mul_right d (lo/d+k+1)
    simp [hn]

private def sieveSteps {len : ℕ} (lo : ℕ) : ℕ → Vector ℤ len → Vector ℤ len
  | 0, v => v
  | k+1, v =>
    let d := k+2
    let count := (lo+len)/d-lo/d
    sieveSteps lo k (mark lo d ((d:ℤ)*coeff d) count v)

private theorem get_sieveSteps {len : ℕ} (lo j k : ℕ) (hj : j<len) (v : Vector ℤ len) :
    (sieveSteps lo k v)[j] = v[j] +
      ∑ i ∈ Finset.range k, if i+2 ∣ lo+j+1 then ((i+2:ℕ):ℤ)*coeff (i+2) else 0 := by
  induction k generalizing v with
  | zero => simp [sieveSteps]
  | succ k ih =>
    rw [sieveSteps,ih,get_mark _ _ _ (by omega) hj,sum_hits _ _ _ _ (by omega) hj,
      Finset.sum_range_succ]
    ring

private theorem sum_dictionary (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range 8191, f (i+2)) = ∑ d ∈ support, f d := by
  simpa only [intFold_eq,zero_add] using intFold_support f

private def physicalSteps (lo len : ℕ) : Vector ℤ len :=
  sieveSteps lo 8191 (Vector.replicate len (-987443549))

private theorem physicalSteps_spec (lo len j : ℕ) (hj : j<len) :
    (physicalSteps lo len)[j] = residual (lo+j+1) - residual (lo+j) := by
  rw [physicalSteps,get_sieveSteps _ _ _ hj,Vector.getElem_replicate hj,
    sum_dictionary (fun d => if d ∣ lo+j+1 then (d:ℤ)*coeff d else 0),
    ← Finset.sum_filter,residual_succ,coefficientSum_value]
  ring

private def roundedLoss (n : ℕ) (e : ℤ) : ℕ :=
  let den := n*(n+1)
  (e.natAbs^2+(den-1))/den

private def scan {len : ℕ} (steps : Vector ℤ len) (lo : ℕ) :
    (count index : ℕ) → ℤ → ℕ → ℕ
  | 0, _, _, total => total
  | count+1, i, e, total =>
    let next := e + (steps[i]?).getD 0
    scan steps lo count (i+1) next (total + roundedLoss (lo+i+1) next)

private theorem scan_spec {len : ℕ} (lo count i acc : ℕ) (h : i+count ≤ len) :
    scan (physicalSteps lo len) lo count i (residual (lo+i)) acc =
      acc + ∑ j ∈ Finset.range count, roundedUnit (lo+i+j+1) := by
  induction count generalizing i acc with
  | zero => simp [scan]
  | succ count ih =>
    have hi : i < len := by omega
    have hnext : residual (lo+i) + ((physicalSteps lo len)[i]?).getD 0 =
        residual (lo+(i+1)) := by
      rw [Vector.getElem?_eq_getElem hi,Option.getD_some,physicalSteps_spec _ _ _ hi]
      rw [← Nat.add_assoc]
      ring
    rw [scan,hnext,ih (i+1) _ (by omega),Finset.sum_range_succ']
    simp only [Nat.add_zero,roundedLoss,roundedUnit]
    simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private def startingResidual (lo : ℕ) : ℤ :=
  10^9 - fastSum (fun d => coeff d * ((lo%d : ℕ):ℤ))

private theorem startingResidual_spec (lo : ℕ) : startingResidual lo = residual lo := by
  unfold startingResidual residual
  rw [fastSum_spec]

/-- Executable exact integer head of sites `lo+1` through `lo+length`. -/
def sievedBlock (lo length : ℕ) : ℕ :=
  scan (physicalSteps lo length) lo length 0 (startingResidual lo) 0

theorem sievedBlock_spec (lo length : ℕ) :
    sievedBlock lo length = ∑ j ∈ Finset.range length, roundedUnit (lo+j+1) := by
  simpa [sievedBlock,startingResidual_spec] using scan_spec lo length 0 0 (show 0+length≤length by omega)

/-- The billion-site head consists of 8192 independently evaluable blocks. -/
theorem roundedHead_eq_sievedBlocks :
    roundedHead (2^30) = ∑ b ∈ Finset.range 8192, sievedBlock ((2^17)*b) (2^17) := by
  rw [show (2^30 : ℕ) = (2^17)*8192 by norm_num,roundedHead_eq_blocks]
  exact Finset.sum_congr rfl fun b _ => (sievedBlock_spec _ _).symm

/-- One of eight consecutive groups used by the full integer replay. -/
def sievedStripe (g : ℕ) : ℕ :=
  (List.range 1024).foldl
    (fun a j => a + sievedBlock (131072 * (1024*g+j)) 131072) 0

private theorem sum_range_foldl (f : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldl (fun t i => t+f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.foldl_append,ih,Finset.sum_range_succ,Nat.add_assoc]

private theorem sum_range_groups (f : ℕ → ℕ) (length count : ℕ) :
    (∑ i ∈ Finset.range (length*count), f i) =
      ∑ g ∈ Finset.range count, ∑ j ∈ Finset.range length, f (length*g+j) := by
  induction count with
  | zero => simp
  | succ g ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem roundedHead_eq_sievedStripes :
    roundedHead (2 ^ 30) = ∑ g ∈ Finset.range 8, sievedStripe g := by
  rw [roundedHead_eq_sievedBlocks]
  change (∑ b ∈ Finset.range (1024*8), sievedBlock (131072*b) 131072) = _
  rw [sum_range_groups]
  apply Finset.sum_congr rfl
  intro g hg
  unfold sievedStripe
  rw [sum_range_foldl,zero_add]

end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192

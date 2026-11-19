import RiemannResearch.RH.RamanujanResidueMassData

/-! # Periodic signed envelopes for raw Pareto residue signals

Each conductor in a group divides the group's period. Consequently a certified
range for its finite period holds at every physical site. -/

namespace RiemannResearch.RH.GroupedResidueMass
open RamanujanResidueMass.Certificate (signal)

structure ResidueGroup where
  period : ℕ
  terms : List (ℕ × ℤ)
  lower : ℤ
  upper : ℤ
  deriving DecidableEq

def ResidueGroup.Valid (g : ResidueGroup) : Prop :=
  0 < g.period ∧ (∀ t ∈ g.terms, t.1 ∣ g.period) ∧
    ∀ k : Fin g.period, g.lower ≤ signal g.terms k ∧ signal g.terms k ≤ g.upper

instance (g : ResidueGroup) : Decidable g.Valid := by
  unfold ResidueGroup.Valid
  infer_instance

private theorem signal_mod (s : List (ℕ × ℤ)) (p k : ℕ)
    (hs : ∀ t ∈ s, t.1 ∣ p) : signal s (k % p) = signal s k := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    obtain ⟨d, z⟩ := t
    have hd : d ∣ p := hs (d,z) (by simp)
    simpa only [signal, Nat.mod_mod_of_dvd _ hd, ih (fun t ht => hs t (by simp [ht]))]

theorem ResidueGroup.bounds (g : ResidueGroup) (h : g.Valid) (k : ℕ) :
    g.lower ≤ signal g.terms k ∧ signal g.terms k ≤ g.upper := by
  have hf := h.2.2 ⟨k % g.period, Nat.mod_lt k h.1⟩
  change g.lower ≤ signal g.terms (k % g.period) ∧ signal g.terms (k % g.period) ≤ g.upper at hf
  simpa only [signal_mod g.terms g.period k h.2.1] using hf

private theorem signal_append (s t : List (ℕ × ℤ)) (k : ℕ) :
    signal (s ++ t) k = signal s k + signal t k := by
  induction s with
  | nil => simp [signal]
  | cons a s ih =>
    obtain ⟨d,z⟩ := a
    simp [signal, ih, add_assoc]

theorem group_sum_bounds (gs : List ResidueGroup) (h : ∀ g ∈ gs, g.Valid) (k : ℕ) :
    (gs.map ResidueGroup.lower).sum ≤ signal (gs.flatMap ResidueGroup.terms) k ∧
      signal (gs.flatMap ResidueGroup.terms) k ≤ (gs.map ResidueGroup.upper).sum := by
  induction gs with
  | nil => simp [signal]
  | cons g gs ih =>
    have hg := g.bounds (h g (by simp)) k
    have ht := ih (fun a ha => h a (by simp [ha]))
    simpa only [List.flatMap_cons, signal_append, List.map_cons, List.sum_cons]
      using And.intro (add_le_add hg.1 ht.1) (add_le_add hg.2 ht.2)

namespace Conductor241
def groups : List ResidueGroup := [
    ⟨480, [(5, 173348), (3, 317008), (6, -125109), (10, -66898), (15, -42552), (30, 17914), (2, 478877), (4, 18343), (160, -195), (20, -1628), (12, -2359)], -466544, 936123⟩,
    ⟨192, [(192, 99), (8, -127)], -196, 18216⟩,
    ⟨432, [(9, 2257), (16, 998), (54, 237), (27, -299)], -1116, 38929⟩,
    ⟨50, [(50, 47)], 0, 2303⟩,
    ⟨420, [(7, 115239), (21, -28555), (14, -43453), (35, -15358), (42, 11851), (70, 5756), (105, 2887), (210, -613), (28, -1785)], -526673, 566937⟩,
    ⟨330, [(11, 63531), (22, -22069), (33, -14082), (55, -6119), (66, 4777), (165, 559), (110, 767)], -513821, 390416⟩,
    ⟨44, [(44, -473)], -20339, 0⟩,
    ⟨390, [(13, 50852), (26, -18606), (39, -10595), (65, -4934), (78, 3534), (130, 520), (195, 177)], -520195, 320419⟩,
    ⟨208, [(208, -366), (104, 187)], -56501, 0⟩,
    ⟨510, [(17, 35926), (34, -12561), (51, -7038), (85, -3264), (102, 2418), (170, 499)], -437682, 300458⟩,
    ⟨228, [(19, 30974), (38, -10813), (57, -5828), (114, 1198), (228, 541), (76, -218)], -287280, 360194⟩,
    ⟨190, [(95, -2110), (190, 542)], -147392, 51490⟩,
    ⟨276, [(23, 23703), (46, -8128), (69, -4198), (138, 1304), (92, -803)], -308913, 284730⟩,
    ⟨230, [(115, -1265), (230, 500)], -87210, 57500⟩,
    ⟨207, [(207, -258)], -53148, 0⟩,
    ⟨290, [(29, 16679), (58, -5443), (145, -1652)], -349479, 268352⟩,
    ⟨174, [(87, -2638), (174, 808)], -157380, 70296⟩,
    ⟨372, [(31, 15230), (93, -3103), (62, -4572), (124, -325)], -364343, 216900⟩,
    ⟨222, [(37, 11857), (74, -2935), (111, -1147)], -193473, 279900⟩,
    ⟨185, [(185, -361)], -66424, 0⟩,
    ⟨246, [(41, 10686), (123, -2001), (82, -2285)], -257767, 256000⟩,
    ⟨205, [(205, -664)], -135456, 0⟩,
    ⟨430, [(43, 8228), (86, -2852), (215, -206)], -158068, 217140⟩,
    ⟨94, [(47, 6851), (94, -2520)], -118440, 199226⟩,
    ⟨49, [(49, 44)], 0, 2112⟩,
    ⟨159, [(53, 6436), (159, -1361)], -144266, 263900⟩,
    ⟨212, [(212, -716)], -151076, 0⟩,
    ⟨118, [(59, 4829), (118, -2342)], -138178, 144246⟩,
    ⟨122, [(61, 4988), (122, -1332)], -81252, 219360⟩,
    ⟨134, [(67, 3584), (134, -683)], -45761, 191466⟩,
    ⟨426, [(71, 4411), (213, -821), (142, -1131)], -196883, 172130⟩,
    ⟨146, [(73, 3205), (146, -613)], -44749, 186624⟩,
    ⟨462, [(77, -4068), (231, 729), (154, 721)], -198968, 167783⟩,
    ⟨79, [(79, 3297)], 0, 257166⟩,
    ⟨83, [(83, 2270)], 0, 186140⟩,
    ⟨89, [(89, 2027)], 0, 178376⟩,
    ⟨91, [(91, -2335)], -210150, 0⟩,
    ⟨97, [(97, 2331)], 0, 223776⟩,
    ⟨202, [(101, 1643), (202, -413)], -41713, 123000⟩,
    ⟨206, [(103, 3033), (206, -1103)], -113609, 196860⟩,
    ⟨107, [(107, 1068)], 0, 113208⟩,
    ⟨218, [(109, 1880), (218, -657)], -71613, 132084⟩,
    ⟨113, [(113, 1715)], 0, 192080⟩,
    ⟨119, [(119, -2001)], -236118, 0⟩,
    ⟨127, [(127, 957)], 0, 120582⟩,
    ⟨131, [(131, 1020)], 0, 132600⟩,
    ⟨133, [(133, -1542)], -203544, 0⟩,
    ⟨137, [(137, 1559)], 0, 212024⟩,
    ⟨139, [(139, 1538)], 0, 212244⟩,
    ⟨143, [(143, -1471)], -208882, 0⟩,
    ⟨149, [(149, 274)], 0, 40552⟩,
    ⟨151, [(151, 327)], 0, 49050⟩,
    ⟨157, [(157, 127)], 0, 19812⟩,
    ⟨161, [(161, -906)], -144960, 0⟩,
    ⟨163, [(163, 107)], 0, 17334⟩,
    ⟨167, [(167, 530)], 0, 87980⟩,
    ⟨173, [(173, 1104)], 0, 189888⟩,
    ⟨179, [(179, 154)], 0, 27412⟩,
    ⟨181, [(181, 663)], 0, 119340⟩,
    ⟨191, [(191, 950)], 0, 180500⟩,
    ⟨193, [(193, 617)], 0, 118464⟩,
    ⟨197, [(197, 499)], 0, 97804⟩,
    ⟨199, [(199, 629)], 0, 124542⟩,
    ⟨203, [(203, -904)], -182608, 0⟩,
    ⟨209, [(209, -975)], -202800, 0⟩,
    ⟨217, [(217, -479)], -103464, 0⟩,
    ⟨227, [(227, 95)], 0, 21470⟩,
    ⟨229, [(229, 642)], 0, 146376⟩,
    ⟨233, [(233, 209)], 0, 48488⟩,
    ⟨239, [(239, 620)], 0, 147560⟩,
    ⟨241, [(241, 266)], 0, 63840⟩]

def rows : List (ℕ × ℤ) := groups.flatMap ResidueGroup.terms

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem groups_valid : ∀ g ∈ groups, g.Valid := by decide +kernel

set_option maxRecDepth 100000 in
theorem rows_range : ∀ t ∈ rows, 2 ≤ t.1 ∧ t.1 ≤ 241 := by decide

def difference (k : ℕ) : ℤ := 1000000 - signal rows k

theorem scaled_abs_bound (k : ℕ) : |difference k| ≤ 8963702 := by
  have h := group_sum_bounds groups groups_valid k
  have hlo : (groups.map ResidueGroup.lower).sum = -7948434 := by decide
  have hhi : (groups.map ResidueGroup.upper).sum = 9963702 := by decide
  rw [hlo, hhi] at h
  change -7948434 ≤ signal rows k ∧ signal rows k ≤ 9963702 at h
  unfold difference
  rw [abs_le]
  omega

def headUnit (k : ℕ) : ℕ :=
  (difference (k+1)).natAbs^2 / ((k+1)*(k+2)) + 1

def block (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 128, headUnit (j*128+i)

def headBatch (j : ℕ) : ℕ := ∑ i ∈ Finset.range 32, block (j*32+i)
end Conductor241
end RiemannResearch.RH.GroupedResidueMass

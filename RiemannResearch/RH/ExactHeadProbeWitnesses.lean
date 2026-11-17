import RiemannResearch.RH.ExactHeadProbeCertificate
import RiemannResearch.RH.MobiusHeadGreenNormal
import Mathlib.Tactic

/-!
# Published rational centered-probe witnesses

The upper coefficients are the exact fractions published at
https://github.com/Cnoack3/RiemannResearch/blob/2ac5952fb4fb0efd67d12408390c8ed7fa3fa07a/RiemannResearch/ResearchData/ExactHeadGreen20261116/moment_probe_certificates.json
expressed over the same denominator as the floor coefficients of the probe.
The checks certify the complete energies with independent elementary tail bounds.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadProbeWitnesses
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.MobiusAffineProfile (weight)
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence (sum_Icc_one)
open ExactHeadAtomOptimizer ExactHeadProbeCertificate
open MobiusHeadGreen (greenPeriod)

private def scale : ℕ := 10 ^ 22

/-- The rational upper endpoint for each checked cutoff. -/
def probeBound : ℕ → ℚ
  | 5 => 628954 / 1000000
  | 7 => 510332 / 1000000
  | 11 => 365700 / 1000000
  | 13 => 364855 / 1000000
  | _ => 2 / 3

/-- Upper endpoints after removing the residues where the fitted residual is zero. -/
def tailProbeBound : ℕ → ℚ
  | 5 => 18057 / 1000000
  | 7 => 32283 / 1000000
  | 11 => 9073 / 1000000
  | 13 => 5777 / 1000000
  | _ => 2 / 3

private theorem of_witness (w : Witness) (K : ℕ) (hx : w.cutoff < w.period)
    (hperiod : greenPeriod w.cutoff = w.period) (hd : 0 < w.halfDen)
    (hp : ∀ r, fittedMomentProbe w.cutoff r = w.probe r)
    (hv : w.upper.all (fun z => decide (w.cutoff < z.1 ∧ z.1 ∣ w.period)) = true)
    (he : (((scan w scale K (w.period - 1) 0 w.halfDen 0).2 : ℤ) : ℚ) ≤
      probeBound w.cutoff * (scale : ℚ) * (w.den : ℚ) ^ 2)
    (ht : (((scan w scale K (w.period - 1) 0 w.halfDen 0).2 -
      (scan w scale K w.cutoff 0 w.halfDen 0).2 : ℤ) : ℚ) ≤
      tailProbeBound w.cutoff * (scale : ℚ) * (w.den : ℚ) ^ 2) :
    ∃ v ∈ upperSpan (greenPeriod w.cutoff) w.cutoff (atom (greenPeriod w.cutoff)),
      let P := greenPeriod w.cutoff
      let f := fun r => fittedMomentProbe w.cutoff r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound w.cutoff : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 w.cutoff) (progressionWeight P) f ≤
          (tailProbeBound w.cutoff : ℝ) := by
  rw [hperiod]
  have hP : 0 < w.period := by omega
  exact ⟨w.correction, w.correction_mem hv hP,
    energy_le_of_scan w scale K hP (by decide) hd hp _ he,
    tail_energy_le_of_scan w scale K hx (by decide) hd hp _ ht⟩

private def five : Witness where
  period := 30
  cutoff := 5
  halfDen := 9550000000000000000000
  head := [(1, 11100000000000000000000), (2, -700000000000000000000),
    (3, -12500000000000000000000), (5, -36100000000000000000000)]
  upper := [(6, 6670592336970732965211), (10, -22012266128825447461596),
    (15, -27365054179730234105386)]

private theorem five_head (r : ℕ) : fittedMomentProbe five.cutoff r = five.probe r := by
  have mu2 : ArithmeticFunction.moebius 2 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu3 : ArithmeticFunction.moebius 3 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu4 : ArithmeticFunction.moebius 4 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu5 : ArithmeticFunction.moebius 5 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [fittedMomentProbe, five, Witness.probe, Witness.den, columns,
    affineMomentDual, mass, energy, weight, sum_Icc_one, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one, mu2, mu3, mu4, mu5]
  ring

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel replays the exact arithmetic of each consecutive residue block.
private theorem five_scan :
    scan five scale 256 29 0 9550000000000000000000 0 =
      (-3042782910501802832266,
        2294486400978966381496482565536016388848970702491702100063435753369) := by
  decide +kernel

private theorem five_certificate :
    ∃ v ∈ upperSpan (greenPeriod 5) 5 (atom (greenPeriod 5)),
      let P := greenPeriod 5
      let f := fun r => fittedMomentProbe 5 r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound 5 : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 5) (progressionWeight P) f ≤
          (tailProbeBound 5 : ℝ) := by
  refine of_witness five 256 (by decide) (by decide) (by decide) five_head (by decide) ?_ ?_
  · change ((scan five scale 256 29 0 9550000000000000000000 0).2 : ℚ) ≤ _
    rw [five_scan]
    decide +kernel
  · change (((scan five scale 256 29 0 9550000000000000000000 0).2 -
      (scan five scale 256 5 0 9550000000000000000000 0).2 : ℤ) : ℚ) ≤ _
    rw [five_scan]
    decide +kernel

private def seven : Witness where
  period := 210
  cutoff := 7
  halfDen := 8850000000000000000000
  head := [(1, 6250000000000000000000), (2, 2200000000000000000000),
    (3, -1850000000000000000000), (5, -9950000000000000000000),
    (6, -14000000000000000000000), (7, -18050000000000000000000)]
  upper := [(10, 7462372924742740424877), (14, -12200084510705293796934),
    (15, -7947261808532185659816), (21, -21344803890110071513530),
    (30, -8509957700336286581388), (35, -14044041364910417602818),
    (42, -29330064746638033044006), (70, -16645512793296347735499),
    (105, -37123811604897305505435)]

private theorem seven_head (r : ℕ) : fittedMomentProbe seven.cutoff r = seven.probe r := by
  have mu2 : ArithmeticFunction.moebius 2 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu3 : ArithmeticFunction.moebius 3 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu4 : ArithmeticFunction.moebius 4 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu5 : ArithmeticFunction.moebius 5 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu6 : ArithmeticFunction.moebius 6 = (1 : ℤ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 3)
    norm_num [mu2, mu3] at h
    exact h
  have mu7 : ArithmeticFunction.moebius 7 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [fittedMomentProbe, seven, Witness.probe, Witness.den, columns,
    affineMomentDual, mass, energy, weight, sum_Icc_one, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one, mu2, mu3, mu4, mu5, mu6, mu7]
  ring

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel replays the exact arithmetic of each consecutive residue block.
private theorem seven_scan :
    scan seven scale 32 209 0 8850000000000000000000 0 =
      (-7952087489756446863615,
        1598818474263312500232155284027357994657536986660802875551248196387) := by
  decide +kernel

private theorem seven_certificate :
    ∃ v ∈ upperSpan (greenPeriod 7) 7 (atom (greenPeriod 7)),
      let P := greenPeriod 7
      let f := fun r => fittedMomentProbe 7 r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound 7 : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 7) (progressionWeight P) f ≤
          (tailProbeBound 7 : ℝ) := by
  refine of_witness seven 32 (by decide) (by decide) (by decide) seven_head (by decide) ?_ ?_
  · change ((scan seven scale 32 209 0 8850000000000000000000 0).2 : ℚ) ≤ _
    rw [seven_scan]
    decide +kernel
  · change (((scan seven scale 32 209 0 8850000000000000000000 0).2 -
      (scan seven scale 32 7 0 8850000000000000000000 0).2 : ℤ) : ℚ) ≤ _
    rw [seven_scan]
    decide +kernel

private def eleven : Witness where
  period := 2310
  cutoff := 11
  halfDen := 1155450000000000000000000
  head := [(1, 504340000000000000000000), (2, 270380000000000000000000),
    (3, 36420000000000000000000), (5, -431500000000000000000000),
    (6, -665460000000000000000000), (7, -899420000000000000000000),
    (10, -1601300000000000000000000), (11, -1835260000000000000000000)]
  upper := [(14, 345651321172798970149272), (15, 78762970887904707423900),
    (21, -1347420909049348545637221), (22, -1721937979503804925546404),
    (30, -1418247116455153554687939), (33, -1268620172103188431179222),
    (35, -915535834810613464768338), (42, -1326350706844054632066744),
    (55, -1850077587462327561153291), (66, -1393630793118704064317493),
    (70, -902429912971855748358645), (77, -1312820174586004847700528),
    (105, -1431446085082415371396572), (110, -2629187258642783440928046),
    (154, -1601796676839315707086746), (165, -2008846733906070470875368),
    (210, -3495998801671087704025140), (231, -3378259852445060287633656),
    (330, -3743729623723775296164789), (385, -3195909263252892508739187),
    (462, -3529546820660267622758403), (770, -3997692796074957695036556),
    (1155, -4525165236205971703229331)]

private theorem eleven_head (r : ℕ) : fittedMomentProbe eleven.cutoff r = eleven.probe r := by
  have mu2 : ArithmeticFunction.moebius 2 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu3 : ArithmeticFunction.moebius 3 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu4 : ArithmeticFunction.moebius 4 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu5 : ArithmeticFunction.moebius 5 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu6 : ArithmeticFunction.moebius 6 = (1 : ℤ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 3)
    norm_num [mu2, mu3] at h
    exact h
  have mu7 : ArithmeticFunction.moebius 7 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu8 : ArithmeticFunction.moebius 8 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu9 : ArithmeticFunction.moebius 9 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (3 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 3 (by decide)))
  have mu10 : ArithmeticFunction.moebius 10 = (1 : ℤ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 5)
    norm_num [mu2, mu5] at h
    exact h
  have mu11 : ArithmeticFunction.moebius 11 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [fittedMomentProbe, eleven, Witness.probe, Witness.den, columns,
    affineMomentDual, mass, energy, weight, sum_Icc_one, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11]
  ring

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel replays the exact arithmetic of each consecutive residue block.
private theorem eleven_scan :
    scan eleven scale 8 2309 0 1155450000000000000000000 0 =
      (-1173865161634433515171257,
        19529319781543690115508966178719011105860482595404275947455282425682324) := by
  refine scan_eq_of_split (a := 512) (b := 1797)
    (mid := (1255927877204268450134038,
      19508063720072093521741615305959867255023209170451200103974316230992607))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 1285)
    (mid := (439717689374806498756204,
      19521032066999280177776666537092764882667910731421215880061850730568740))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 773)
    (mid := (-140116129989529791518882,
      19525816299056235386194497257318603799969857840133654553939652663988284))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 261)
    (mid := (941980158797433536648674,
      19528402407270775767418559037489973112794433155449588445063776530819653))
    (by decide +kernel) ?_
  decide +kernel

private theorem eleven_certificate :
    ∃ v ∈ upperSpan (greenPeriod 11) 11 (atom (greenPeriod 11)),
      let P := greenPeriod 11
      let f := fun r => fittedMomentProbe 11 r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound 11 : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 11) (progressionWeight P) f ≤
          (tailProbeBound 11 : ℝ) := by
  refine of_witness eleven 8 (by decide) (by decide) (by decide) eleven_head (by decide) ?_ ?_
  · change ((scan eleven scale 8 2309 0 1155450000000000000000000 0).2 : ℚ) ≤ _
    rw [eleven_scan]
    decide +kernel
  · change (((scan eleven scale 8 2309 0 1155450000000000000000000 0).2 -
      (scan eleven scale 8 11 0 1155450000000000000000000 0).2 : ℤ) : ℚ) ≤ _
    rw [eleven_scan]
    decide +kernel

private def thirteen : Witness where
  period := 30030
  cutoff := 13
  halfDen := 13216950000000000000000000
  head := [(1, 5772325000000000000000000), (2, 3093700000000000000000000),
    (3, 415075000000000000000000), (5, -4942175000000000000000000),
    (6, -7620800000000000000000000), (7, -10299425000000000000000000),
    (10, -18335300000000000000000000), (11, -21013925000000000000000000),
    (13, -26371175000000000000000000)]
  upper := [(14, -5392291819988245272165315), (15, -2241371183741588362580208),
    (21, -16697371782199835773215738), (22, -19568649540798110338770231),
    (26, -19549024075652850806181003), (30, -15348707181636680232613791),
    (33, -13721931852559163746784397), (35, -8481552394520400867632115),
    (39, -25635145589910920388730473), (42, -16806219612928243413400449),
    (55, -20206997106226739297353242), (65, -11414532965139002303026677),
    (66, -18985252626039049671953133), (70, -16145904883345935627346794),
    (77, -15038319699309416342678289), (78, -27831223426954737044169171),
    (91, -13073175728587737916191864), (105, -20365363318218210823827546),
    (110, -26050270866363357095238957), (130, -21659184403704288249650514),
    (143, -13512214055519355120422409), (154, -23200070680489607714694771),
    (165, -24305513187736204762212135), (182, -27926862255153105913602855),
    (195, -32115929158847391500977956), (210, -35681171061427533769597470),
    (231, -38243728464822795410388153), (273, -37586704204655115838233039),
    (286, -42508217042852784812752689), (330, -42172359867921107381887089),
    (385, -30657455463584569796555850), (390, -46945845948194864273651463),
    (429, -43220787453501490110027087), (455, -25005768718122620632249992),
    (462, -36951443706807729882802656), (546, -42551832296208659734733463),
    (715, -30497775838413114352126212), (770, -43071842307301629117002820),
    (858, -55689936662569755689269632), (910, -40275071736173688874817295),
    (1001, -32131456451070247847457567), (1155, -49478905276670772263145285),
    (1365, -48642865734377113605179163), (1430, -51638887706584187832021477),
    (2002, -52505332098954119339610555), (2145, -56092974061359995069419980),
    (2310, -65534665486607820252213696), (2730, -67377503777830634349729117),
    (3003, -62945565158947584085132023), (4290, -82595784197784729122813232),
    (5005, -48977320589317047729509415), (6006, -72030900657765614794876332),
    (10010, -73703749432140434903840019), (15015, -79541321390760099567553884)]

private theorem thirteen_head (r : ℕ) : fittedMomentProbe thirteen.cutoff r = thirteen.probe r := by
  have mu2 : ArithmeticFunction.moebius 2 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu3 : ArithmeticFunction.moebius 3 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu4 : ArithmeticFunction.moebius 4 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu5 : ArithmeticFunction.moebius 5 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu6 : ArithmeticFunction.moebius 6 = (1 : ℤ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 3)
    norm_num [mu2, mu3] at h
    exact h
  have mu7 : ArithmeticFunction.moebius 7 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu8 : ArithmeticFunction.moebius 8 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu9 : ArithmeticFunction.moebius 9 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (3 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 3 (by decide)))
  have mu10 : ArithmeticFunction.moebius 10 = (1 : ℤ) := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 5)
    norm_num [mu2, mu5] at h
    exact h
  have mu11 : ArithmeticFunction.moebius 11 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  have mu12 : ArithmeticFunction.moebius 12 = (0 : ℤ) := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro h
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp (h 2 (by decide)))
  have mu13 : ArithmeticFunction.moebius 13 = (-1 : ℤ) := by
    exact ArithmeticFunction.moebius_apply_prime (by decide)
  norm_num [fittedMomentProbe, thirteen, Witness.probe, Witness.den, columns,
    affineMomentDual, mass, energy, weight, sum_Icc_one, Finset.sum_range_succ,
    ArithmeticFunction.moebius_apply_one, mu2, mu3, mu4, mu5, mu6, mu7, mu8, mu9, mu10, mu11, mu12, mu13]
  ring

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
-- The kernel replays the exact arithmetic of each consecutive residue block.
private theorem thirteen_scan :
    scan thirteen scale 4 30029 0 13216950000000000000000000 0 =
      (-13232357386352280428718708,
        2549427457524436305860329810385542777668987686076112109219761407829817547) := by
  refine scan_eq_of_split (a := 512) (b := 29517)
    (mid := (8606337356302956035668925,
      2546748245215636874886676460288144833615983744555009606529716347875183647))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 29005)
    (mid := (16760029187050759192057404,
      2548072097110926116783809887664349800697421527340948699604894757518914131))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 28493)
    (mid := (2336220913679059614747708,
      2548521585486165557524004743420518325275831182100826244335090822674848709))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 27981)
    (mid := (12610261337770200461547453,
      2548765344620988218283384022051952830874481626129914241064530020983004284))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 27469)
    (mid := (5877411316600618897508231,
      2548884020190894178052608911187013854772766168267456450852523506502225310))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 26957)
    (mid := (-12190047975817967449444315,
      2548976966309876718708224449067896389197787929494887017086563958219386194))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 26445)
    (mid := (-7268900594437599395923207,
      2549046291428744501427272974060517692855474345019064479567163163135762235))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 25933)
    (mid := (17118228716015774962773074,
      2549099080357144891058835728383269658327146928398501876003341142928558863))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 25421)
    (mid := (5734908583573910130328638,
      2549137063705199397277110997186564490244955420067447942905497449056487538))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 24909)
    (mid := (-12958375566338318244627589,
      2549166993293306650700964940892463159607220872127402867536787347658031827))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 24397)
    (mid := (-1027105548261784650579791,
      2549191392272481748102789959178695116191703268411140352107339506354538156))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 23885)
    (mid := (-7904691300979803376274557,
      2549211893674743865172706026905896243212992551282982312870999827380907547))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 23373)
    (mid := (-9191755324348201967881916,
      2549232353916817055468955575838746966096183589760947522818147237097700553))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 22861)
    (mid := (7262737446073421443520138,
      2549247686736317855336920827291705080218383889195187617624500110953782178))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 22349)
    (mid := (-11091350899546062869762895,
      2549263212017444800625010012085482270228665447054985025976565420731857950))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 21837)
    (mid := (6434580653990580250290402,
      2549274014158285479162463508231990850461130029072614843729252649256359728))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 21325)
    (mid := (23418201251274719477605387,
      2549284645307775560331017038858385778914245228043161269126394641046921018))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 20813)
    (mid := (18727976853336362549546700,
      2549294257322790796586166905360349429032326963515480918890755870732756644))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 20301)
    (mid := (5490263892197169992089015,
      2549302812396028107847464538676982864179887718986444457630353956883315764))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 19789)
    (mid := (4956661872115131899792322,
      2549312241046336341268140375645686852373761056925820019455882775826835864))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 19277)
    (mid := (-13046932423304397671120396,
      2549319194552348487939242764592645803561214909236526866514472299390424565))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 18765)
    (mid := (-8251467325052762200062722,
      2549325479059743709760581271598353449631312509018751658753437201498385368))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 18253)
    (mid := (6496040900062737944968187,
      2549331098361913046736974646291134563892385432274149695664978799527725262))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 17741)
    (mid := (4897414092542530526260082,
      2549336930202088388115417044587946238046909767702929554792515077704707359))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 17229)
    (mid := (-24980272583493917770243419,
      2549342256681409617068701307457364856142279860611260597509829741959808622))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 16717)
    (mid := (1923085857649586432820209,
      2549347889486264838927292213554566244015166763587652502137526455703269179))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 16205)
    (mid := (-5983886923399225287509835,
      2549352041293025828792788927922545534880637442509937149824315980932305271))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 15693)
    (mid := (-5335931342635762076379514,
      2549356286072525305834031530587968245502969256148727163872169201166017235))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 15181)
    (mid := (13438141911713189907742974,
      2549361428068602598896407670502810038908735364639666090642112167998360517))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 14669)
    (mid := (-15275083332670547988994652,
      2549365241480794194401849714163156592036203507930287588177345059956863873))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 14157)
    (mid := (-11133523015134697202163492,
      2549370065399325294689912915197326482014024247164459561298208143371538551))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 13645)
    (mid := (15924131196604357819629428,
      2549373048298533570315300885774617178730906382675174659751300203291088282))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 13133)
    (mid := (26636083161976664838590720,
      2549376040146293605239477948349752039689970008110296006704950940509554929))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 12621)
    (mid := (10003315778599723634433680,
      2549379704888699469814078607305419997259245690878360434451035520799854447))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 12109)
    (mid := (-1672746198967870129611882,
      2549382626491386100852691387790536306032396151941990442560691831148195693))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 11597)
    (mid := (-2867032553649959231315354,
      2549385301071349194096505563952070515338858883062882441936547774281786109))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 11085)
    (mid := (-6697205012872069550510584,
      2549387801212675203676704364370981355108151230221740430910517263236860730))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 10573)
    (mid := (9605283866384756257514325,
      2549390220020276480181487498842720614599241187908675192861071088454251736))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 10061)
    (mid := (-1097806734253605528023679,
      2549392649258631781617201505750576827393153106412090660371700311446551385))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 9549)
    (mid := (-13085648519404477039106627,
      2549395476948450987253394893823476046239840824173175836027313431554401593))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 9037)
    (mid := (-7365534996297437064676723,
      2549397692929042963147765928310614988216740525553289534157856533368421775))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 8525)
    (mid := (1805014474195610638152704,
      2549399982210095485892816876361925976198397044704481254746872599677510498))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 8013)
    (mid := (-3454623257763409946266401,
      2549401966955523661476636054584307925988363814599620241276798411726630001))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 7501)
    (mid := (8378450881623948565533490,
      2549404009901033892692191797485366171891574076927878274351992387381797663))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 6989)
    (mid := (2366210523645559419521750,
      2549406013098413534147579114977041160690522261128511769048068804355668595))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 6477)
    (mid := (-13663922377499030622178222,
      2549407983038632314773952694991130916889644896921019712559692552882178644))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 5965)
    (mid := (8990128904810918847565698,
      2549410026393913625107751480537489395328623336911964255877686001933714623))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 5453)
    (mid := (17025500519976990383675277,
      2549411680436693258865023327321575665053897491989467168483756141055019860))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 4941)
    (mid := (24204694480318413959641227,
      2549413296596578047156354185503809250128608546838939627088828983667785019))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 4429)
    (mid := (-250083974056733085003416,
      2549414863944787909137900121446458518442865151792560381897604807324274144))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 3917)
    (mid := (3110803312459087467400850,
      2549416419172904652321809599375567794714145596752276264587060245402672713))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 3405)
    (mid := (2731730038131687307276524,
      2549418370824177097940393142691044369699439932910794048089242170180473149))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 2893)
    (mid := (6843364122977575361513194,
      2549419823653771634421740491629109692761070227196855228795295772912642488))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 2381)
    (mid := (-3284654854583840784890241,
      2549421320708070661796389550946735354560856875478183001988175122224683963))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 1869)
    (mid := (-21478748661148152648244677,
      2549422679087586175413928282850144893843991324627311327723529214381399671))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 1357)
    (mid := (-606814938640695804056702,
      2549424093608312501070554071369524506759053190183657081568771866435314117))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 845)
    (mid := (-4810532367408068952413367,
      2549425517193027614518514621016207362407311778431233958660918688815129055))
    (by decide +kernel) ?_
  refine scan_eq_of_split (a := 512) (b := 333)
    (mid := (2044816489684819622434312,
      2549426716239138755654276479907459771182985117759410289902413102274731368))
    (by decide +kernel) ?_
  decide +kernel

private theorem thirteen_certificate :
    ∃ v ∈ upperSpan (greenPeriod 13) 13 (atom (greenPeriod 13)),
      let P := greenPeriod 13
      let f := fun r => fittedMomentProbe 13 r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound 13 : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 13) (progressionWeight P) f ≤
          (tailProbeBound 13 : ℝ) := by
  refine of_witness thirteen 4 (by decide) (by decide) (by decide) thirteen_head (by decide) ?_ ?_
  · change ((scan thirteen scale 4 30029 0 13216950000000000000000000 0).2 : ℚ) ≤ _
    rw [thirteen_scan]
    decide +kernel
  · change (((scan thirteen scale 4 30029 0 13216950000000000000000000 0).2 -
      (scan thirteen scale 4 13 0 13216950000000000000000000 0).2 : ℤ) : ℚ) ≤ _
    rw [thirteen_scan]
    decide +kernel

/-- The same upper-span correction certifies both energies at each listed cutoff. -/
theorem centered_probe_energy_bounds (x : ℕ) (hx : x ∈ ({5, 7, 11, 13} : Finset ℕ)) :
    ∃ v ∈ upperSpan (greenPeriod x) x (atom (greenPeriod x)),
      let P := greenPeriod x
      let f := fun r => fittedMomentProbe x r - (1 / 2 : ℝ) * target P r - v r
      energy (Finset.Icc 1 (P - 1)) (progressionWeight P) f ≤ (probeBound x : ℝ) ∧
        energy (Finset.Icc 1 (P - 1) \ Finset.Icc 1 x) (progressionWeight P) f ≤
          (tailProbeBound x : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact five_certificate
  · exact seven_certificate
  · exact eleven_certificate
  · exact thirteen_certificate

/-- The actual signed-moment gap satisfies the two-sided squared estimate. -/
theorem fitted_moment_gap_sq_le (x : ℕ) (hx : x ∈ ({5, 7, 11, 13} : Finset ℕ)) :
    (atomFittedMoment (greenPeriod x) x - (1 / 2 : ℝ) * atomEnergy (greenPeriod x) x) ^ 2 ≤
      atomEnergy (greenPeriod x) x * (tailProbeBound x : ℝ) := by
  obtain ⟨v, hv, _, ht⟩ := centered_probe_energy_bounds x hx
  have hq : 0 ≤ atomEnergy (greenPeriod x) x :=
    energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg _ r)
  exact (fitted_moment_gap_sq_le_tail x (1 / 2) v hv).trans
    (mul_le_mul_of_nonneg_left ht hq)

/-- The finite additive budget retains the cutoff-specific endpoint and any positive slope loss. -/
theorem fitted_moment_deficit (x : ℕ) (hx : x ∈ ({5, 7, 11, 13} : Finset ℕ))
    (eps : ℝ) (heps : 0 < eps) :
    atomFittedMoment (greenPeriod x) x ≤
      (1 / 2 + eps) * atomEnergy (greenPeriod x) x + (tailProbeBound x : ℝ) / (4 * eps) := by
  obtain ⟨v, hv, _, ht⟩ := centered_probe_energy_bounds x hx
  have hM : 0 ≤ (tailProbeBound x : ℝ) :=
    (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg _ r)).trans ht
  exact fitted_moment_deficit_of_tail_probe_bound x _ _ _ hM heps v hv ht

theorem fitted_moment_three_quarters (x : ℕ) (hx : x ∈ ({5, 7, 11, 13} : Finset ℕ)) :
    atomFittedMoment (greenPeriod x) x ≤ (3 / 4 : ℝ) * atomEnergy (greenPeriod x) x +
      (tailProbeBound x : ℝ) := by
  simpa only [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num,
    show (4 : ℝ) * (1 / 4 : ℝ) = 1 by norm_num, div_one] using
    fitted_moment_deficit x hx (1 / 4) (by norm_num)

theorem fitted_moment_three_quarters_common
    (x : ℕ) (hx : x ∈ ({5, 7, 11, 13} : Finset ℕ)) :
    atomFittedMoment (greenPeriod x) x ≤
      (3 / 4 : ℝ) * atomEnergy (greenPeriod x) x + 32283 / 1000000 := by
  have hb : (tailProbeBound x : ℝ) ≤ 32283 / 1000000 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num [tailProbeBound]
  linarith only [fitted_moment_three_quarters x hx, hb]

end RiemannResearch.RH.Pareto.ExactHeadProbeWitnesses

import RiemannResearch.RH.ParetoGroupedResidueMassBatch00
import RiemannResearch.RH.ParetoGroupedResidueMassBatch01
import RiemannResearch.RH.ParetoGroupedResidueMassBatch02
import RiemannResearch.RH.ParetoGroupedResidueMassBatch03
import RiemannResearch.RH.ParetoGroupedResidueMassBatch04
import RiemannResearch.RH.ParetoGroupedResidueMassBatch05
import RiemannResearch.RH.ParetoGroupedResidueMassBatch06
import RiemannResearch.RH.ParetoGroupedResidueMassBatch07
import RiemannResearch.RH.ParetoGroupedResidueMassBatch08
import RiemannResearch.RH.ParetoGroupedResidueMassBatch09
import RiemannResearch.RH.ParetoGroupedResidueMassBatch10
import RiemannResearch.RH.ParetoGroupedResidueMassBatch11
import RiemannResearch.RH.ParetoGroupedResidueMassBatch12
import RiemannResearch.RH.ParetoGroupedResidueMassBatch13
import RiemannResearch.RH.ParetoGroupedResidueMassBatch14
import RiemannResearch.RH.ParetoGroupedResidueMassBatch15

namespace RiemannResearch.RH.GroupedResidueMass.Conductor241
private theorem splitBatches (N : ℕ) :
    (∑ j ∈ Finset.range (N*32), block j) = ∑ j ∈ Finset.range N, headBatch j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ headBatch N]
    simp only [headBatch]

private theorem sum_sixteen_batches (b : ℕ → ℕ)
    (h0 : b 0 = 8497304208)
    (h1 : b 1 = 49933911)
    (h2 : b 2 = 17311211)
    (h3 : b 3 = 8739062)
    (h4 : b 4 = 5167841)
    (h5 : b 5 = 3398415)
    (h6 : b 6 = 2455934)
    (h7 : b 7 = 1929281)
    (h8 : b 8 = 1407149)
    (h9 : b 9 = 1203962)
    (h10 : b 10 = 1132738)
    (h11 : b 11 = 738996)
    (h12 : b 12 = 713311)
    (h13 : b 13 = 625231)
    (h14 : b 14 = 485750)
    (h15 : b 15 = 419019) :
    (∑ j ∈ Finset.range 16, b j) = 8592966019 := by
  rw [Finset.sum_range_succ b 15, h15,
    Finset.sum_range_succ b 14, h14,
    Finset.sum_range_succ b 13, h13,
    Finset.sum_range_succ b 12, h12,
    Finset.sum_range_succ b 11, h11,
    Finset.sum_range_succ b 10, h10,
    Finset.sum_range_succ b 9, h9,
    Finset.sum_range_succ b 8, h8,
    Finset.sum_range_succ b 7, h7,
    Finset.sum_range_succ b 6, h6,
    Finset.sum_range_succ b 5, h5,
    Finset.sum_range_succ b 4, h4,
    Finset.sum_range_succ b 3, h3,
    Finset.sum_range_succ b 2, h2,
    Finset.sum_range_succ b 1, h1,
    Finset.sum_range_succ b 0, h0, Finset.sum_range_zero] <;> decide

theorem head_units_total : (∑ j ∈ Finset.range 512, block j) = 8592966019 :=
  (splitBatches 16).trans (sum_sixteen_batches headBatch
    headBatch_0 headBatch_1 headBatch_2 headBatch_3 headBatch_4 headBatch_5 headBatch_6 headBatch_7
    headBatch_8 headBatch_9 headBatch_10 headBatch_11 headBatch_12 headBatch_13 headBatch_14 headBatch_15)

end RiemannResearch.RH.GroupedResidueMass.Conductor241

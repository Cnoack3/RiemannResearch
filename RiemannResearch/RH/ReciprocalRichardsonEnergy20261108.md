# External reciprocal-energy results

Exact rational certificates and separately marked floating-point diagnostics. These numeric outputs were independently reproduced outside Lean.

```json
{
  "floating_status": "external long-double; no rounding certification",
  "integer_status": "exact integer outward rational enclosures plus proved analytic integral tails; external calculation, not Lean",
  "floating": [
    {
      "family": "Richardson",
      "n": 2,
      "N": 64,
      "T": 1000000,
      "prefix_energy": 0.6517906405436609,
      "energy_tail_budget": 3.1660321287354474e-05,
      "reciprocal_error_sq": 0.005360673645370372,
      "reciprocal_tail_budget": 1.3680855711727582e-17,
      "signed_range_bound": 7.216587909319021,
      "seconds": 0.12101173400878906
    },
    {
      "family": "Richardson",
      "n": 3,
      "N": 19683,
      "T": 30000000,
      "prefix_energy": 0.8086962287610524,
      "energy_tail_budget": 0.008299921882511023,
      "reciprocal_error_sq": 0.0014904647345769138,
      "reciprocal_tail_budget": 3.083659217107736e-18,
      "signed_range_bound": 639.9880684056878,
      "seconds": 5.080326557159424
    },
    {
      "family": "first_order_same_cutoff",
      "n": 3,
      "N": 19683,
      "T": 30000000,
      "prefix_energy": 0.4875291262305603,
      "energy_tail_budget": 0.0022264672675029076,
      "reciprocal_error_sq": 0.014642081987434535,
      "reciprocal_tail_budget": 8.296005436438765e-19,
      "signed_range_bound": 331.46908711241906,
      "seconds": 4.9258646965026855
    }
  ],
  "integer": [
    {
      "family": "first_order",
      "n": 2,
      "N": 16,
      "T": 200000,
      "scale_bits": 80,
      "zeta_series_cutoff": 100000,
      "complete_energy_lower_rational": "155666201199299736334584/497150816259240862726513",
      "complete_energy_upper_rational": "1505566710279457172030148486186556912100476949262961/4808147663853979972800798567267612656496719953920000",
      "complete_energy_lower_float_for_display": 0.3131166561700406,
      "complete_energy_upper_float_for_display": 0.31312821808651925,
      "complete_energy_outward_decimal": [
        "0.313116656170",
        "0.313128218087"
      ],
      "complete_reciprocal_error_sq_lower_rational": "60228748370998919485489/1988603265036963450906052",
      "complete_reciprocal_error_sq_upper_rational": "145624177977547321583933858864585866414357174337710269923004163/4808147663853979972800798567267612656496719953920000000000000000",
      "complete_reciprocal_error_sq_lower_float_for_display": 0.030286960415847154,
      "complete_reciprocal_error_sq_upper_float_for_display": 0.030286960417688583,
      "complete_reciprocal_error_sq_outward_decimal": [
        "0.030286960415847",
        "0.030286960417689"
      ],
      "pointwise_bound_upper_rational": "1178890476078392597534845/604462909807314587353088",
      "seconds": 0.4986844062805176
    },
    {
      "family": "first_order",
      "n": 2,
      "N": 64,
      "T": 200000,
      "scale_bits": 80,
      "zeta_series_cutoff": 100000,
      "complete_energy_lower_rational": "677265791811138784146671/1988603265036963450906052",
      "complete_energy_upper_rational": "40944861716179271821394275186800852422022233028302369/120203691596349499320019964181690316412417998848000000",
      "complete_energy_lower_float_for_display": 0.34057360948693305,
      "complete_energy_upper_float_for_display": 0.34062898711692097,
      "complete_energy_outward_decimal": [
        "0.340573609486",
        "0.340628987117"
      ],
      "complete_reciprocal_error_sq_lower_rational": "55554677967884993235567/1988603265036963450906052",
      "complete_reciprocal_error_sq_upper_rational": "402968907574523024586630464081841357769810304110676265191085601/14424442991561939918402395701802837969490159861760000000000000000",
      "complete_reciprocal_error_sq_lower_float_for_display": 0.027936531607199368,
      "complete_reciprocal_error_sq_upper_float_for_display": 0.027936531608898394,
      "complete_reciprocal_error_sq_outward_decimal": [
        "0.027936531607199",
        "0.027936531608899"
      ],
      "pointwise_bound_upper_rational": "2580037415946458329988463/604462909807314587353088",
      "seconds": 0.518341064453125
    },
    {
      "family": "Richardson",
      "n": 2,
      "N": 64,
      "T": 200000,
      "scale_bits": 80,
      "zeta_series_cutoff": 100000,
      "complete_energy_lower_rational": "324037468088816933202740/497150816259240862726513",
      "complete_energy_upper_rational": "104488641035339149782743369252199584112723702329469427/160271588795132665760026618908920421883223998464000000",
      "complete_energy_lower_float_for_display": 0.6517890698178932,
      "complete_energy_upper_float_for_display": 0.6519473714639584,
      "complete_energy_outward_decimal": [
        "0.651789069817",
        "0.651947371464"
      ],
      "complete_reciprocal_error_sq_lower_rational": "10660253113657074003693/1988603265036963450906052",
      "complete_reciprocal_error_sq_upper_rational": "458220630497116171152218691674316493577583758668787708346707/85478180690737421738680863418090891671052799180800000000000000",
      "complete_reciprocal_error_sq_lower_float_for_display": 0.005360673645207419,
      "complete_reciprocal_error_sq_upper_float_for_display": 0.005360673645535016,
      "complete_reciprocal_error_sq_outward_decimal": [
        "0.005360673645207",
        "0.005360673645536"
      ],
      "pointwise_bound_upper_rational": "8724319453094519789399909/1208925819614629174706176",
      "seconds": 0.5242431163787842
    }
  ],
  "exact_comparison": {
    "Richardson_n2_energy_strictly_larger_than_both_first_order_cutoffs": true,
    "Richardson_n2_reciprocal_error_strictly_smaller_than_both_first_order_cutoffs": true
  }
}
```

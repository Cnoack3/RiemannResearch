# Complete-Q energy of the finite Richardson family

Date: 8 November 2026.

This note records an external exact-integer enclosure calculation and separate floating-point diagnostics. The integer calculation is not a Lean-checked arithmetic computation. Every endpoint displayed as a rational number in the accompanying JSON was constructed using Python arbitrary-precision integers and rational fractions; its generic enclosure argument is given below. Floating diagnostic rows have no rounding certificate.

## Families and conclusion

Write Z = zeta(2), Q(k)=1/(Z k^2), g_m(k)=(k mod m)/m, and Bv(k)=v(k)/(k+1). The first-order family is

    v_n = -sum_(2<=m<=n^(2n)) mu(m) m^(-1/n) g_m.

The finite Richardson family is

    w_n = -sum_(2<=m<=n^(3n)) mu(m)
                 [2m^(-1/n)-m^(-2/n)] g_m.

The energy is the entire sum E(v)=sum_(k>=1) Q(k)v(k)^2, and the reciprocal squared error is D(v)=sum_(k>=1) Q(k)[(v(k)-1)/(k+1)]^2.

At n=2 the exact rational enclosures prove that Richardson increases the unsmoothed energy and decreases the reciprocal error. A first-order control with the same cutoff N=64 is included, so this conclusion does not depend only on increasing the conductor cutoff from 16 to 64. This is a finite-stage observation; it proves no asymptotic boundedness or subpower-energy claim.

## Exact coefficient enclosures

Set S=2^80. For each squarefree conductor m, compute

    q_m = isqrt(floor(S^2/m)),
    q'_m = q_m if q_m^2 m=S^2, and q_m+1 otherwise.

Exact integer assertions check q_m^2 m <= S^2 <= (q'_m)^2 m. Therefore q_m/S <= 1/sqrt(m) <= q'_m/S. The positive first-order coefficient has integer bounds q_m and q'_m. The positive Richardson coefficient 2/sqrt(m)-1/m has integer bounds

    2q_m-ceil(S/m),  2q'_m-floor(S/m).

Multiply these intervals by the exact integer mu(m), reversing endpoints for mu(m)=-1. Write the resulting scaled coefficient bounds as A_m^- <= S a_m <= A_m^+. The script verifies the sign of every nonzero coefficient interval.

The Möbius sieve uses integer and Boolean arithmetic: each prime changes the sign at its multiples, and every multiple of its square is set to zero.

## Retaining signed cross terms in the physical prefix

For v(k)=-sum_m a_m g_m(k), define C=sum_m a_m/m. The exact identity

    v(k) = sum_m a_m floor(k/m) - k C

is used before squaring. Thus all signed cross terms in the finite physical prefix are retained.

Integer density bounds are

    C^- = sum_m floor(A_m^-/m),
    C^+ = sum_m ceil(A_m^+/m).

Divisor increments form

    F_k^- = sum_m A_m^- floor(k/m),
    F_k^+ = sum_m A_m^+ floor(k/m).

Hence V_k^- = F_k^- - k C^+ and V_k^+ = F_k^+ - k C^- satisfy V_k^-/S <= v(k) <= V_k^+/S. The implementation builds the F prefixes from divisor increments using integer additions; it never rounds a signed physical value to floating point.

For an integer interval [L,U], define square_min(L,U)=0 if it contains zero and min(L^2,U^2) otherwise, and square_max(L,U)=max(L^2,U^2). Directed integer division gives

    P^- = sum_(k=1)^T floor(square_min(V_k^-,V_k^+) / (S k^2)),
    P^+ = sum_(k=1)^T ceil(square_max(V_k^-,V_k^+) / (S k^2)).

These enclose the prefix sum of v(k)^2/k^2 after division by S. For the reciprocal error replace [V_k^-,V_k^+] by [V_k^--S,V_k^+-S] and replace the denominator S k^2 by S k^2(k+1)^2, producing R^- and R^+.

## The zeta normalization is also enclosed by integers

With K=100000, use the decreasing-series integral bounds

    1/(K+1) <= sum_(k>K) 1/k^2 <= 1/K.

Define

    Z^- = sum_(k=1)^K floor(S/k^2) + floor(S/(K+1)),
    Z^+ = sum_(k=1)^K ceil(S/k^2) + ceil(S/K).

Then 0 < Z^-/S <= zeta(2) <= Z^+/S. No floating-point value of pi is used in the integer certificate.

## Entire omitted tails

Because 0 <= g_m(k) <= 1-1/m, separate positive and negative coefficients before taking the maximum. A scaled integer upper bound for |v(k)| at every physical site is

    U = max(sum_(a_m>0) ceil(A_m^+(m-1)/m),
            sum_(a_m<0) ceil((-A_m^-)(m-1)/m)).

The resulting bound |v(k)|<=U/S holds uniformly, including all omitted sites. The exact inequalities

    sum_(k>T) 1/k^2 <= 1/T,
    sum_(k>T) 1/[k^2(k+1)^2] <= sum_(k>T)1/k^4 <= 1/(3T^3)

give the complete rational enclosures

    P^-/Z^+ <= E(v) <= P^+/Z^- + U^2/(S Z^- T),

    R^-/Z^+ <= D(v) <= R^+/Z^- + (U+S)^2/(3 S Z^- T^3).

These bounds concern complete Q energies, not just their prefixes. For n=2 the physical cutoff is T=200000. Decimal interval endpoints below are rounded outward by integer division; the longer rational endpoints are exact.

## Reproduction and interpretation

Save the Python block in [MobiusRichardsonEnergyScript20261108.md](MobiusRichardsonEnergyScript20261108.md) as `mobius_richardson_energy_experiment.py`, then run `python3 mobius_richardson_energy_experiment.py --certificate-only --output /tmp/reciprocal_energy_certificate.json`. The checked-in output is [ReciprocalRichardsonEnergy20261108.md](ReciprocalRichardsonEnergy20261108.md). By default the script emits a JSON file next to itself with exact rational endpoints, outward decimal intervals, separate floating rows, and assertions of the strict comparisons. The --output option chooses its destination. The --certificate-only option recomputes the rational certificate using only the Python standard library; NumPy is imported only for the separate floating diagnostics. The first-order and Richardson complete-energy assertions compare rational Fractions, not displayed decimals.

The reciprocal acceleration therefore comes with a real finite-stage increase in the unsmoothed energy. The observed energies remain below the target constant's energy 1, so this increase alone is not evidence of divergence or instability. The RH criterion still requires a cofinal subpower bound for the complete unsmoothed energies. Neither these finite values nor the improved reciprocal rate supply that missing bound.

## Numerical and exact rational output


| n=2 family | cutoff | complete energy, outward interval | reciprocal squared error, outward interval |
|---|---:|---|---|
| first_order | 16 | [0.313116656170, 0.313128218087] | [0.030286960415847, 0.030286960417689] |
| first_order | 64 | [0.340573609486, 0.340628987117] | [0.027936531607199, 0.027936531608899] |
| Richardson | 64 | [0.651789069817, 0.651947371464] | [0.005360673645207, 0.005360673645536] |

The following exact rational inequalities are the primary numerical certificate; every denominator is positive.

first_order, n=2, N=16:

    155666201199299736334584/497150816259240862726513 <= E <= 1505566710279457172030148486186556912100476949262961/4808147663853979972800798567267612656496719953920000

    60228748370998919485489/1988603265036963450906052 <= D <= 145624177977547321583933858864585866414357174337710269923004163/4808147663853979972800798567267612656496719953920000000000000000

first_order, n=2, N=64:

    677265791811138784146671/1988603265036963450906052 <= E <= 40944861716179271821394275186800852422022233028302369/120203691596349499320019964181690316412417998848000000

    55554677967884993235567/1988603265036963450906052 <= D <= 402968907574523024586630464081841357769810304110676265191085601/14424442991561939918402395701802837969490159861760000000000000000

Richardson, n=2, N=64:

    324037468088816933202740/497150816259240862726513 <= E <= 104488641035339149782743369252199584112723702329469427/160271588795132665760026618908920421883223998464000000

    10660253113657074003693/1988603265036963450906052 <= D <= 458220630497116171152218691674316493577583758668787708346707/85478180690737421738680863418090891671052799180800000000000000

Separate long-double diagnostics:

| family | n | N | T | energy prefix | analytic omitted-energy budget, floating | reciprocal squared error prefix |
|---|---:|---:|---:|---:|---:|---:|
| Richardson | 2 | 64 | 1000000 | 0.6517906405436609 | 3.166032128735447e-05 | 0.005360673645370372 |
| Richardson | 3 | 19683 | 30000000 | 0.8086962287610524 | 0.008299921882511023 | 0.001490464734576914 |
| first_order_same_cutoff | 3 | 19683 | 30000000 | 0.4875291262305603 | 0.002226467267502908 | 0.01464208198743453 |

The n=3 floating rows show the same trend even at a common conductor cutoff. Their rounding is not enclosed, so they remain diagnostic rather than rational certificates.

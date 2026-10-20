# Wolfram symbolic checks through the seventh primorial

Run for the 20 October 2026 continuation. Maximum period 510510; no eighth or later primorial was evaluated.

## Scope

Exact symbolic/rational checks: all seven primorials 2, 6, 30, 210, 2310, 30030, 510510, retaining every nontrivial divisor. Legal dictionary dimensions 1, 3, 7, 15, 31, 63, 127. For each period, both divisor incidence inverse identities, all gcd-class charge formulas, all divisibility moments, total class cardinality, and the centered square decomposition passed. These verify the algebraic consequences of the normal equations, not a fresh solution of the rational optimizer normal equations.

Full-period exact integer checks: Mobius synthesis passed at every n=0,...,L for all seven periods, 543105 cases total. The literal CRT carry identity passed at every n=0,...,L for one canonical split L=p*d with p the largest prime factor, at all six composite primorials, 543102 cases total. These do not test every CRT split or representative.

No floating-point approximations, extrapolation, infinite-limit claims, or optimizer solves are used here.

## Algebraic checks

For D=divisors(L), Z[d,e]=1_(d|e) and M[e,d]=mu(d/e)1_(e|d), verify ZM=MZ=I. The divisibility moment vector y[d]=5/(3Ld) maps under M to b[e]=5 phi(L/e)/(3L^2). Set c=5/(3L^2), n[e]=phi(L/e). The symbolic arbitrary quadratic totals q[e] satisfy sum_e(q[e]-2c b[e]+n[e]c^2)=sum_e q[e]-Lc^2.

```wl
Module[{levels = {2, 6, 30, 210, 2310, 30030, 510510}, rows, a, ell, k, telescope},
 rows = Table[
   Module[{ds = Divisors[ll], z, mob, target, endpoint, card, c, centered},
    z = Table[Boole[Divisible[ee, dd]], {dd, ds}, {ee, ds}];
    mob = Table[If[Divisible[dd, ee], MoebiusMu[dd/ee], 0], {ee, ds}, {dd, ds}];
    target = (5 EulerPhi[ll/#]/(3 ll^2) &) /@ ds;
    endpoint = (5/(3 ll #) &) /@ ds;
    card = (EulerPhi[ll/#] &) /@ ds; c = 5/(3 ll^2);
    centered = Expand[Total[Table[q[j] - 2 c target[[j]] + card[[j]] c^2, {j, Length[ds]}]] -
      (Total[Array[q, Length[ds]]] - ll c^2)];
    <|"Primorial" -> ll, "Squarefree" -> SquareFreeQ[ll],
      "AllDivisors" -> Length[ds], "LegalAtoms" -> Length[ds] - 1,
      "IncidenceTimesMobius" -> (z.mob == IdentityMatrix[Length[ds]]),
      "MobiusTimesIncidence" -> (mob.z == IdentityMatrix[Length[ds]]),
      "AllClassCharges" -> (mob.endpoint == target),
      "AllDivisibilityMoments" -> (z.target == endpoint),
      "ClassCardinalitiesSum" -> (Total[card] == ll),
      "CenteredQuadraticIdentity" -> (centered == 0)|>
   ], {ll, levels}];
 telescope = Together[
   2/(ell (2 a + (2 k - 1) ell)) -
   2/(ell (2 a + (2 k + 1) ell)) -
   1/(a + k ell)^2 -
   ell^2/((a + k ell)^2 (4 (a + k ell)^2 - ell^2))];
 <|"MaximumPrimorial" -> Max[levels], "Rows" -> rows,
   "TelescopingGapIdentity" -> (telescope == 0),
   "GapNonnegative" -> FullSimplify[
     ell^2/((a + k ell)^2 (4 (a + k ell)^2 - ell^2)) >= 0,
     Assumptions -> a > 0 && ell > 0 && k >= 1 && Element[{a, ell, k}, Reals]]|>
]
```

Raw tool result:

```text
Out[1]= <|"MaximumPrimorial" -> 510510, "Rows" -> {<|"Primorial" -> 2, "Squarefree" -> True, "AllDivisors" -> 2, "LegalAtoms" -> 1, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 6, "Squarefree" -> True, "AllDivisors" -> 4, "LegalAtoms" -> 3, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 30, "Squarefree" -> True, "AllDivisors" -> 8, "LegalAtoms" -> 7, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 210, "Squarefree" -> True, "AllDivisors" -> 16, "LegalAtoms" -> 15, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 2310, "Squarefree" -> True, "AllDivisors" -> 32, "LegalAtoms" -> 31, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 30030, "Squarefree" -> True, "AllDivisors" -> 64, "LegalAtoms" -> 63, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>, <|"Primorial" -> 510510, "Squarefree" -> True, "AllDivisors" -> 128, "LegalAtoms" -> 127, "IncidenceTimesMobius" -> True, "MobiusTimesIncidence" -> True, "AllClassCharges" -> True, "AllDivisibilityMoments" -> True, "ClassCardinalitiesSum" -> True, "CenteredQuadraticIdentity" -> True|>}, "TelescopingGapIdentity" -> True, "GapNonnegative" -> True|>
```

## Complete residue checks

The integer-scaled Mobius identity tested is -sum_(d|L,d>1) mu(d)(L/d)(n mod d)=L*C_L(n)-phi(L)n. For the CRT split, a=d^{-1} mod p and b=p^{-1} mod d, so qnum=a*d*(n mod p)+b*p*(n mod d). The exact integer check L*Quotient[qnum,L]=qnum-(n mod L) is equivalent to floor(a*g_p(n)+b*g_d(n))=a*g_p(n)+b*g_d(n)-g_L(n).

```wl
Module[{levels = {2, 6, 30, 210, 2310, 30030, 510510}, rows},
 rows = Table[Module[{ns = Range[0, ll], ds = Rest[Divisors[ll]], c, lhs, pp, dd, aa, bb, num, crt},
    c = Accumulate[Prepend[(Boole[CoprimeQ[#, ll]] &) /@ Range[ll], 0]];
    lhs = Fold[#1 - MoebiusMu[#2] (ll/#2) Mod[ns, #2] &, ConstantArray[0, ll + 1], ds];
    crt = If[ll == 2, "NotApplicable", pp = Last[First /@ FactorInteger[ll]]; dd = ll/pp;
      aa = PowerMod[dd, -1, pp]; bb = PowerMod[pp, -1, dd];
      num = aa dd Mod[ns, pp] + bb pp Mod[ns, dd];
      ll Quotient[num, ll] == num - Mod[ns, ll]];
    <|"Primorial" -> ll, "ResiduesIncludingEndpoints" -> ll + 1,
      "MobiusSynthesisAllResidues" -> (lhs == ll c - EulerPhi[ll] ns),
      "CanonicalCRTAllResidues" -> crt|>
 ], {ll, levels}];
 <|"MaximumPrimorial" -> Max[levels], "MobiusResidueCases" -> Total[levels + 1],
   "CRTResidueCases" -> Total[Rest[levels] + 1], "Rows" -> rows|>
]
```

Raw tool result:

```text
Out[1]= <|"MaximumPrimorial" -> 510510, "MobiusResidueCases" -> 543105, "CRTResidueCases" -> 543102, "Rows" -> {<|"Primorial" -> 2, "ResiduesIncludingEndpoints" -> 3, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> "NotApplicable"|>, <|"Primorial" -> 6, "ResiduesIncludingEndpoints" -> 7, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>, <|"Primorial" -> 30, "ResiduesIncludingEndpoints" -> 31, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>, <|"Primorial" -> 210, "ResiduesIncludingEndpoints" -> 211, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>, <|"Primorial" -> 2310, "ResiduesIncludingEndpoints" -> 2311, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>, <|"Primorial" -> 30030, "ResiduesIncludingEndpoints" -> 30031, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>, <|"Primorial" -> 510510, "ResiduesIncludingEndpoints" -> 510511, "MobiusSynthesisAllResidues" -> True, "CanonicalCRTAllResidues" -> True|>}|>
```

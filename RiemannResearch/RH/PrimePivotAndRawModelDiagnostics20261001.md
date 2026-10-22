# Wolfram diagnostics for the exact prime-pivot continuation

Date: October 1, 2026. These are exact finite checks and numerical illustrations, separate from the Lean proofs in [the continuation report](PrimePivotAndRawModelContinuation20261001.md).

The exact two/four-site checks gave zero for every observation residual (conductors 2 through p, including composites) and every norm residual at the six pairs below.

| p | r | Exact dual norm squared 2p^2+2r^2 | Bertrand bound 10p^2 |
|---|---|---|---|
| 3 | 5 | 68 | 90 |
| 5 | 7 | 148 | 250 |
| 7 | 11 | 340 | 490 |
| 11 | 13 | 580 | 1210 |
| 13 | 17 | 916 | 1690 |
| 17 | 19 | 1300 | 2890 |

The full physical-tail Gram matrix for conductors 2 through 17 was computed by periodic digamma sums at 30-digit working precision, then screened against every earlier conductor. No physical cutoff was substituted. Successful values (rounded here):

| p | Actual 1/sigma_p | 4p^2+2C_<=p-4C_<p | Two-site Cauchy slack |
|---|---|---|---|
| 3 | 9.052180535227 | 25.810061849379 | 5.415612976756 |
| 5 | 19.766872342750 | 82.905760173776 | 16.518472919354 |
| 7 | 32.141371749555 | 159.631680931065 | 48.210692908651 |
| 11 | 67.063528134409 | 436.614513791831 | 162.238284652361 |
| 13 | 87.185216004755 | 626.676787676512 | 214.705529909285 |
| 17 | 134.110099080889 | 1096.691824195964 | 424.681560599048 |

The slack is 2p^2-C_<p-(eta_p-1)^2/sigma_p. Positivity at these scales is a diagnostic; the exact formal completion and Cauchy inequality prove the universal statement.

For the norm/energy distinction, c_j=1/j and m_j=1 gave:

| N | Energy saving M_N-T_N | Norm saving sqrt(M_N)-sqrt(T_N) |
|---|---|---|
| 10 | 4.3081687768 | 0.7765217583 |
| 100 | 8.7397711351 | 0.4469780245 |
| 1000 | 13.3270071544 | 0.2114252642 |
| 10000 | 17.9303780002 | 0.0896921134 |

The ordinary harmonic-number argument proves the asymptotics; the finite table only illustrates them.

## Reproduction

The kernel is stateless; run the definitions and computation together. This script reconstructs the exact finite checks and the same full-tail numerical quantities. Extra guard digits may change the final displayed rounding.

~~~wolfram
ClearAll[zSite, tailValue, periodicWeight, tailGram];
zSite[pp_, kk_] := Piecewise[
  {{pp (pp + 1), kk == pp}, {-pp (pp - 1), kk == pp - 1}}, 0];
tailValue[dd_, kk_] := If[kk == 1, 0, Mod[kk, dd]/dd];

pList = {3, 5, 7, 11, 13, 17};
rList = {5, 7, 11, 13, 17, 19};
observationResiduals = MapThread[
  Function[{pp, rr},
    Table[
      Sum[tailValue[dd, kk] (zSite[rr, kk] - zSite[pp, kk])/
          (kk (kk + 1)), {kk, 1, rr}] - If[dd == pp, 1, 0],
      {dd, 2, pp}]], {pList, rList}];
normResiduals = MapThread[
  Function[{pp, rr},
    Sum[(zSite[rr, kk] - zSite[pp, kk])^2/(kk (kk + 1)),
      {kk, 1, rr}] - 2 (pp^2 + rr^2)], {pList, rList}];

periodicWeight[kk_, ell_] :=
  (PolyGamma[0, N[(kk + 1)/ell, 40]] -
   PolyGamma[0, N[kk/ell, 40]])/ell;
tailGram[dd_, ee_] := Module[{ell = LCM[dd, ee]},
  N[Sum[Mod[kk, dd] Mod[kk, ee]/(dd ee) periodicWeight[kk, ell],
      {kk, 1, ell - 1}] - 1/(2 dd ee), 30]];
(* The subtraction removes only physical site 1 of the exact full tail. *)
gram = Table[tailGram[dd, ee], {dd, 2, 17}, {ee, 2, 17}];
pivotTable = Table[
  Module[{old, inverse, cross, source, sigma, eta, cold, cnew},
    old = Take[gram, pp - 2, pp - 2];
    inverse = Inverse[old];
    cross = gram[[pp - 1, 1 ;; pp - 2]];
    source = N[1/Range[2, pp - 1], 30];
    sigma = gram[[pp - 1, pp - 1]] - cross.inverse.cross;
    eta = 1/pp - cross.inverse.source;
    cold = source.inverse.source;
    cnew = cold + eta^2/sigma;
    N[{pp, cold, cnew, 1/sigma, 4 pp^2 + 2 cnew - 4 cold,
       2 pp^2 - cold - (eta - 1)^2/sigma}, 12]], {pp, pList}];

normExamples = Table[
  Module[{aa = HarmonicNumber[nn, 2], hh = HarmonicNumber[nn]},
    {nn, N[2 hh - aa, 12],
     N[Sqrt[nn] - Sqrt[nn + aa - 2 hh], 12]}],
  {nn, {10, 100, 1000, 10000}}];
{observationResiduals, normResiduals, pivotTable, normExamples}
~~~

The digamma identity used is
sum_(m>=0) 1/[(k+mL)(k+mL+1)] =
[psi((k+1)/L)-psi(k/L)]/L for 1<=k<L.
Each residue product is periodic and the omitted k=L class is zero. This accounts for every physical tail site before the first-site subtraction.

Finite numerical matrix inversion is not a proof of asymptotic pivot control or of RH. The new unconditional bound is instead kernel checked from an exact finite-support dual and the formal Bertrand theorem.

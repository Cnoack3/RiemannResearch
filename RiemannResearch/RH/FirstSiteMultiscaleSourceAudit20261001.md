# Audit continuation: source floors, multiscale scatter and moving CRT contrasts

Date: October 1, 2026 UTC.
Audited base: `be45e99a22abe009356faf7dd686248b4ebb77d5`.
Integrated research base: `eb1d81748c27b5e05805e5d9ace2576f1e466158`.
Input: `RH_be45e99_Independent_Audit(2).md`.

## Outcome

The six audited declarations and the relevant forward RH chain were independently
rechecked. The unconditional advances are:

1. The exact two-child scatter identity now allows zero-source children.
2. Complete binary-tree scatter accounting resolves all internal scales.
3. Explicit reciprocal-prime floors discharge nonnegativity and both finite
   child-source comparisons; stronger harmonic floors assemble the newly
   published adjacent-conductor estimate and dominate those earlier floors.
4. Every fixed Hilbert-vector contribution, including the fixed CRT base and
   any finite signed column packet, preserves dyadic contrast summability even
   when the balanced tests vary arbitrarily with the block.
5. More generally, a signed row correction with proved weighted square
   summability preserves the same contrast summability target.

The nonsummability of the actual moving screened arithmetic remains Open.
No unconditional capacity divergence or proof of RH is claimed.
The developments are elementary weighted regression and Bessel consequences;
no mathematical novelty is claimed merely because these declarations are new.

## Reverification of the attachment

At the exact base, fresh source compilation returned exit code zero for:

| File | SHA-256 of checked source |
| --- | --- |
| Analysis/WeightedScalarEnergy.lean | `db751187ff0161408bdc81f47a45a15fe516455e2fb6e90fdb567c17b63930e3` |
| RH/ParetoFirstSitePrimeBlockContrast.lean | `af5f0f7a917c2c60e4505c2e4f0cb9a62c85c5ba627547d417157d84d8ddac34` |

The hashes reproduce those in the attachment. The workspace used its exact
commit cache and matching Lean v4.33.0-rc2 dependency environment. This does
not mean that every dependency was rebuilt from source.

A successful ephemeral Lean job printed axioms for all six requested
declarations and eleven supporting declarations, including the actual
point-error identity and the imported PNT theorem `pi_alt'`. Every report
contained only `propext`, `Classical.choice` and `Quot.sound`.
The printed split-gap type kept `hv`, `hleft`, `hright`, `hgap` and
`hdiv` explicitly. Axiom output does not discharge local hypotheses.

GitHub's combined status list and the connector's PR-triggered workflow-run
list were empty on the base. This does not assert absence of every possible
Actions run or check-run category.

Source inspection followed the block, angular, alignment, budget, CRT,
tail-capacity, first-point, coefficient and Mellin chains. It confirmed
that the base pairing, every earlier signed screened cross-Gram entry,
the infinite physical tail, initial capacity and all nonprime gains remain.
The unscreened negative-entry formula was not substituted for screened rows.

The forward chain uses no RH-to-approximation provider:

split/contrast nonsummability -> angular nonsummability -> capacity divergence
-> vanishing first-point error -> coefficient targets -> legal closure
-> continuous Mellin separation -> Mathlib RiemannHypothesis.

The historical full-build statement in the input is a report of its earlier
run. This continuation verifies its own changed modules and their affected
dependencies through the publication checkpoint; it does not relabel that
earlier run as a new from-source rebuild.

## Exact identities and their assumptions

Write `w_n=primeSchurWeight n`, `a_n=factorialPrimeDelta n>0`,
`b_n=factorialPrimeError n`. On a finite block define
U=sum w*a^2, X=sum w*a*b, V=sum w*b^2 and S=V-X^2/U.

The original source-balanced test completion remains exact:
S=L^2/D + completeContrastRemainder.
Both D=0 and U=0 use real division by zero, with the nonnegative Gram
inequality supplying the required vanishing source pairing.

For two consecutive children, Gram positivity proves U=0 implies X=0.
Consequently the canonical `primeBlockVariance_split` now has no
positive-child-source hypotheses:

S_parent = S_L + S_R + H_split,

H_split = U_L*U_R/(U_L+U_R) * (X_R/U_R-X_L/U_L)^2
        = (U_L*X_R-U_R*X_L)^2/[U_L*U_R*(U_L+U_R)].

Every identity is valid at empty source children. The angular equality still
requires a positive preceding cutoff N and retains historical head--block drift.
The finite split-gap estimate still explicitly requires a nonnegative common
lower witness v below both actual child source budgets.

## Complete binary-tree scatter

`ParetoFirstSitePrimeMultiscale.lean` defines T(N,0)=0 and

T(N,h+1)=T(N,h)+T(N+2^h,h)+H_split(N,2^h,2^h).

A singleton has zero scatter, since its source value a_n is positive;
nonprime zero-weight singletons also have zero scatter. Induction proves

S(N,2^h)=T(N,h).

Thus every internal split is included once and no child scatter disappears.
The exact capacity identity is

C_(2^J+1)=C_1+R_(2^J)
          +sum_(j<J) T(2^j,j)
          +sum_(j<J) historicalDrift(2^j,2^j)
          +nonprimeGainBudget(2^J).

The module gives the exact angular summability equivalence and retains all
four capacity-growth alternatives. Nonsummability of T(2^j,j) is sufficient
for RH, but is not asserted necessary for RH: the mean, historical-drift
and nonprime channels remain.

Interpretation: with mu_n=w_n*a_n^2 and y_n=b_n/a_n, each split is a weighted
Haar contrast of the actual signed y_n. The aligned constant component cancels
in these contrasts. This identifies a complete finite scatter decomposition,
not an arithmetic lower bound.

## Unconditional finite source floors

`ParetoFirstSitePrimeSourceFloors.lean` proves

F(N,k)=sum_(i<k, N+i+3 prime) 1/[8(N+i+3)] <= U(N,k).

The proof uses the existing checked per-prime normalized defect estimate.
Its finite counting bridge also proves

numberOfPrimesInBlock/[8(N+k+2)] <= F(N,k),

where the numerator is represented exactly as the real sum of prime indicators.

Taking the minimum of the two child floors supplies `hv`, `hleft` and
`hright` unconditionally. A stronger finite lower coefficient keeps unequal
child masses:

W_floor=F_L*F_R/(F_L+F_R) <= U_L*U_R/(U_L+U_R).

`reciprocalPrimeSplitEnergy` multiplies this floor by the square of the
actual screened slope difference. Its comparison with the full block variance
is checked. Its nonsummability endpoint has only the actual energy-divergence
hypothesis; no source provider is concealed.

## A substantive moving-row reduction

`ParetoFirstSitePrimeContrastPerturbations.lean` concerns arbitrary tests f_j.
Let c_j be their actual source-balanced tests, D_j=sum w*c_j^2 and

B_j(z)=sum_(n in block_j) w_n*c_j(n)*inner(tailInnovation(n+1),z).

The weighted Gram inequality gives

B_j(z)^2/D_j <= sum_(n in block_j)
                  inner(tailInnovation(n+1),z)^2/schurSigma(n+1).

Dyadic blocks are disjoint. Bessel makes the latter series summable for
every fixed Hilbert vector z. Hence sum B_j(z)^2/D_j is finite, without
uniform size or regularity assumptions on the changing tests.

The existing weighted square-perturbation theorem therefore proves

Summable((L_j-B_j(z))^2/D_j) iff Summable(L_j^2/D_j).

This applies to z=the fixed factorial-2 certificate and to any fixed vector
sum_(m in finite s) a_m*factorialPrimeRefinement(m). The coefficients and
the finite packet must remain independent of j.

In particular put A_j=sum w*c_j*sum_(m<n) factorialPrimeCrossGram(n,m).
The complete signed equality is L_j=A_j+B_j(base), followed by

L_j^2/D_j=A_j^2/D_j+2*A_j*B_j(base)/D_j+B_j(base)^2/D_j.

The signed cross term is retained exactly. The theorem removes the base
only from the summability question:

Summable(actualContrastCertificate_j)
iff Summable(movingCRTContrastCertificate_j).

Nonsummability of these actual moving screened CRT contrasts is a sufficient
RH provider, still Open. The unchanged capacity equality still contains
the actual full contrasts and their remainders.

The more general transfer theorem permits any signed correction e_n satisfying
sum w_n*e_n^2<infinity. The weighted norm condition is explicit; no estimate
for the growing all-column correction has been invented. It gives a precise
criterion for transferring future trustworthy arithmetic model estimates to
the actual screened contrasts.

## Published prime estimates isolate the harmonic gap

The following analytic consequence is proved here in ordinary mathematics.
The finite floor comparison above is Lean-verified. Dusart's explicit
prime-count theorem and the resulting numerical eventual bound are NOT
new Lean imports in this commit. No project-local axiom is introduced.

Source: P. Dusart, *Estimates of Some Functions Over Primes without R.H.*,
[arXiv:1002.0442](https://arxiv.org/pdf/1002.0442), Theorem 6.9, equation (6.6),
printed page 9. It gives pi(x)>=x/(log x-1) for x>=5393 and
pi(y)<=y/(log y-11/10) for y>=60184, without assuming RH.

Let N=2^j, j>=17, X=4N+2, L=log X, a=11/10+log 2.
The children contain primes in (2N+2,3N+2] and (3N+2,4N+2].
For either interval endpoints y<x, we have x-y=N, x<=X, y>=X/2.
All Dusart thresholds and positive-denominator conditions hold. Thus

pi(x)-pi(y) >= x/L-y/(L-a)
             = (N*L-x*a)/[L(L-a)]
             >= (N*L-X*a)/[L(L-a)]
             >= N/(2L).

The last comparison is equivalent to L>=(7+4/N)*a. Indeed

L-(7+4/N)*a >= 12*log 2-77/10-4*a/N
            >= 3/10-42/(5N) > 0,

using 2/3<=log 2<=1 and N>=2^17. Every prime is <=X, so both source floors
and both actual sources are at least

N/(16*X*L) >= 1/(80L) >= 1/[80(j+3)log 2].

For the ACTUAL screened pooled slope gap G_j the audited finite estimate yields

angularBlock_j >= G_j^2/[160(j+3)log 2],  j>=17.

Therefore sum G_j^2/(j+3)=infinity is a sufficient arithmetic provider.
A fixed nonzero gap on any index set with divergent harmonic weight suffices.
The gap has not been proved. Mere prime density supplies its weight, not
its sign or magnitude.

The existing PNT theorem `pi_alt'` also has no local hypotheses and its
printed axioms are standard. It yields the same eventual 1/j source scale.
Formal interval reindexing and the eventual source-rate corollary remain a
separate implementation task, not an unresolved assertion of PNT.

## Stronger harmonic floors from the updated repository

During publication, origin/main advanced to
`eb1d81748c27b5e05805e5d9ace2576f1e466158`. The first checkpoint compiled
and committed the development on the audited base but could not publish:
a concurrent theorem-catalog insertion caused an integration conflict.
All results were preserved and integrated into a fresh workspace on that
newer commit; both catalog entries and the newer root exports are retained.

The newer `ParetoAdjacentSchurBound.lean` proves, for p=n+3 prime,

source_n >= 1/[4 H_(p-1)].

Its actual Schur-pivot comparison retains the full inverse-Gram projection
remainder and the literal infinite adjacent-residue tail before bounding them.
It supplies a positive source bound, not a signed gain or gap estimate.

`ParetoFirstSitePrimeSourceFloors.lean` also assembles that stronger result:

F_H(N,k)=sum_(i<k, N+i+3 prime) 1/[4 H_(N+i+2)] <= U(N,k),

numberOfPrimesInBlock/[4 H_(N+k+1)] <= F_H(N,k).

It also proves F_H>=F for the earlier reciprocal-prime floor. The stronger
harmonic split energy uses F_H,L*F_H,R/(F_H,L+F_H,R) and the identical ACTUAL
signed screened pooled slope gap. It dominates the reciprocal split energy
and lies below the complete parent variance, including zero-source children.
Its RH endpoint keeps nonsummability of this actual stronger energy explicit.

Combining the ordinary Dusart count calculation above with
H_m<=1+log m gives, for N=2^j and j>=17, both child sources at least

N/[8 L(1+L)], where L=log(4N+2).

Therefore the actual complete parent scatter, and hence its angular budget,
satisfies

S(2N,2N) >= N*G_j^2/[16 L(1+L)]
         >= 2^j*G_j^2/[32(j+3)^2(log 2)^2].

Here 1+L<=2L and L<=(j+3)log 2 were used. Thus divergence of
sum 2^j*G_j^2/(j+3)^2 is a stronger sufficient research route than the
earlier reciprocal-floor criterion. It permits much smaller actual gaps,
but that divergence is still Open. The finite harmonic comparisons are
Lean-verified; the analytic Dusart rate assembly is ordinary mathematics,
not an installed Lean provider. No signed term or retained capacity channel
is replaced by positive source mass.

## Literature screening and remaining research

Primary sources were inspected beyond their abstracts.

- [Burnol, arXiv:math/0103058](https://arxiv.org/pdf/math/0103058), Theorem 1.3:
  its multiplicity-sensitive approximation-error lower bound constrains rates
  but does not prove convergence or give screened slope separation.
- [Bettin--Conrey--Farmer, arXiv:1211.5191](https://arxiv.org/pdf/1211.5191),
  Theorem 1: the optimal asymptotic assumes RH plus a reciprocal-zeta-derivative
  moment bound. It cannot supply an unconditional provider here.
- [Ehm, arXiv:2405.06349v2](https://arxiv.org/html/2405.06349v2), Section 8
  and Proposition 8.2: exact Gram and Mobius-convolution decompositions are
  useful signed model candidates. Their products with growing moments require
  control; centered moments tending to zero alone do not supply it.
- The imported large-sieve modules provide upper energy comparisons with
  explicit spacing assumptions. No screened lower singular value, gap or
  sign estimate follows just by reversing such an upper inequality.
- [Carvill, arXiv:2510.18132](https://arxiv.org/pdf/2510.18132), proof of
  Theorem 6.1: its phase lower bound is false. For indices (3,0),(0,2),
  |3 log 2-2 log 3|=log(9/8)<5 log 2. The smoothing proof was therefore
  not imported. Wolfram checked this counterexample and regression algebra;
  these calculations supplement mathematical proofs, not the Lean kernel.

Repository searches also revisited exact CRT screening, fixed cross-Gram
columns, stretched inverse transfer, sparse derivative Gram bounds and
full sieve energies. Fixed inverse-Gram diagonals already have checked
dual-norm bounds. The unresolved inverse-transfer issue is a MOVING physical
tail times the arithmetic growth factor, not the total fixed diagonal norm.
Sparse derivative Gram comparisons cannot silently replace the legal
screened Gram. No unconditional actual screened-gap provider was found.

The concrete research sequence is now:

1. Express the moving CRT Haar/contrast pairings through signed arithmetic
   convolutions before taking absolute values.
2. Compare a useful explicit arithmetic model with those actual rows; prove
   the weighted square-summability condition of the new transfer theorem,
   or retain its nonnegligible remainder in an exact energy equality.
3. Establish a divergent model contrast series, a divergent complete tree
   budget, or a separate retained capacity channel.
4. Apply the checked forward endpoint only after the provider is proved.

The open obligations are actual signed divergence or a comparison strong
enough to supply it. Neither PNT, Bessel, independence of auxiliary random
signs, nor raw Gram sparsity discharges that obligation.

## Verification and publication scope

All newly developed proof candidates were submitted to the Lean kernel in
one serialized verification stream. Original source checks, new snippet
checks, source auditing and final project validation are distinct evidence.
The publication checkpoint validates changed modules and local reverse
dependents, including the root export. Build and publication evidence must be assessed separately from cache
housekeeping errors; the observed records follow.

No substantive growth hypothesis is relabeled as established. Axioms and
precise new declaration types are checked again after the project build.

### Observed publication and post-build evidence

The proof commit is
[78e1dcaa2a0acdb7aa117425a6231cc1c95442b1](https://github.com/Cnoack3/RiemannResearch/commit/78e1dcaa2a0acdb7aa117425a6231cc1c95442b1).
The checkpoint completed source auditing, affected-module and reverse-dependent
validation, commit and push. Its outer job subsequently finished with failure
while copying the project build cache: `Errno 28, No space left on device`.
This is not reported as a globally successful checkpoint job.

Independent GitHub lookup confirmed that proof commit on main. The workspace
reported `state: published`, identical HEAD and origin/main, and a clean tree.
The missing cache snapshot does not mean the source or commit was lost.

After publication, Lean imported the committed modules and checked the exact
declaration types: zero-source split without positivity hypotheses; arbitrary
tests with a fixed Hilbert vector or fixed finite column packet; the explicit
weighted-square-summability premise for row corrections; and the actual
nonsummability premises of all four new RH endpoints. That job returned exit 0.

A separate untruncated axiom check of 17 key published declarations returned
exit 0 and only `propext`, `Classical.choice`, `Quot.sound` for every entry.
Its code SHA-256 is
`fd89a7d41367d495e23f89a79ecb3c0b374105a3cf415bae4b9c9077e1baff1c`.
The check covered split/determinant/tree/capacity identities, both source-floor
families, fixed/moving/finite-column/general-row contrast transfer, the exact
signed square, and the explicit conditional RH endpoints.

# Remaining formalization for RH and Montgomery positive-gap pair correlation

The two main proof obligations are the vanishing of the actual centered unit boundary and the microscopic signed limit for the actual zero ordinates. Lean proves criteria equivalent to each. The results below refer to the November 24 closeout of the RH/PCC ledger. [Source ledger](RH_PCC_CLOSURE_LEDGER.md)

## Rank one and the ambient constant

For a mixed-orthogonal probe $h$, write $f_h(a)$ for its residue pairing and $C(v)=\langle v,\mathbf 1\rangle_P$ for the mean of a legal vector. The Fekete coefficient is computed on integer exponents,
$$
R(h)=\frac{1}{\log 2}\inf_{k\ge1}\frac{f_h(2^k)}{k}.
$$
Coprime additivity and vanishing dyadic variation give the cross-base logarithmic rigidity. Fekete's theorem identifies the infimum with the normalized power-sequence limit. The rank-one proof uses this coefficient on each residue generator and extends the equality to the closed legal space. Testing at the legal mean-one seed $u$ gives $R(h)=\langle u,h\rangle_P$. The arithmetic variation hypothesis is supplied for these actual pairings. [Fekete slopes](NumberTheory/FeketePowerSlope.lean) · [Bilinear forms](RH/MixedConductorBilinear.lean)

The remaining scalar is exact. With $E$ the limiting squared projection error,
$$
\operatorname{defectForm}(v,w)=\frac{E}{1-E}\,C(v)C(w),\qquad
\operatorname{defectForm}(u,u)=\|u-\mathbf 1\|_P^2=\frac{E}{1-E}.
$$
Here $1-E>0$. Proving $E=0$, or equivalently $u=\mathbf 1$, would settle the ambient step. At every stage $n$, Lean proves $\partial_n(1)=0\iff\mathrm{RH}$. The squarefree closure criterion and the two-seed density criterion with all positive dilations of 2 and 3 also hold in both directions. [Screened norm identity](RH/MixedConductorRankOne.lean) · [Stage equivalence](RH/CenteredMeanSquarefreeConverse.lean) · [Two-seed equivalences](RH/CenteredMeanTwoSeedConverse.lean)

| Route | Proof still needed |
| --- | --- |
| Finite Gram tail | Find one $C<\infty$ such that for arbitrarily large $N$, and for each such $N$ arbitrarily large $B$, $N\,\mathrm{finiteSectionTailCost}(B,N)\le C$. The cost is exactly the squared norm of the physical tail of the finite mean-one section minus the constant. [Exact cost and equivalence](RH/CenteredMeanGramTail.lean) |
| First-site Gram inequality | Prove the quadratic inequality for every $\varepsilon>0$ at cofinal Gram cutoffs. The published bound supplies $49/2000$ for every $n\ge481$. [Required quantifiers](RH/CenteredMeanDyadicGram.lean) · [Finite bound](RH/CenteredMeanGramUpperBound.lean) |
| Quotient representatives and thresholds | Find representatives of $\partial(1)$ with arbitrarily long zero heads and a common squared Hilbert norm bound. A separate sufficient test asks for legal membership of one difference of distinct positive normalized thresholds. [Bounded representatives](RH/MixedConductorL1Closure.lean) · [Threshold contrast](RH/ParetoCenteredFirstSite.lean) |
| Möbius and parity | Prove interchange against the screened probe on the adjacent-contrast family. The one-site tail tends to $u(1)-1$. For the centered parity error $d_y^2$, the proved interval is $(44/125)^2 E\le d_y^2\le(56/125)^2 E$. An upper coefficient strictly below $(44/125)^2$ would force $E=0$. [Interchange](RH/MobiusParityInterchange.lean) · [Parity bounds](RH/CenteredParityDilationCapacity.lean) |
| Tail capacity and prescribed fits | Show $\sup_K (K+1)q_K=1$ for the legal tail-mean capacity. For the separate prescribed Möbius approximation under RH, exhibit $N(\varepsilon)\to\infty$ with vanishing complete natural tail energy as $\varepsilon\downarrow0$. Freely chosen squarefree coefficients are already supplied under RH. [Capacity gap](RH/LegalTailMeanCapacityMellin.lean) · [Prescribed fits](RH/BalazardDeRotonNaturalTail.lean) |
| Other RH tests | Supply the rational horizontal xi inequalities for left abscissae in $[1/2,1)$, or the cofinal bare variance bound at unfolded width $T^{-2}$. The late-Gram polynomial obstruction separately assumes the continuous Burnol lower envelope. [Horizontal xi](Analysis/XiHorizontalComparison.lean) · [Shrinking width](Analysis/MontgomeryPrescribedArgumentWidth.lean) · [Burnol hypothesis](RH/CenteredMeanBurnolStageBarrier.lean) |

## Actual positive-gap pair correlation

Let $A(T,q)$ be the signed increment of the counting discrepancy over forward windows of unfolded width $q$, clipped at $T$, averaged over actual zero occurrences with multiplicity and divided by $D(T)=T\log T/(2\pi)$. The exact open limit is
$$
\forall q\in\mathbb Q_{>0},\qquad
A(T,q)\longrightarrow\mathrm{sineGapMass}(q)-q
=-\int_0^q\!\left(\frac{\sin(\pi x)}{\pi x}\right)^2\,dx .
$$
This is equivalent to the full positive-gap law, uniformly on compact subintervals of positive widths. The collision-corrected integrated deficit tending to zero at every positive rational width is another equivalent condition. The smooth logarithmic correction after subtracting $A(T,q)$, the mesoscopic count law, and the full macroscopic triangle law are proved. [Signed criterion](Analysis/MontgomerySampledArgumentError.lean) · [Integrated criterion](Analysis/MontgomeryWindowPairCorrelation.lean) · [Smooth drift](Analysis/MontgomerySmoothSampleDrift.lean) · [Full triangle](Analysis/MontgomeryPhysicalTriangleLaw.lean)

- **Prime-probe route.** Write $B_T(q)=\mathrm{primeProbeEnergy}(T,q)$. Centered Mertens and Plancherel prove $B_T(q)-(q-\mathrm{sineGapMass}(q))\to0$ for eventually nonnegative $q=o((\log T)^{3/2})$. For unconditional ordinary PCC, the signed limit $A(T,q)+B_T(q)\to0$ at each fixed positive rational $q$ is still open. With upper bounds on all fixed rational positive-gap shells, it is enough to prove eventual lower bounds $A(T,n)+B_T(n)\ge-\varepsilon$ at arbitrarily large fixed integers chosen before the height limit. The sharp arithmetic threshold $q=o((\log T)^2)$ and its diagonal coefficient are derived in the proof note. Formalizing the uniform Fourier-tail and diagonal-limit arguments would extend the arithmetic theorem in Lean. [Verified arithmetic bound](Analysis/MontgomeryPrimeProbeCenteredPlancherel.lean) · [Cofinal signed criterion](Analysis/MontgomeryCofinalPrimeProbeTrace.lean) · [Arithmetic proof](MONTGOMERY_PRIME_PROBE_MOVING_WIDTHS.md)
- **Determinantal route.** For every rational $0<a<b$, prove both that the omitted-pair triangle loss tends to zero and that the restored prime-projected moment tends to $\int_a^b\mathrm{sineWindowEnergy}(r)\,dr$. Lean proves the finite identity adding these two contributions. [Projection bridge](Analysis/ZeroDPPProjectionBridge.lean)
- **Resolvent route.** The prime heat interchange, Archimedean heat interchange and signed gamma term, and normalized incoming and outgoing height errors are available. Four recovered source drafts still need successful integration in order: the literal all-zero Weil identity, the signed prime-signal approximation, its finite-window mean-square bound, and the resulting fixed-$0<\alpha<1$ sharp form-factor limit. Passing from that complex-zero statistic to the ordinate form factor requires the horizontal budget. [Gamma interchange](Analysis/MontgomeryResolventGammaMixture.lean) · [Signed gamma](Analysis/MontgomeryResolventGammaCentering.lean) · [Boundary limit](Analysis/MontgomeryResolventBoundaryLimit.lean) · [Residual and horizontal criteria](Analysis/MontgomeryFixedFrequencyResidual.lean)
- **Sampling route.** Two source drafts address rational-width sampling along sparse height sequences and one gap-free cutoff in each unit interval. The sampled-cutoff check stopped at the physical-count indicator rewrite. The sampled microscopic sine limit itself would still require an estimate for the actual zeros. [Published gap-free cutoffs](Analysis/MontgomeryGapFreeCutoffs.lean)

The four resolvent drafts are named `MontgomeryResolventExplicitFormula`, `MontgomeryResolventPrimeApproximation`, `MontgomeryResolventErrorEnergy`, and `MontgomeryFixedSubunitResolvent`. The sampling drafts are `MontgomerySampledCutoffs` and `MontgomeryGapFreePCCSampling`. Auxiliary scratch calculations include a signed parity-adjoint tail bound and a Pythagorean identity for doubled legal trials. These have no accepted declaration in this release.

## Verification record

The full project at source commit `ab49c803c6b0ab751f1702659f5c693c7fa20a81` passed the managed Bazel target `//:RiemannResearch`. Every Lean file from the reconciled snapshot `18052fe` is present there byte-for-byte. [Published baseline](https://github.com/Cnoack3/RiemannResearch/commit/ab49c803c6b0ab751f1702659f5c693c7fa20a81) · [Full baseline build](https://app.buildbuddy.io/invocation/4e067126-f020-4d2e-917e-d6604cbe2c79)

# FMZ, Parseval and compact Fourier tests of physical zeta pairs

Compact Orbit identifies “ZMF” with Ford–Meng–Zaharescu (FMZ). Its diagonal Parseval result groups equal prime characters before taking the Haar norm. This development also applies Parseval to the actual rounded Fourier amplitudes of the zero occurrences. Two different limits enter the calculation.

## Exact inversion at a fixed height using primes 2 and 3

For the finite occurrence sample at height $T$, put $Z_T(u)=\sum_j e^{iu\gamma_j}$ and $N_T=\#\{j\}$. The map $t\mapsto(e^{it\log 2},e^{it\log 3})$ is injective. With $n=M+1$, $W_n=\{0,\ldots,n-1\}^2$, and $\omega_a=a_1\log2+a_2\log3$, define
$$
E_{T,n}(s)=\frac1{n^4}\sum_{a,b\in W_n}
      \cos\bigl(s(\omega_a-\omega_b)\bigr)\,
      |Z_T(\omega_a-\omega_b)|^2.
$$
The sum uses finitely many characters on the compact two-prime torus at each $n$. The multiplicity labels include every occurrence of a zero. Lean proves
$$
\lim_{n\to\infty}E_{T,n}(s)
=\#\{(i,j):\gamma_i-\gamma_j=s\}.
$$
Hence the entire finite pair measure can be recovered, and summing the atoms against a test gives its exact finite-height integral. At $s=0$, the limit is $C_T=\sum_y m_T(y)^2$, where $m_T(y)$ counts all occurrence labels at ordinate $y$. Here there is a finite upper certificate
$$
\max(C_T,N_T^2/n^2)\ \le\ E_{T,n}(0),\qquad
\lfloor E_{T,n}(0)\rfloor=C_T\quad\text{eventually for each fixed }T.
$$
The first lower bound follows from the product Fejér kernel on differences, which is nonnegative and equals one on coincident ordinates. The second follows from the $n^2$ terms with $a=b$. For arbitrary translations of all ordinates, $Z_T(u)$ picks up a common unit phase; its modulus and the sums above are invariant.

A symmetric off-line pair or a multiple zero forces $C_T-N_T\ge2$ eventually. Consequently
$$
\mathrm{RH}\ \text{and simple nontrivial zeros}\ \Longleftrightarrow\
\text{for arbitrarily large }T\text{ there is a finite }n\text{ with }E_{T,n}(0)<N_T+2.
$$
Every such certificate requires $n^2>N_T^2/(N_T+2)$. Every fixed window eventually fails the strict certificate as the height increases. This is an absolute finite-count condition. The fixed-height inversion gives no uniform word cutoff or upper estimate as $T$ grows.

Lean files: [TorusCollisionReconstruction](Analysis/TorusCollisionReconstruction.lean), [TwoPrimeCompactCollision](Analysis/TwoPrimeCompactCollision.lean), [TwoPrimeGapAtoms](Analysis/TwoPrimeGapAtoms.lean).

## Bandwidth required for the triangular Fourier certificate

Write $F_T(R)$ for the triangular average of $|Z_T(u)|^2$ over
$[-R,R]$ with weight $(1-|u|/R)/R$. If $N_T\ge 6$, a certificate
$F_T(R)<N_T+2$ requires
$$
  R>\frac{N_T^2}{2T(N_T+2)}.
$$
For fixed $0<c<1/(4\pi)$, every positive bandwidth $R\le c\log T$
therefore fails the certificate at all sufficiently large heights. This
bound follows from the contribution of frequencies near zero and applies
even when the ordinates are simple. The upper bound $F_T(R)<N_T+2$ at
arbitrarily large $T$ remains open.

The generic bound is `triangularBandEnergy_coherent_lower` in
[OrdinateTriangularIntegral](Analysis/OrdinateTriangularIntegral.lean).
The actual-zero declarations `bandwidth_necessary_for_actualTriangular_certificate`
and `eventually_log_band_fails_certificate` are in
[ActualZeroTriangularIntegral](Analysis/ActualZeroTriangularIntegral.lean).

## Selberg comparison on a triangular Fourier window

[ActualSelbergTriangularComparison](Analysis/ActualSelbergTriangularComparison.lean)
proves `selberg_two_triangular_trace_error` for the same zero occurrences
as the collision certificate. Write $Z_T$ for the ordinate sum and $L_T$
for the centered Landau sum. For $0\le R\le\log T$, the Selberg density
bound with slope two and constant $C$ at height $T$ implies
$$
\int_{-1}^{1}(1-|x|)
 \left|\frac{Z_T(Rx)-L_T(Rx)}{T}\right|^2\,dx
 \le \frac{4C^2R^4}{135(\log T)^2}.
$$
The triangular fourth moment is exactly $1/15$. The density premise is
explicit. At a radius proportional to $\log T$, this upper bound is of
order $(\log T)^2$ for fixed $C>0$. The strict upper certificate for every
projected ordinate to be simple remains open.

## Consecutive gaps and all-pairs power

[HomometricConsecutiveGaps](Analysis/HomometricConsecutiveGaps.lean) proves that two sorted lists with the same size, first point, last point, and Fourier power at every real frequency can have different adjacent counts. In [Bloom’s example](https://doi.org/10.1016/0097-3165(77)90013-9), the width-four counts are three and four. A second pair of nine-occurrence lists has three and two tied neighbors. The declaration `sum_difference_power` proves the common-power identity for sums and differences of any two finite real samples.

For actual zeta zeros, let $H(\tau)$ count the occurrences at an occupied height, $C=\sum_\tau H(\tau)^2$, and $Z$ count the tied consecutive pairs. [MicroscopicFirstGapVacancy](Analysis/MicroscopicFirstGapVacancy.lean) proves $Z=N-\#\{\tau\}$ and the finite identity $C=N+2Z+\sum_\tau(H(\tau)-1)(H(\tau)-2)$. In particular $C=N+o(N)$ suffices for $Z=o(N)$. The three-prime adjacent transform uses the chronological indices $j,j+1,j+2$ in its input.

## Signed Haar energy at the PCC scale

Let $D_T=T\log T/(2\pi)$ and let $f$ be real, smooth, even and compactly supported. The Fourier transform uses $e^{-2\pi i v x}$. Three-prime words on $2,3,5$ give a positive mesh $h_T<T^{-3}$ for all sufficiently large $T$. For each $k\in\mathbb Z$, put
$$
b_{T,k}=\int_{\operatorname{round}(v\log T/h_T)=k}\widehat f(v)\,dv,\qquad
A_{T,k}=Z_T(kh_T).
$$
Write $b^+=\max(b,0)$ and $b^-=\max(-b,0)$. The two circle functions with Fourier coefficients $\sqrt{b_{T,k}^{\pm}}A_{T,k}$ are defined in Haar $L^2$ at fixed $T$. Parseval converts the rounded physical test **exactly** to
$$
\frac{\|F_{T,+}\|_2^2-\|F_{T,-}\|_2^2-f(0)C_T}{2D_T}.
$$
Every integer cell is included; $\widehat f$ need not have compact frequency support. Multiplying each coefficient by a phase of modulus one preserves the two norms. The frequency rounding has vanishing error at this normalization. Thus the limits of these signed Haar energies characterize ordinary positive-gap PCC. Positive rational inner and outer radii give a countable family of smooth plateau tests whose endpoint inequalities also determine it, using continuity of the sine gap mass. The zero-index Fourier cell has width $h_T/\log T$. For $|\widehat f|\le C$ its normalized contribution is eventually at most $C/(\pi T^2)$ in absolute value. The separate collision subtraction $f(0)C_T/(2D_T)$ remains in the exact statistic.

Lean files: [RoundedFourierCellParseval](Analysis/RoundedFourierCellParseval.lean), [MontgomerySignedHaarCriterion](Analysis/MontgomerySignedHaarCriterion.lean), [MontgomeryRationalPlateau](Analysis/MontgomeryRationalPlateau.lean), [MontgomeryRationalHaarEnvelope](Analysis/MontgomeryRationalHaarEnvelope.lean), [RoundedFourierZeroCell](Analysis/RoundedFourierZeroCell.lean), [MontgomeryNonconstantHaarCriterion](Analysis/MontgomeryNonconstantHaarCriterion.lean).

## What FMZ supplies at fixed frequencies

At fixed nonzero rational frequencies, the squared FMZ main terms yield an unconditional collision-subtracted all-pair series on the $T^2$ scale under the module's weighted summability hypothesis. A fixed prime-power cosine mode even tends to positive infinity after division by $D_T$. The mixed balanced three-prime ratio words have zero arithmetic main term when nontrivial. In the active mesh, the nonzero order $k$ is the balanced rational word with prime exponents $(-ka,k(a-b),kb)$. Its prime-power main term vanishes exactly. Writing $r_{T,k}$ for the actual one-ordinate FMZ residual in its height normalization gives $Z_T(kh_T)=T r_{T,k}$ for $k\ne0$ and $Z_T(0)=N_T$. The physical signed test can consequently be expressed at its original scale using
$$
\frac{T^2\sum_{k\ne0} b_{T,k}|r_{T,k}|^2-C_T f(0)}{2D_T}.
$$
The difference from the full rounded expression is the normalized central-cell term bounded above. Controlling the displayed sum as the words and cells vary with $T$ is the specific FMZ remainder problem for PCC. The weights $b_{T,k}$ can have either sign. The fully composed theorem is `exists_two_three_five_rational_noncentralFMZ_envelopes`. If $f_{r,s}$ is one on $[-r,r]$ and zero outside $(-s,s)$, write $X_T(f_{r,s})$ for the displayed statistic and $G(q)=\int_0^q(1-\operatorname{sinc}^2(\pi u))\,du$. Ordinary positive-gap PCC holds exactly when, for every rational $0<r<s$ and every $\epsilon>0$, eventually $G(r)-\epsilon\le X_T(f_{r,s})\le G(s)+\epsilon$.

The amplitude error estimate retains the collision correction. A cofinal bound below $N_T+2$ for the weighted actual power from any cosine-inverse test equal to one at zero and nonnegative on positive gaps also yields RH with simple zeros. For Fourier weight $w$ and model amplitude $B$, define $H=\int |w||Z-B|^2$ and $E=\int |w||B|^2$. The difference of the signed spectral powers is bounded by $H+2\sqrt{EH}$. Applying this to actual compact tests requires hypotheses at the physical normalization on both the energy error and the collision term.

A circle model illustrates loss of uniformity. The probability density $1+\cos(2\pi n x)$ agrees with Haar on every fixed finite collection of Fourier coefficients for all large $n$. Its nonconstant Fourier energy stays $1/2$. Its autocorrelation integrated over the unfolded width $q$ gives $q+\sin(2\pi q)/(4\pi)$. Fixed-mode convergence alone does not authorize the moving-scale limit. No such discrepancy is asserted for zeta itself.

Lean files: [MontgomeryFixedRationalPairSeries](Analysis/MontgomeryFixedRationalPairSeries.lean), [MontgomeryThreePrimeFMZResidual](Analysis/MontgomeryThreePrimeFMZResidual.lean), [MontgomeryThreePrimeFMZCriterion](Analysis/MontgomeryThreePrimeFMZCriterion.lean), [MontgomeryAmplitudeResidual](Analysis/MontgomeryAmplitudeResidual.lean), [MontgomeryFixedModesEscape](Analysis/MontgomeryFixedModesEscape.lean).

The open statements are the signed physical Haar-energy asymptotics for PCC and the cofinal two-prime upper certificate for RH with simple zeros. Neither is assumed in the fixed-height reconstruction.

[Compact Orbit, current proofs](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/current-proofs.html) · [Compact Orbit, November 18 notation](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/november-18.html) · [Ford, Meng and Zaharescu, simultaneous fractional parts of zeta zeros](https://arxiv.org/abs/1511.06814) · [Earlier prime and Mellin sine-kernel transfer](THEOREM_CATALOG_PRIME_BULK_KERNEL_TRANSFER.md).

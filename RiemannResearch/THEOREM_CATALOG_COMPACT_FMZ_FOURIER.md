# FMZ, Parseval and compact Fourier tests of physical zeta pairs

Compact Orbit identifies “ZMF” with Ford–Meng–Zaharescu (FMZ). Its diagonal Parseval result groups equal prime characters before taking the Haar norm. This development also applies Parseval to the actual rounded Fourier amplitudes of the zero occurrences. Two different limits enter the calculation.

## Completeness of the ordinate probes in the legal Pareto space

In the real Pareto space with mass $P(n)=1/[n(n+1)]$ at $n\ge1$, write
$c_\gamma(n)=\cos(\gamma\log n)$ and $e_m=\mathbf1_{\{m\}}$. Each of the
following averages counts the analytic copies of every positive zeta zero.
The module [ParetoOrdinateCosineCompleteness](RH/ParetoOrdinateCosineCompleteness.lean)
proves the strong limit
$$
R_{T,m}=\frac1{N(T)}\sum_{0<\gamma\le T}c_\gamma(m)c_\gamma
\longrightarrow d_m e_m,
\qquad d_1=1,\quad d_m=\tfrac12\quad(m>1).
$$
The Lean index for physical site $m$ is $m-1$. Fixed-frequency cancellation
gives the limit at each site by the cosine product formula. The summable
Pareto weights promote these limits to convergence in Hilbert norm.
Selberg density at slope two suffices for the fixed-strip hypothesis of
`recovery_tendsto_of_fixedStrip`. The actual normalized displacement moment
also supplies that hypothesis unconditionally.

- `actualRow_span_dense` gives completeness of the cosine probes in the
  ambient Pareto space. `projected_actualRow_span` gives completeness of
  their orthogonal projections in the closed legal space $V$.
- `first_recovery_landau_error_of_selberg_two` bounds the physical coordinate
  error between $R_{T,1}(n)$ and $\Re L_T(\log n)/N(T)$ by
  $2CT(\log n)^2/[3N(T)\log T]$ for $1\le n\le T$, assuming the project's
  slope-two density bound at height $T$ with constant $C$.
- `rh_iff_first_recovery_defect` gives
  $\mathrm{RH}\iff\|(I-P_V)R_{T,1}\|_P\to0$. Its limit as a vector always
  exists and equals $(I-P_V)e_1$. Proving this vector vanishes remains open.
  At a critical-line zero the finite arithmetic Mellin kernel has a zero row
  by `MellinFrequency.kernel_row_zero_of_zeta_zero`.

## GUE and Selberg density in the squared legal projection error

Write $b_T=R_{T,1}$, $r_\gamma=(I-P_V)c_\gamma$ and $E_T=\|(I-P_V)b_T\|_P^2$.
[ParetoOrdinatePairError](RH/ParetoOrdinatePairError.lean) proves that $E_T$
is the signed sum of $\langle r_\gamma,r_{\gamma'}\rangle_P$ over all ordered
zero occurrences, divided by $N(T)^2$. Under the actual-ordinate sine second
moment, the number of pairs with $|(\gamma-\gamma')\log T/(2\pi)|\le q$,
divided by $N(T)$, tends to $1+2\int_0^q(1-\operatorname{sinc}(\pi u)^2)\,du$
for every fixed $q>0$, with $\operatorname{sinc}(x)=\sin(x)/x$.
At the squared-count normalization the fixed-window contribution to $E_T$
tends to zero unconditionally by the local zero-count bound below. The sum over the complementary
pairs tends to $(1-K_V(1,1))/2$, where $K_V$ is the discrete legal projection
on normalized Pareto atoms.

[ParetoOrdinateLandauRecovery](RH/ParetoOrdinateLandauRecovery.lean) compares
$b_T$ with the real centered Landau trace divided by $N(T)$ on $1\le n\le K$,
continued by zero for $n>K$. Under Selberg density at exponent two with
constant $C$ at height $T$, the squared norm of the difference is at most
$24[2CT/(3N(T)\log T)]^2+1/(K+1)$ for each integer $K\le T$ and $N(T)>0$,
$T>1$. Under uniform slope two, taking $K=\lfloor T\rfloor$ gives the same
limiting squared projection error. This also equals the
limit of the sum outside each fixed unfolded window. RH is equivalent to
$K_V(1,1)=1$. This diagonal value remains to be established.

[ParetoOrdinateInghamRecovery](RH/ParetoOrdinateInghamRecovery.lean) gives a
second proof of the strong Landau limit on the same integer head. For the
Ingham rate $I(d)=4d/(3-2d)$ the least $b$ satisfying $2d\le I(d)+b$ on
$0\le d\le1/2$ is $5-2\sqrt6$. Taking $b=1/8$ bounds the count at
$\sigma=3/4$ strongly enough that $T^{1/4}N(3/4,T)\le N(T)$ eventually.
Consequently the normalized Landau traces on $n\le T$ have absolute value at
most $2n^{1/4}$, with square summable against the Pareto weights. Fixed
integer-log Landau limits then give strong convergence to $e_1$. The
limiting squared error formula follows unconditionally from these project
theorems. The weak-star result identifies it with the distant zero-pair sum
unconditionally. Selberg density at slope two supplies the finite-height
comparison displayed above.

## Weak-star limits in the unfolded gap variable

[ParetoOrdinateGapWeakStar](RH/ParetoOrdinateGapWeakStar.lean) represents the
original ordered pairs as signed measures on the one-point compactification
of the gap line. For weights of absolute value at most one, division by
$N(T)^2$ places all the measures in the weak-star compact dual unit ball.
At each fixed unfolded width the unconditional Cauchy row bound gives
$O(N(T)\log(T+3))$ pairs. Consequently, if the total signed mass tends to
$d$, the whole weak-star limit is $d\delta_\infty$. For the legal residual
pairs at any cofinal finite rank, $d=(1-K_V(1,1))/2$. The separated
quarter intervals contribute $(1-K_V(1,1))/32$ at infinity. A zero $s$ with
$\Re s>1/2$ forces $d\ge(2\Re s-1)|(1-2^{-s})/s|^2>0$, so the signed sum
outside each fixed window has the same positive lower bound. RH is equivalent
to a nonpositive liminf for this signed sum at any one fixed width. Absolute
tightness of the residual pair tails would also force RH. This tail estimate is open.

## Condition (iv) and the frequency of zero first spacings

For the original zero occurrences, let $A_T$ count tied adjacent pairs
strictly inside the cutoff and let $D_T$ be the number of occupied heights.
Then $A_T+D_T=N(T)$. Each block of $m\ge2$ occurrences contributes $m-1$
ties, so at most $2A_T$ occurrences lie in nonsingleton blocks. Under the
first marginal of Arias de Reyna–Rodgers condition (iv), Portmanteau at
$\{0\}$ gives $A_T/N(T)\to0$. Hence singleton ordinates and simple critical
zeros both have limiting occurrence proportion one. For a Borel set $S_T$
containing zero, even one exceptional zero forces its empirical first-gap
mass to be at least $1/N(T)$ at every later nonempty cutoff. A strict upper
bound below $1/N(T)$ on cofinal cutoffs would prove RH and simplicity. This
unnormalized estimate is open. Vanishing of $A_T$ at cofinal cutoffs is
equivalent to RH together with analytic simplicity at all nontrivial zeros.
The sine Palm expected count in $(0,r]$ is
at most $\pi^2r^3/9$. A one-sided upper comparison of the actual first-gap
mass in $[0,r_T]$ with this pair integral, accurate to $o(1/N(T))$ at cofinal
cutoffs, suffices when $N(T)r_T^3\to a$ and $\pi^2 a/9<1$.
[Lean proof](Analysis/ActualFirstGapMarginal.lean).
[Theorem 2(iv) and Section 5.2](https://arxiv.org/abs/2311.13441).

## Absolute Gaussian recovery and the two-prime Fejér certificate

Write $N=N(T)>0$, $C=\sum_\gamma m(\gamma)^2$, $E=C-N$, and $L=\log T/(2\pi)$.
Every original positive ordinate occurrence keeps its multiplicity. With $a>0$,
$U=\sum_{\gamma_i\ne\gamma_j}\exp(-aL^2(\gamma_i-\gamma_j)^2)$ sums ordered pairs.
The reconstructed power $R(a,T,b)$ satisfies
$|E+U-N(R-1)|\le3N\exp(-b)$ for every $b\ge0$. At $b=\log(12N)$ put
$S=N(R-1)$. A strict upper bound $S<1$ forces $E<5/4$, hence $E=0$ by parity.
Conversely $E=0$ gives such an upper bound at a sufficiently large positive integer
precision. Existence at arbitrarily large cutoffs is equivalent to RH and analytic
simplicity of every nontrivial zero. The cofinal upper bound is **open**.
[Absolute certificate and global equivalence](Analysis/GaussianAbsoluteCollision.lean).

If $\delta>0$ bounds the unfolded separation of every pair of different ordinates
from below, $U\le N^2 e^{-a\delta^2}$. Thus $a\ge\log(4N^2)/\delta^2$ gives
$U\le1/4$, $|S-E|\le1/2$, and the exact integer decoder
$E=2\lfloor(S+1)/2\rfloor$. If there are no positive gaps, $U=0$.
For an attained positive gap $d$, its two orientations force
$a d^2>\log(8/5)$ whenever the certificate passes.
The actual width-two packing bound also gives $4a>\log(2W/15)$ at every sufficiently
large passing cutoff, with $W=T\log T/(2\pi)$. These are necessary bounds.
The minimum-gap formula is sufficient and its uniform arithmetic control is open.

At physical frequency $u=h\log T$ the signed amplitude is
$\mathcal L_T(u)-\sum_{j=1}^{J}u^{2j}H_{2j,T}(u)/(2j)!$, where
$H_{2j,T}(u)=\sum_\rho e^{iu\gamma}(\beta-\tfrac12)^{2j}$ with multiplicities.
The exact integrand retains the signed cross term with the reflected Landau sum
and the square of the whole horizontal correction. The verified choice is
$J=\lceil(\log(N+1)+|h|\log T+1+b)/(2\log 2)\rceil$.
One order at $B\log T$ suffices on $|h|\le B$. The full integral uses all real
frequencies. Its Gaussian weight has standard deviation $\sqrt a/(\sqrt2\pi)$
in $h$. In the proved tangent band $|u|\le(4/3)\log T$, the Fourier weight is at
most $(8/3)\sqrt{\pi/a}$. This tends to zero along passing cutoffs.
The uniform rational prime main term has the additional numerator and frequency
restrictions in [RationalLandauMovingBand](Analysis/RationalLandauMovingBand.lean).

The full integral can also be certified on a finite interval. At
$B^2=(2a/\pi^2)\log(4\sqrt2\,(N+1)^2)$, discarded absolute power is between
zero and $1/4$. Integrating the signed squared amplitude over $[-B,B]$ and
subtracting $N$ gives the band excess $S_B$. At a nonempty cutoff $T>1$,
existence of a positive integer precision with $S_B<1$ is equivalent to $C=N$.
Under the same separation precision, $|S_B-E|\le 1/2$ and
$E=2\lfloor(S_B+1)/2\rfloor$. The discarded power and the unequal-height mass enter
with opposite signs. Every Taylor order used in the integral is bounded by the order at $B\log T$.
The remaining arithmetic estimate is the strict bound $S_B<1$ along cofinal cutoffs.
[Finite Fourier band and cofinal equivalence](Analysis/GaussianCollisionFiniteBand.lean).

The two-prime Fejér test uses a finite rectangle of rational words in $2$ and $3$.
At each nonempty height above one, existence of a Gaussian test $S<1$ is equivalent
to existence of a Fejér test $F_M<N+2$. Its zero word forces
$N^2<(N+2)(M+1)^2$. Signed Landau reconstruction gives $1/4$ absolute error
for the entire Fejér average as well, uniformly in $M$. Existence of a signed
reconstructed Fejér value below $N+7/4$ is likewise equivalent to $C=N$. Increasing Taylor order
reduces reconstruction error. A cofinal upper estimate for either actual power
requires additional arithmetic control.
[Frequency and precision estimates](Analysis/GaussianCollisionBandwidth.lean).
[Two-prime Fejér certificate](Analysis/TwoPrimeCompactCollision.lean).

## Fluctuations after subtracting the actual occurrence mean

Let $q=(I-P_V)e_1$ for the physical first-site indicator and let
$Y_\gamma=\langle c_\gamma,q\rangle_P$. Center $Y_\gamma$ by its mean over
all original zero occurrences at each cutoff. For every integer $k\ge2$ its
covariance with $\cos(\gamma\log k)$ tends to
$\frac12\langle e_k,q\rangle_P$. Finite Cauchy–Schwarz bounds the square of
every such covariance by the empirical variance. If that variance tends to
zero along any unbounded cutoff sequence, all coordinates of $q$ after
the first vanish. The legal conductor-two residue has first value $1/2$,
so its orthogonality to $q$ eliminates the first coordinate as well.
Thus vanishing of this unscaled centered variance is equivalent to RH.
If RH fails, a fixed cosine covariance bounds this variance away from zero
at all sufficiently large cutoffs, and the standardized observations have
uniformly bounded support. Vanishing of the actual variance remains open. [Lean proof](RH/ParetoOrdinateCenteredFluctuations.lean).

For the limiting law itself, put $a_m=P(m)q(m)$ and choose independent
uniform phases $U_p$ on the unit circle for the primes. Set
$Z_m=\prod_{p\mid m}U_p^{v_p(m)}$. At a uniformly sampled original
occurrence, $Y_\gamma-\overline Y_T$ converges in distribution to
$\sum_{m\ge2} a_m\operatorname{Re} Z_m$. Indeed, every nontrivial
character of a finite vector $(\exp(i\gamma\log p))_p$ has frequency
$\log r\ne0$ for a positive rational $r\ne1$. Fixed-frequency ordinate
equidistribution and Weyl's criterion give joint Haar measure on each
finite prime torus. Cauchy–Schwarz gives $\sum_m |a_m|\le\|q\|_P$, so the
tails of the cosine series are uniformly small, and the first coefficient
is removed by centering in the limit. Haar character orthogonality then gives
$\lim_T\operatorname{Var}_T(Y)=\tfrac12\sum_{m\ge2}a_m^2$. This derivation
uses the fixed-frequency theorem described by
[Ford and Zaharescu, Section 1](https://arxiv.org/abs/math/0405459).

## Dyadic dilation and the physical first-site marginal

[MellinDilationFirstSite](RH/MellinDilationFirstSite.lean) proves that normalized
dyadic dilation multiplies each critical-line Mellin feature by the phase
$2^{-it}$. The correlation determinants agree at every finite rank on the
same frequency tuple, including repeated frequencies. Every dyadically
dilated legal vector vanishes at site $1$. For the original legal space,
the one-conductor marginal is $1/(2\log 2)$ and the exact two-conductor
marginal is approximately $0.7245114070$. Both give lower bounds for
$K_V(1,1)$. Determinant data alone cannot recover this physical evaluation.

## A separated pair of height intervals suffices for the first-site criterion

[ParetoOrdinateHeightBands](RH/ParetoOrdinateHeightBands.lean) uses the original
multiplicity labels in two intervals $(aT,bT]$ and $(cT,dT]$. Dividing their
signed residual Gram sum by $N(T)^2$ gives the unconditional limit
$(b-a)(d-c)(1-K_V(1,1))/2$ for fixed positive endpoints in $(0,1]$.
The intervals $(T/4,T/2]$ and $(3T/4,T]$ give $(1-K_V(1,1))/32$.
RH is equivalent to this statistic falling below each positive tolerance at
arbitrarily large heights. The centered Landau estimators give the same
limit by Ingham recovery. Selberg density at exponent two at the band endpoints
bounds the finite-height change of estimator.

[ParetoOrdinateFiniteBands](RH/ParetoOrdinateFiniteBands.lean) proves the same
limit for finite legal ranks increasing at any rate. The two band load vectors
paired through the inverse residue Gram matrix tend to $K_V(1,1)/32$.
Reaching $1/32$ is equivalent to RH. In particular, `rh_iff_landau_finite_band`
expresses RH as a nonpositive liminf with the legal rank and each Landau head
cut off at the integer part of its height. A single right-half-strip zero
forces a persistent positive lower bound here. The liminf estimate is open.

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

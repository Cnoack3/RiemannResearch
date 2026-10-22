# Complete-Q energy audit of squarefree exact heads

Christian Noack's RiemannResearch program — 18 October 2026.

The published explicit constant loses several orders of magnitude before the choice of approximant becomes the principal issue. Refitting coefficients gives additional finite savings. Classical unconditional Möbius cancellation also gives a quantitative logarithmic improvement beyond the existing qualitative o(N) result, but does not supply bounded or subpolynomial energy.

The halted five-iteration sparse power-cost program remains closed. No finite calculation here establishes RH.

## 1. Construction and current sources

The starting benchmark is commit [498a4517c7c85819156ce52aa36ab2a6125023eb](https://github.com/Cnoack3/RiemannResearch/commit/498a4517c7c85819156ce52aa36ab2a6125023eb). The inspected server workspace started from 0f23dd1b4f9e5cc3e70b52a4ebc6895cab67634f.

Existing modules inspected: QMobiusExactHead, QSquarefreeLinearBenchmark, QSquarefreeSublinearHeads, QSquarefreeConstrainedMinimum, QResidueHeadSpace, QSquarefreeAffineHead, QResidueMoments, QTailGram, and QExactHeadSubpolynomial. Existing coefficient-forcing and constrained-completion results are reused.

Write
\[
Q(n)=\frac1{\zeta(2)n^2},\quad g_d(n)=\frac{n\bmod d}{d},\quad
S_N=\sum_{d\le N}\frac{\mu(d)}d,\quad M(t)=\sum_{d\le t}\mu(d).
\]
For each requested H, choose the least prime p>H, put N=p−1, and test
\[
F_N=-\sum_{d\le N}\mu(d)g_d+pS_Ng_p.
\]
This is the actual canonical construction, exact through N and squarefree legal. The least prime makes the calculation reproducible; the original theorem only requires a Bertrand prime.

Also compare the requested-head baseline
\[
B_{H,p}=-\sum_{d\le H}\mu(d)g_d+pS_Hg_p.
\]
Both errors are complete infinite Q norms.

## 2. Certified results

Each interval encloses an exact complete error. The least-squares minimum is over every squarefree conductor 2≤d≤D, with F(n)=1 for 1≤n≤H. It is not the minimum over the infinite squarefree span. Endpoints are rounded outward; the published bound is rounded upward.

| H | p | N | Published bound, upper | Canonical complete error | D | Constrained minimum |
|---:|---:|---:|---:|---|---:|---|
| 1 | 2 | 1 | 21.453668 | [0.2499999997, 0.2500000002] | 4 | [0.0693072546, 0.0693072551] |
| 2 | 3 | 2 | 40.907335 | [0.0706644259, 0.0706644265] | 6 | [0.0274376949, 0.0274376955] |
| 3 | 5 | 4 | 60.361002 | [0.0277014168, 0.0277014173] | 10 | [0.0176045362, 0.0176045369] |
| 4 | 5 | 4 | 79.814670 | [0.0277014168, 0.0277014173] | 10 | [0.0176045362, 0.0176045369] |
| 6 | 7 | 6 | 118.722004 | [0.0230894698, 0.0230894707] | 14 | [0.0160758304, 0.0160758314] |
| 10 | 11 | 10 | 196.536673 | [0.0216759065, 0.0216759076] | 22 | [0.0151768649, 0.0151768661] |
| 16 | 17 | 16 | 313.258677 | [0.0234910418, 0.0234910432] | 34 | [0.0135656605, 0.0135656621] |
| 24 | 29 | 28 | 468.888015 | [0.0230422159, 0.0230422176] | 58 | [0.0124428196, 0.0124428217] |
| 32 | 37 | 36 | 624.517353 | [0.0227973821, 0.0227973842] | 74 | [0.0135582470, 0.0135582494] |
| 48 | 53 | 52 | 935.776029 | [0.0222703687, 0.0222703710] | 106 | [0.0129663236, 0.0129663263] |
| 64 | 67 | 66 | 1247.034705 | [0.0209200932, 0.0209200959] | 134 | [0.0129468806, 0.0129468836] |

For H=1 the canonical error is exactly 1/4, now separately formalized. In the D=4 dictionary the rational feasible trial
\[
c_2=\frac{5398768687549}{5000000000000},\qquad
c_3=\frac{13803693937353}{10000000000000}
\]
satisfies c₂/2+c₃/3=1 exactly. Its error exceeds the true finite minimum by less than 1.7×10⁻¹⁹.

Same-dictionary and shorter-head comparisons, shown as rounded summaries:

| H | Canonical | Minimum using conductors through p | Baseline using head H |
|---:|---:|---:|---:|
| 24 | 0.023042217 | 0.022557492 | 0.025415363 |
| 32 | 0.022797383 | 0.020973768 | 0.036811327 |
| 48 | 0.022270370 | 0.022238826 | 0.023277727 |
| 64 | 0.020920095 | 0.020604372 | 0.020994751 |

The JSON retains the certified endpoints. Simply shortening the canonical exact head is not uniformly beneficial.

At H=32 the published bound exceeds the canonical error by a factor above 27,000; enlargement and refitting to D=74 reduces the actual error by about 40.5%. At H=64 these figures are above 59,000 and about 38.1%. Most of the explicit slack is in the inequalities, while the canonical coefficient choice still incurs a measurable finite cost.

## 3. Complete-tail certification

For positive a,L let
\[
W_L(a)=\sum_{j=0}^{\infty}(a+jL)^{-2}.
\]
The existing complete-Q moment identity gives
\[
b_d=\frac1{\zeta(2)}\sum_{a=1}^d
 \frac{a\bmod d}{d}W_d(a),
\]
\[
G_{de}=\frac1{\zeta(2)}\sum_{a=1}^{\operatorname{lcm}(d,e)}
 \frac{a\bmod d}{d}\frac{a\bmod e}{e}
 W_{\operatorname{lcm}(d,e)}(a).
\]
This is also a finite Hurwitz-zeta expression; see [DLMF 25.11.1](https://dlmf.nist.gov/25.11.E1). No floating special-function values are trusted.

Define
\[
U(x)=x^{-1}+\tfrac12x^{-2}+\tfrac16x^{-3},\qquad
V(x)=U(x)-\tfrac1{30}x^{-5}.
\]
The exact identities
\[
U(x)-U(x+1)-x^{-2}=\frac1{6x^3(x+1)^3}>0,
\]
\[
V(x)-V(x+1)-x^{-2}
=-\frac{5x^2+5x+1}{30x^5(x+1)^5}<0
\]
telescope to
\[
V(x)\le\sum_{j\ge0}(x+j)^{-2}\le U(x).
\]
The Lean version assumes x≥1, covering every tail used by the calculator.

Put x₀=a+KL. Then
\[
\begin{aligned}
W_L(a)&\ge\sum_{j<K}(a+jL)^{-2}
+\frac1{Lx_0}+\frac1{2x_0^2}+\frac L{6x_0^3}
-\frac{L^3}{30x_0^5},\\
W_L(a)&\le\sum_{j<K}(a+jL)^{-2}
+\frac1{Lx_0}+\frac1{2x_0^2}+\frac L{6x_0^3}.
\end{aligned}
\]
The analytic width is L³/(30x₀⁵). We use K=32 for moments, K=4096 for ζ(2), and integer fixed-point scale 10³⁵. Every division is rounded outward by integer floor or ceiling. Analytic remainders and rounding errors are both retained. Every positive integer contributes to these certified full-tail quantities.

## 4. Certifying constrained minima

The exact-head constraints in the finite squarefree dictionary are
\[
c_d=-\mu(d)\quad(2\le d\le H),\qquad
\sum_{H<d\le D}c_d/d=S_H.
\]
Discrete differences and Möbius inversion force the low coefficients; they are not optimization variables.

With B=B_{H,p}, use the head-zero directions
\[
z_d=g_d-\frac p d g_p\quad(H<d\le D,\ d\ne p).
\]
Let
\[
A_{de}=\langle z_d,z_e\rangle_Q,\quad
u_d=\langle1-B,z_d\rangle_Q,\quad E_B=\|1-B\|_Q^2.
\]
All inner products are complete, and
\[
E(t)=E_B-2u^\top t+t^\top At,\qquad
E_{\min}=E_B-u^\top A^{-1}u,
\]
\[
E(t)-E_{\min}=(t-A^{-1}u)^\top A(t-A^{-1}u).
\]
Positive definiteness follows from existing residue independence. This is the existing constrained Q-Gram completion specialized to the actual dictionary; it assumes no independence of residues under Q.

Floating linear algebra only proposes coefficients. They are rounded to rationals, the anchor coefficient is repaired exactly, and every head value is checked with exact rational arithmetic.

For a lower bound, use the unnormalized tangent Gram ζ(2)A and a rational inverse proposal R. Interval arithmetic must verify
\[
\delta=\|I-R(\zeta(2)A)\|_\infty<1.
\]
A Neumann-series estimate, followed by symmetry, gives
\[
\lambda_{\min}(\zeta(2)A)\ge(1-\delta)/\|R\|_\infty.
\]
The squared norm of the trial's certified gradient divided by this bound controls its excess energy. Thus both endpoints enclose the true finite minimum.

At H=64,D=134, δ<8.84×10⁻⁷ and the unnormalized tangent eigenvalue lower bound exceeds 5.008×10⁻⁵. Trial excess energy is below 8.05×10⁻¹⁶. Most interval width comes from the progression enclosure. The JSON contains rational coefficients and exact rational certificate bounds.

These numerical certificates are exact-arithmetic calculations, not individually kernel-verified numerical theorems.

## 5. Locating inequality losses

The original argument bounds ‖F‖² in Pareto space, transfers to Q with a factor at most two, bounds the error by 2+2‖F‖², then replaces N by 2H. In particular, it discards the favorable signed term −2⟨1,F⟩.

Even using the actual complete Q norm in 2+2‖F‖² leaves a bound close to four. A separate improvement preserves the zero head. Define
\[
L_c=\sum_{c_d<0}c_d(1-1/d),\quad
U_c=\sum_{c_d>0}c_d(1-1/d),\quad
B_c=\max(|1-L_c|,|1-U_c|).
\]
Since L_c≤F(n)≤U_c, an exact head through N gives
\[
E(F)\le\frac{B_c^2}{\zeta(2)}\sum_{n>N}n^{-2}.
\]

| H | 2+2‖F‖² using the actual norm | Signed-coefficient tail bound, upper | Actual error |
|---:|---|---:|---|
| 1 | [3.4999999994, 3.5000000009] | 0.3920728982 | [0.2499999997, 0.2500000002] |
| 10 | [4.0453253859, 4.0453253891] | 0.4322351165 | [0.0216759065, 0.0216759076] |
| 32 | [4.0417730099, 4.0417730158] | 1.7928443243 | [0.0227973821, 0.0227973842] |
| 64 | [4.0448977370, 4.0448977445] | 3.3995517498 | [0.0209200932, 0.0209200959] |

These are finite-constant improvements. The coefficient envelope still grows; it does not establish a better asymptotic exponent.

## 6. Physical error redistribution

For H=64,p=67, this is a complete partition. The first range includes the canonical zero residual at 65 and 66. The optimized column is the rational feasible D=134 trial, with total excess above the true minimum below 8.05×10⁻¹⁶.

| Physical n | Canonical contribution | Least-squares trial contribution |
|---|---|---|
| 65–133 | [0.0131504457, 0.0131504458] | [0.0043515420, 0.0043515421] |
| 134–267 | [0.0033652527, 0.0033652528] | [0.0044406439, 0.0044406440] |
| 268–1071 | [0.0032976009, 0.0032976010] | [0.0032156875, 0.0032156876] |
| 1072–infinity | [0.0011067938, 0.0011067965] | [0.0009390070, 0.0009390100] |

The first range saves about 0.008799, but the next range costs about 0.001075 more. A first-block comparison alone overstates the total gain. The positive remaining infinite tail is explicitly retained.

## 7. Signed arithmetic structure and an unconditional rate improvement

For n>N set p=N+1 and q=⌊n/p⌋. The complete signed identity is
\[
R_N(n):=1-F_N(n)
=\sum_{k=1}^{q}\left[M(\lfloor n/k\rfloor)-M(N)\right]+pS_Nq.
\]
It is formalized in the new RH module. On p≤n<2p this reduces to
\[
R_N(n)=M(n)-M(N)+pS_N.
\]
This identifies the actual fluctuation being charged in the first block.

Suppose at a fixed cutoff N that
\[
|M(t)|\le\varepsilon t\quad(t\ge N),\qquad |S_N|\le\varepsilon.
\]
These are cancellation inputs, not an RH premise. Since every floor argument in the signed sum is at least p, the identity implies
\[
|R_N(n)|\le\varepsilon\left(nH_q+qN+pq\right)
\le\varepsilon n(H_q+2),
\qquad H_q=\sum_{k\le q}1/k.
\]
Use floor(n/k)≤n/k and qN≤pq≤n. This harmonic inequality is an ordinary mathematical derivation, not a new Lean declaration.

Combining it with |F_N(n)|≤2N yields, for every integer K≥2,
\[
E_N\le\frac1{\zeta(2)}
\left[\varepsilon^2 Kp(3+\log K)^2+\frac{(2N+1)^2}{Kp}\right].
\]
Proof: the head has zero residual; on N<n≤Kp each R_N(n)²/n² is at most ε²(3+log K)²; beyond Kp the complete inverse-square mass is at most 1/(Kp). All physical sites remain accounted for.

For 0<ε≤1/2 choose K comparable to
\[
[\varepsilon(3+\log(1/\varepsilon))]^{-1},
\]
enlarging constants to ensure K≥2. Therefore
\[
E_N\ll N\varepsilon(3+\log(1/\varepsilon)).
\]

Classically and unconditionally,
\[
M(x)\ll x e^{-c\sqrt{\log x}}
\]
for some c>0; see [DLMF 27.11.12](https://dlmf.nist.gov/27.11.E12). DLMF 27.11.14 records S_N→0. Partial summation retains the full convergent integral:
\[
S_N=\frac{M(N)}N-\int_N^\infty\frac{M(t)}{t^2}\,dt,
\qquad
|S_N|\ll(1+\sqrt{\log N})e^{-c\sqrt{\log N}}.
\]
A cancellation envelope may thus be chosen with ε_N≪exp(−c₁√log N), for some c₁>0. Substitution proves
\[
\boxed{E_N\ll N e^{-c_2\sqrt{\log N}}}
\]
for some c₂>0 and all sufficiently large N. In particular,
\[
\boxed{E_N=O_A\!\left(N/(\log N)^A\right)
\quad\text{for every fixed }A>0.}
\]
Prime-anchor stages satisfy H≤N<2H, so this is also an existence bound in H. Finite constrained dictionaries with D≥p inherit it by minimality.

This is a quantitative strengthening beyond qualitative o(N), derived from known unconditional cancellation. No mathematical novelty claim is made. It remains far short of a subpolynomial estimate: the upper envelope has logarithmic exponent tending to one.

The new Lean module separately checks the coarser finite budget derived from existing window bounds:
\[
E_N\le\frac{8+4N(N^{-1}+2\varepsilon K(K+2))^2+16N/K}{\zeta(2)}.
\]
Its exact type retains the two cancellation bounds as hypotheses. The quantitative provider and final asymptotic corollaries have not been connected in Lean here. The harmonic refinement and asymptotic deduction above are mathematical proofs, not claims of kernel-verified unconditional rate theorems.

## 8. The remaining subpolynomial obligation

The measured errors are nonmonotone: the D=2p constrained minimum rises from H=24 to H=32. These finite values imply no uniform or asymptotic bound.

The exact finite identity
\[
E_{\min}=E_B-u^\top A^{-1}u
\]
locates the target-specific issue. Positive definiteness alone gives 0≤E_min≤E_B. It does not control the size left after subtraction. A stronger inequality must bound the signed alignment of u with the small-eigenvalue directions of A, or the complete weighted mean square of the signed Möbius floor-sum residual.

The existing zero-witness theorem makes the limitation precise: if ζ(s)=0, β=Re(s)>1/2 and s≠1, every squarefree legal trial exact for 1≤k<n has
\[
\|1-F\|_Q^2\ge
\frac{2\beta-1}{\zeta(2)|s|^2}n^{2\beta-1}.
\]
Consequently a cofinal subpolynomial complete-error bound would imply RH. Generic matrix positivity, logarithmic savings, and finite measurements do not discharge that obligation.

The useful next analytic target is a complete mean-square bound for the displayed signed residual, retaining covariance with pS_Nq, or an explicit lower bound on the actual Gram gain uᵀA⁻¹u relative to E_B. The required subpolynomial remainder remains Open and must not be inserted as an assumed bound.

## 9. Reproduction and verification

The separately saved calculation bundle q_exact_head_energy_audit.zip contains a q_exact_head_energy_audit directory with:

- certify_q_errors.py: complete moment enclosures, exact head feasibility, and finite minimum certificates.
- analyze_certificates.py: loss comparisons and complete physical partitions.
- certificates.json: H=1,2,3,4,6,10,16,24,32.
- certificates_moderate.json: H=48,64.
- analysis_summary.json: outward display intervals and physical partitions.

From that directory:
~~~bash
python3 certify_q_errors.py --out certificates.json
python3 certify_q_errors.py --heads 48,64 --out certificates_moderate.json
python3 analyze_certificates.py
~~~

Python 3 and NumPy generate proposals. Acceptance uses integers and Fraction. A poor numerical proposal can fail certification but cannot make a failed exact inequality pass.

New reusable Lean modules:

- Analysis/InverseSquareTailCertificates.lean: rational step identities, finite telescoping bounds, summability, complete-tail bounds and scaling.
- RH/QExactHeadEnergyCertificates.lean: exactHead_one, two_residue_error_sq, exactHead_one_error_sq, exactHead_residual_floor_tail, exactHead_error_window_budget.

The small-stage identity and analytic tail bounds passed actual serialized server snippets. Numerical interval certificates are not individually kernel-verified. The rate deduction is an ordinary mathematical consequence of the cited classical bounds. Final project validation and publication use the push-enabled server checkpoint; its terminal job, scope and published commit are reported separately.

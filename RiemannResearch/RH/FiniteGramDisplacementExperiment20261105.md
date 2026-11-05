# Finite projection displacements and the harmonic prefix

The table gives both one-sided harmonic sums for each of the four windows and three squarefree dictionaries in the November 5 agenda. Every displayed mass is within $10^{-10}$ of the exact value and all sign counts are certified. At $X=6561$, the smaller harmonic mass grows from $0.0184025799$ to $0.0496803233$ as the largest allowed conductor grows from 6 to 15. The computations certify individual finite dictionaries. Uniform control as both the window and the dictionary grow remains open.

## Both signs at each window

Here $M$ is the **largest included conductor**, so the legal dictionary is all squarefree $2\le m\le M$. In code that indexes the finite stage by $m\le M'+1$, use $M'=M-1$. The sums and counts refer to the finite resolvent iterate $u_{M,j}$, with $j$ determined by $X=9^j$. The squared norm used for the physical projection is proportional to $\sum_n u(n)^2/n^2$.

| $M$ | $X$ | $j$ | $S_+$ | $S_-$ | $h$ | $N_+$ | $N_-$ | $N_0$ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 9 | 1 | 0.0155550174 | 0.0025064470 | 0.0025064470 | 6 | 3 | 0 |
| 6 | 81 | 2 | 0.0285209573 | 0.0079514150 | 0.0079514150 | 52 | 27 | 2 |
| 6 | 729 | 3 | 0.0401985570 | 0.0133253825 | 0.0133253825 | 463 | 242 | 24 |
| 6 | 6561 | 4 | 0.0510024222 | 0.0184025799 | 0.0184025799 | 4156 | 2187 | 218 |
| 10 | 9 | 1 | 0.0175518922 | 0.0044371553 | 0.0044371553 | 6 | 3 | 0 |
| 10 | 81 | 2 | 0.0345539319 | 0.0162056492 | 0.0162056492 | 43 | 38 | 0 |
| 10 | 729 | 3 | 0.0488953587 | 0.0281231607 | 0.0281231607 | 372 | 354 | 3 |
| 10 | 6561 | 4 | 0.0618228521 | 0.0393334680 | 0.0393334680 | 3344 | 3186 | 31 |
| 15 | 9 | 1 | 0.0160237545 | 0.0044020555 | 0.0044020555 | 5 | 4 | 0 |
| 15 | 81 | 2 | 0.0319714320 | 0.0186860590 | 0.0186860590 | 38 | 43 | 0 |
| 15 | 729 | 3 | 0.0467565448 | 0.0346614301 | 0.0346614301 | 350 | 379 | 0 |
| 15 | 6561 | 4 | 0.0600472610 | 0.0496803233 | 0.0496803233 | 3143 | 3418 | 0 |

For $M=15$, the less frequent sign changes between $X=9$ and $X=81$, while the negative sign has the smaller harmonic mass in all four windows. At the last window 3,418 negative sites contribute less harmonic mass than 3,143 positive sites.

## Complete Gram matrices and error bounds

Write $G,H$ for the unnormalized $Q$ and normalized $P$ Gram matrices. Their weights are $n^{-2}$ and $[n(n+1)]^{-1}$. Write $v,w$ for the corresponding pairings of the dictionary with 1. On a residue class $a\bmod L$, with $1\le a\le L$, the exact total weights are
$$
Q'_{a,L}=\frac{\psi_1(a/L)}{L^2},\qquad
P_{a,L}=\frac{\psi((a+1)/L)-\psi(a/L)}{L}.
$$
Take $L=\mathrm{lcm}(i,k)$ for a Gram entry and weight each class by $g_i(a)g_k(a)$. The derivation uses the trigamma series and the difference of two digamma series. Wolfram independently summed both series and gave these two expressions. A separate Wolfram calculation using the polygamma formulas returned $(S_+,S_-,N_+,N_-)=(0.02852095729445158,0.007951414995747359,52,27)$ for $(M,X,j)=(6,81,2)$. [NIST DLMF §5.15](https://dlmf.nist.gov/5.15) · [NIST DLMF §5.7](https://dlmf.nist.gov/5.7)

The projection coordinates satisfy $Gq=v$ and $Hp=w$. The coefficients $b$ of $\Pi_M B_0(1-f_{Q,M})$ and the finite iteration satisfy
$$
G b=(v-w)-(G-H)q,\qquad
u_0=0,\qquad u_{j+1}=\frac43 b+\left(I-\frac43G^{-1}H\right)u_j.
$$
The pointwise identity $n^{-2}/(n+1)=n^{-2}-[n(n+1)]^{-1}$ accounts for the subtraction and the use of the unnormalized $Q$ Gram matrix. The scheme has fixed point $q-p$. Each entry in the table was computed for the indicated iterate.

The accompanying standard-library Python script uses exact rational arithmetic. It sums the first 64 terms of each residue progression and encloses its entire infinite remainder by Euler–Maclaurin with ten even Bernoulli corrections. Both summands, as functions of the progression index, are completely monotone. Bounding the periodic Bernoulli kernel by $|B_{20}|$ and integrating the twentieth derivative bounds the absolute remainder by the absolute last correction. The $P$ integral includes $\log(1+1/x)$, enclosed by 28 alternating series terms and the next-term bound. Each residue interval is rounded outward to multiples of $10^{-40}$. [Euler–Maclaurin formula, NIST DLMF §2.10(i)](https://dlmf.nist.gov/2.10#i) · [Bernoulli Fourier series, NIST DLMF §24.8(i)](https://dlmf.nist.gov/24.8#i)

The code inverts the midpoint matrix exactly. If $J$ is that inverse and $e$ bounds the matrix error in the induced infinity norm, it checks $\|J\|e<1$ and uses $\|G^{-1}\|\le\|J\|/(1-\|J\|e)$. It propagates the source and transfer errors through all four iterates. The table includes every physical site in the prefix. Sites where all atoms vanish have exactly zero value. The absolute midpoint value at each other site exceeds its coordinate error bound.

| $M$ | Dimension | $Q$ projection equation residual | $P$ projection equation residual | Source equation residual | Largest coordinate error through $j=4$ |
|---:|---:|---:|---:|---:|---:|
| 6 | 4 | $10^{-35}$ | $10^{-35}$ | $10^{-34}$ | $10^{-31}$ |
| 10 | 6 | $10^{-35}$ | $10^{-35}$ | $10^{-34}$ | $10^{-30}$ |
| 15 | 10 | $10^{-35}$ | $10^{-35}$ | $10^{-33}$ | $10^{-29}$ |

Entries in this table are upper bounds. The residual norm is the coordinate infinity norm with the weights specified above. The physical tail beyond the residue sums is included. The error for approximating the infinite squarefree projection by the finite dictionary is a separate open estimate.

## A scalar sufficient condition using the two finite solves

Let $c_{M,m}=q_m-p_m$ denote the coefficient of $g_m$ in the exact finite displacement $d_M$. Compute
$$
A_M^\pm=\sum_{m\le M\text{ legal}}(1-1/m)(\pm c_{M,m})_+ .
$$
In this expression the index set consists of the squarefree conductors $m\ge2$. Each reported value is within $10^{-10}$ of its exact value.

| $M$ | $A_M^+$ | $A_M^-$ |
|---:|---:|---:|
| 6 | 0.0313520323 | 0.0265793937 |
| 10 | 0.0564374406 | 0.0553067802 |
| 15 | 0.0873044689 | 0.0893012944 |

**Paper implication.** If $\liminf_{M\to\infty}\min(A_M^+,A_M^-)<\infty$, then RH follows. Indeed $0\le g_m(n)\le1-1/m$ for every $n$. Along an unbounded subsequence of $M$, the same sign $\epsilon$ has $A_M^\epsilon\le C$ for one finite $C$. For every $n$, $\epsilon d_M(n)\le C$. The known strong convergence of both finite projections implies coordinate convergence at every fixed $n$, and hence $\epsilon d(n)\le C$ for all $n$. Thus $h(d;X)\le C\sum_{n\le X}1/n$ and the repository's unconditional cofinal harmonic theorem applies. This sufficient condition asks for one computable number at each stage and requires no convergence rate. Establishing the displayed liminf for the actual solves remains open. [Finite convergence](https://github.com/Cnoack3/RiemannResearch/blob/2bffac8e49a4a507feed0497444f9a5c80536fd7/RiemannResearch/RH/QSquarefreeFiniteDisplacement.lean) · [Harmonic theorem](https://github.com/Cnoack3/RiemannResearch/blob/2bffac8e49a4a507feed0497444f9a5c80536fd7/RiemannResearch/RH/QCofinalDisplacementMoments.lean)

## A pulse contrast that the actual displacement must satisfy

For each prime $p>3$, let $s_p=2g_{2p}-g_p-2g_{6p}+g_{3p}$. Its six consecutive $p$-blocks in one period have values $(0,1,0,0,-1,0)$. Thus $s_p$ is legal, supported on $n\ge p$, and bounded by 1 in absolute value. Since $d=\Pi B_0 r_P$ and $B_0$ is self-adjoint,
$$
\boxed{\left|\sum_{n\ge1}\frac{d(n)s_p(n)}{n^2}\right|
=\zeta(2)|\langle r_P,B_0s_p\rangle_Q|
\le \frac{\sqrt{\zeta(2)}\,\|r_P\|_Q}{(p+1)\sqrt{p-1}}.}
$$
Indeed $\sum_{n\ge p}n^{-2}\le (p-1)^{-1}$. The same estimate holds for the matched finite displacement whenever $M\ge6p$, with $r_{P,M}=1-f_{P,M}$ on the right. In fact the proof localizes $r_P$ to $n\ge p$. Its $Q$ tail norm tends to zero, and the contrast is $o(p^{-3/2})$. Since $\sum_{n\ge p}n^{-4}\le[3(p-1)^3]^{-1}$ and $\zeta(2)Q(n)/P(n)=1+1/n$, an explicit uniform bound for both the infinite and finite contrasts is $\sqrt{1+1/p}/[\sqrt3(p-1)^{3/2}]$, using $\|r_{P,M}\|_P\le1$ or $\|r_P\|_P\le1$. The little-$o$ bound also holds uniformly for finite $M\ge6p$, since the $Q$-norm convergence $r_{P,M}\to r_P$ implies uniformly vanishing tails along this family. This gives an unconditional arithmetic restriction on the *actual* signed mass. It controls an alternating contrast extending over all periods; isolated sign masses in each block still require an argument.

The normal equations also give a joint bound across scales. Write $t_p=\sum_n d(n)s_p(n)/n^2$, $a_n=|r_P(n)|/n$, and $C_p=\sum_{n\ge p}a_n/[n(n+1)]$ for every positive integer $p$. Then $|t_p|\le C_p$ for legal pulses. The nonnegative matrix $K_{pn}=p\mathbf1_{n\ge p}/[n(n+1)]$ has row sums 1 by telescoping and column sums $1/2$ by summing the integers through $n$. Hence $(pC_p)^2\le\sum_n K_{pn}a_n^2$. Summing over all $p\ge P$ gives the tail estimate
$$
\sum_{\substack{p\ge P\\p>3\ \mathrm{prime}}}p^2|t_p|^2
\le\sum_{p\ge P}p^2 C_p^2
\le\frac12\sum_{n\ge P}\frac{|r_P(n)|^2}{n^2}.
$$
Since $C_p$ is nonincreasing, $2^{3j}C_{2^j}^2\le8\sum_{2^{j-1}\le p<2^j} p^2 C_p^2$ for $j\ge1$. Consequently the sum over $j$ of $2^{3j}$ times the squared largest legal pulse contrast on $[2^j,2^{j+1})$ converges. The convention for an empty block is zero. This square-summability strengthens the individual little-$o$ estimate; cancellation inside each contrast remains possible.

To see the restriction's force, take the lacunary construction $v=\sum_i A_i s_{p_i}$, $A_i=\sqrt{p_i}/i^\beta$, $\beta>1/2$, with $A_{i+1}/A_i\ge4$ and $p_{i+1}/p_i\ge4096$. Such prime scales are available by Bertrand's postulate. Write $E_k=\sum_n s_{p_k}(n)^2/n^2\ge1/(4p_k)$ from the first positive block. Earlier pulses have amplitude at most $A_k/3$, so their absolute contrast is at most $(A_k/3)E_k$, using $|s_{p_k}|=s_{p_k}^2$. The absolute contribution of later pulses is at most
$$
\sum_{i>k}\frac{A_i}{p_i-1}\le \frac{2 A_k}{p_k}\sum_{j\ge1}64^{-j}
=\frac{2 A_k}{63p_k}.
$$
Consequently $\sum_n v(n)s_{p_k}(n)/n^2\ge A_k/(8p_k)$. This exceeds the actual displacement's $O(p_k^{-3/2})$ allowance by an unbounded factor. It identifies an explicit family of normal equations where the two-sign example fails. Deriving cofinal bounds on individual sign masses from such signed tests remains open.

## Reproduction

Run `python finite_prefix.py > finite_prefix.csv 2>bounds.txt` with standard Python 3. The finite computations and paper arguments above have distinct verification status. The computation uses exact rational enclosures checked by Python. The implications use the linked repository theorems and the proofs given here.

### The prescribed conductor schedule

The theorem `riemannHypothesis_of_sqrt_stage_harmonic_prefix` uses the exact difference of the two finite projections. The following entries use that difference directly. The two computations cover every physical site in their respective heads, with the same complete Gram enclosures as above.

| k | Largest conductor | Dimension | Physical head | Positive mass | Negative mass | Positive / negative / zero sites |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 3 | 2 | 1 | 0 | 0.007701905623 | 0 / 1 / 0 |
| 2 | 33 | 20 | 256 | 0.038740513504 | 0.025862657507 | 126 / 130 / 0 |

Each displayed mass has absolute error at most 10⁻¹². At the second head both Gram residuals are bounded by 10⁻³⁵ and each physical coordinate error is bounded by 10⁻³¹. At the first head the smaller mass is exactly zero. The prescribed-family theorem requires a bound for arbitrarily large k.

The companion archive Displacement_Gram_Experiments.zip contains the iteration and prescribed-schedule scripts, the one-prime script, all three output tables and the solve residuals. All three scripts use the same exact rational Gram routine.

## Prime entries from one Pareto projection solve

Write A(p) for the signed Q pairing of g_p with the finite Pareto residual on the squarefree dictionary through p+1. The table lists the scaled quantity ζ(2)pA(p). Each interval has absolute error at most 10⁻¹⁰ and certifies its sign. Run the companion prime_probe.py from the script directory.

| p | ζ(2)pA(p) |
|---:|---:|
| 2 | -0.0097746089 |
| 3 | -0.0042129238 |
| 5 | 0.0174744352 |
| 7 | 0.0202992125 |
| 11 | 0.0214002574 |
| 13 | 0.0183480912 |
| 17 | 0.0190820525 |
| 19 | 0.0192069350 |
| 23 | 0.0163788960 |
| 29 | 0.0168037423 |
| 31 | 0.0165409983 |

The first two entries are negative. The eventual positivity proof uses a lower bound for the finite Pareto distance, so no inference about infinitely many signs is drawn from this finite table.

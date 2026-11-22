# Testing fractional gains in prime-support quotients

Let $L=\log 2$, $x=J_2/L-1$, and let $S_n$ be the ambient image of the stage with at most $n$ distinct prime factors. Write $D_n=\|[x]_{H/S_n}\|_P^2$, $b=P_M(J_2/L)$, and $p_n=P_{S_n}b$.

## What the categorical argument determines

Compatible continuous linear maps from the stage quotients into any Hausdorff target factor uniquely through $H/M$. Every parity class maps to $[u-1]_{H/M}$. Its squared norm equals $\|\delta\|^2=\|u\|_P^2-1$, where $\delta$ is the centered snake boundary. For each fixed $0<c<1$, this boundary vanishes exactly when arbitrarily late $n$ admit some $m\ge n$ with $D_m\le cD_n$. Vanishing implies RH. The direct Lean attempt at $c=11/15$ stopped at the existence of these blocks. [Proof search](https://app.buildbuddy.io/invocation/fa7c227d-c344-4376-afb7-627b31569bf5)

## Finite estimates

* The five conductors $6,10,12,14,15$ give $D_2<(11/15)D_1$. Writing $V_0=L-L^2$, the same certificate gives $D_2/D_1<1-1/(15V_0)$. Here $L^2D_1=V_0>0$. This sharper factor applies to the first block.
* The period-5040 trial gives $\|u\|_P^2<1000/961$. Since $D_n\to\|\delta\|^2$, every sufficiently late cutoff satisfies $D_n<39/961$. The starting index is unspecified, and the bound is a fixed positive number.

## Testing blocks with one trial direction

For $n\le m$ and $y\in S_m$, the Hilbert-space computation gives

$$
|\langle y,b-p_n\rangle_P|^2 \le (D_n-D_m)\|y\|_P^2.
$$

Indeed $b-p_m\perp S_m$ and $p_m-p_n\in S_m$. Pythagoras gives $D_n-D_m=\|p_m-p_n\|_P^2$, and Cauchy–Schwarz gives the inequality. A nonzero finite combination of packets with squared correlation at least $(4/15)D_n\|y\|_P^2$ certifies a successful block at $c=11/15$. Checking a trial direction avoids solving the normal equations for the larger space. The open arithmetic estimate is the existence of such witnesses at arbitrarily late starting levels. The five-packet certificate supplies the first block.

The continuous factorization, the cofinal equivalence, and the five-packet estimate are named theorems in [PrimeSupportParityDescent.lean](PrimeSupportParityDescent.lean). The correlation bound, the logarithmic improvement in multiplicative form, and the eventual period-5040 bound were verified separately as anonymous Lean examples. [Focused verification](https://app.buildbuddy.io/invocation/0476a578-6d24-4dfd-9adc-c3e2d4108ffb)

## Sources

* Emily Riehl, *Category Theory in Context*, §3.1, gives the universal property used for the quotient cocone. [Author's edition](https://math.jhu.edu/~eriehl/context.pdf)
* Stéphane Mallat and Zhifeng Zhang, “Matching Pursuits with Time-Frequency Dictionaries,” *IEEE Transactions on Signal Processing* 41 (1993), 3397–3415, §III, treats residual correlation and captured energy. [Paper](https://www.di.ens.fr/~mallat/papiers/MallatPursuit93.pdf)
* Luis Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis,” *Rendiconti Lincei* 14 (2003), 5–11, Theorem 1, gives the integer-dilation approximation criterion. [Paper](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_1_5_0)

# A finite mixed-conductor lower bound for the Pareto projection of parity

The supplied 35,704 rational coefficients give \(C_{40000}>210015/10^6\). The complete numerical upper bound on the squared half-centered residual is less than \(0.039985\).

Let \(P(n)=1/[n(n+1)]\) for positive integers \(n\), and let \(\mathbf 1(n)=1\).
The integrated packet at \(q>1\) has the divisor formula
\[
 J_q(n)=\sum_{d\mid q}\mu(q/d)(n\bmod d).
\]
In particular \(J_2(n)=n\bmod2\). A mixed conductor has at least two distinct prime factors. Its packet has Pareto mean zero. Write \(M_Q\) for the span of the mixed packets through \(Q\), and \(C_Q=\|\Pi_{M_Q}J_2\|_P^2\).

The supplied integer pair \([q,b_q]\) represents the coefficient \(b_q/D\) with the common positive denominator in the certificate. Put \(c=\sum_q (b_q/D)J_q\) and \(e=J_2-\tfrac12\mathbf 1-c\). Since \(M_Q\perp\mathbf 1\), the projection theorem gives the complete identity
\[
 C_Q=\tfrac14-\|e\|_P^2+\|\Pi_{M_Q}J_2-c\|_P^2.
\]
Consequently any upper bound on the *complete* squared norm of \(e\) certifies a lower bound on \(C_Q\). No assertion about an optimal coefficient or the RH limit is needed.

## Integer head

Set
\[
 a_d=D\,\mathbf 1_{d=2}-\sum_{d\mid q}b_q\mu(q/d)
 \qquad(2\le d\le Q).
\]
Then \(G(n)=2D e(n)=-D+2\sum_da_d(n\bmod d)\). Extending this arithmetic formula to \(G(0)=-D\) gives the exact recurrence
\[
 G(n)-G(n-1)=2\sum_da_d-2\sum_{d\mid n}d a_d .
\]
The verifier checks all conductors, forms the jumps by a divisor sieve, and evaluates every \(n=1,\ldots,T\). In each consecutive group \(h\le n\le\min(T,h+\lfloor h/10000\rfloor)\) the verifier adds \(\sum_nG(n)^2/[4D^2 h(h+1)]\), rounded up to the next multiple of \(10^{-20}\). The first weight in each group is its largest, so this bounds every head term from above. The sums of squares and the rounding use integer arithmetic.

## Complete periodic mean square

Let \(S\) be the unweighted mean of \(e(n)^2\) over a common period. It can be computed without constructing that period. For \(Y_d(n)=2(n\bmod d)-(d-1)\) put \(A=\sum_d(d-1)a_d-D\). Then \(G(n)=A+\sum_d a_dY_d(n)\). Under uniform averaging over a common period, each \(Y_d\) has mean zero and
\[
 \mathbb E[Y_d Y_h]=(\gcd(d,h)^2-1)/3.
\]
Indeed, condition on the common residue mod \(g=\gcd(d,h)\). The residual coordinates are independent and each conditional mean equals \(2(n\bmod g)-(g-1)\), whose uniform second moment is \((g^2-1)/3\). Thus
\[
 S=\frac{3A^2+\sum_{k=2}^Q j_2(k)\left(\sum_{k\mid d}a_d\right)^2}{12D^2},
 \qquad \sum_{k\mid g}j_2(k)=g^2.
\]
This uses the Jordan totient of order two; the divisor recurrence in the verifier computes its integer values.

## Infinite tail

As a sum of functions of individual periods at most \(Q\), \(e(n)\) has a finite Fourier expansion \(\sum_{\alpha}u_\alpha\exp(2\pi i\alpha n)\) with reduced frequency denominators at most \(Q\). The constant term is included. Distinct frequencies on the circle have spacing at least \(Q^{-2}\). Parseval on any common period gives \(\sum_{\alpha}|u_\alpha|^2=S\).

Set \(L=Q^2\) and \(w_L(j)=\max(1-|j|/L,0)\). For any integer center \(t\), the weighted quadratic form \(\sum_jw_L(j)|e(t+j)|^2\) has diagonal entries \(L\). The magnitudes of its off-diagonal entries are bounded by
\[
 \frac{\sin^2(\pi L\theta)}{L\sin^2(\pi\theta)}
 \le\frac{1}{4L\|\theta\|_{\mathbb R/\mathbb Z}^2}.
\]
The identity follows by squaring the finite geometric sum and dividing by \(L\). The sine bound follows from its concavity on \([0,\pi/2]\). On each side of a fixed frequency out to distance \(1/2\), the \(j\)-th distinct frequency is at least \(j/L\) away. Hence each off-diagonal absolute row sum is at most \((L/2)\sum_{j\ge1}j^{-2}\le L\), using \(\sum_{j\ge1}j^{-2}\le1+\int_1^\infty x^{-2}\,dx=2\). The inequality \(2|u_\alpha u_\beta|\le |u_\alpha|^2+|u_\beta|^2\) gives a bound \(2LS\) for the weighted quadratic form. Choosing a center at the midpoint of any block of \(L\) consecutive integers makes every weight there at least \(1/2\), so the unweighted block sum is at most \(4LS\).

Partition \(n>T\) into successive blocks of length \(L\). The largest \(P\)-weight in block \(j\) occurs at \(T+1+jL\). For \(j\ge1\) this weight is at most the average of the \(L\) weights ending there, and the combined weights have mass \(1/(T+2)\). This yields the rational bound for the whole tail
\[
 \sum_{n>T}\frac{e(n)^2}{n(n+1)}
 \le 4 S\left(\frac{Q^2}{(T+1)(T+2)}+\frac{1}{T+2}\right).
\]

Run `python3 verify_capture.py certificate.json` with Python's standard library. All acceptance comparisons use exact integers and fractions. The displayed decimal values are for readability. Floating-point least squares was used only to select the integer witness. The numerical verification and the above elementary tail proof are external to the Lean kernel.

## Verified arithmetic

The squared residual over the first 320,000,000 coordinates is at most \(49913707821946223/1250000000000000000\). The remaining tail is at most \(2263456467521380077340050261/42666667066666667500000000000000\). Subtracting both from a quarter gives the lower bound
\[
C_{40000} \ge \frac{4480341033618830606778698354220759}{21333333533333333750000000000000000} > 0.21001598 .
\]
The saturation target is \(\log2-(\log2)^2\approx0.21269416664\). This witness accounts for more than 98.7408% of that target. The explicit certificate has a fixed cutoff.

## Reproduction files

Download both files from the owner-private Compact Orbit site into one directory and run the command above. [verify_capture.py](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/mixed-capture/verify_capture.py) · [certificate.json](https://riemann-compact-orbit.dreamymeter1.chatgpt.site/mixed-capture/certificate.json)

| File | SHA-256 |
| --- | --- |
| `certificate.json` | `80d2be4be09c53d63cda351b48862f5b0a4cf4fa8d888b7296260466e072da7e` |
| `verify_capture.py` | `c3cbe50db435e361557ae907d2a208809d6b87ee78fb2bfb1ef8a8816e8850fe` |

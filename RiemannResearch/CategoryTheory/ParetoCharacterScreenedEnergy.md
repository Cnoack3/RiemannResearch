# Computing the screened Pareto norm with characters

Let $\lambda=\log 2$, $P(n)=1/[n(n+1)]$ for $n\ge1$, $J_q(n)=\sum_{d\mid q}\mu(q/d)(n\bmod d)$, and $J_2=\mathbf1_{\rm odd}$. Let $M$ be the closed span of packets at conductors with at least two distinct prime factors. The target is $I=\langle u,u\rangle_P$, where $u=(I_H-P_M^P)J_2/\lambda$.

## Complete finite Grams and the exact tail

The character expansion is taken separately on the classes $g=(q,n)$, at the unit $n/g$ modulo $q/g$. Counting measure on the unit group supplies the Fourier coefficients. For $q>1$ the reflection about zero is $J_q(k)+J_q(q-k)=\varphi(q)-c_q(k)$ for $1\le k\le q$, where $c_q$ is the Ramanujan sum. Consequently a nontrivial unit group contributes a constant and odd modes. The zero-extended synthesis reconstructs every physical site, including the single class when $q/g=1$. The finite coefficients can be computed by their defining sum. [Gcd-class character reconstruction](ParetoPacketCharacters.lean)

For $L=\operatorname{lcm}(a,b)$, the full Pareto Gram $G_{ab}$ is the finite sum of the products of the two reconstructed rows against the masses
$$
 w_L(r)=\frac{\psi((r+1)/L)-\psi(r/L)}{L},\qquad 1\le r\le L.
$$
Here $\psi$ is digamma. Equivalently, the integration weight under the inverse-square law $Q$ is $B(n)=dP/dQ=\zeta(2)n/(n+1)$. Gram–Schmidt on the mixed conductors in increasing order gives $d_q=\langle e_q,J_2\rangle_P$ for the resulting orthonormal modes $e_q$. The finite sums keep every signed cross term. For a finite set $S$ of these modes,
$$
 U_S=\frac{\lambda-\sum_{q\in S}|d_q|^2}{\lambda^2}
     = I + \frac{1}{\lambda^2}\sum_{q\notin S}|d_q|^2.
$$
Thus $1\le I\le U_S$ and $U_S\downarrow I$ along the directed set of finite subsets. A raw dictionary gives the same finite projection when it spans the stated modes, in particular for initial segments. For arbitrary raw columns, perform the finite Gram fit on those columns. The repository's period-5040 trial already gives $I<1000/961$. Its earlier conductor-8192 enclosure, which combines a Lean implication with an external exact integer replay, gives $I<1.005097$. [Conductor-8192 evidence](../THEOREM_CATALOG_MIXED_CONDUCTOR_CRT_20261109.md#conductor-8192-enclosure-of-the-normalized-projection)

Proving that finite certificates reach $1+\varepsilon$ for every $\varepsilon>0$ is equivalent to RH. [Character rows, remainder and equivalence](ParetoCharacterScreenedEnergy.lean) · [Period-5040 bound](../RH/MixedCaptureLegalTrials.lean)

## A uniform conversion to Dirichlet powers

Set $r_n=(1-2/n)/3$ and, for $k\ge1$, use
$$
 w_k(n)=\frac{2}{3n^2}\sum_{j=0}^{2k-1}r_n^j
       =P(n)(1-r_n^{2k}).
$$
Since $|r_n|\le1/3$, all these weights are positive and
$$
 (1-9^{-k})P(n)\le w_k(n)\le P(n).
$$
The finite polynomial $w_k$ is a rational linear combination of $n^{-s}$ for $2\le s\le2k+1$. For instance $w_1(n)=8/(9n^2)-4/(9n^3)$. The estimate applies to squared norms of every linear combination, uniformly in the coefficients and dictionary.

For $F_{g,\chi}(n)=\mathbf1_{g\mid n}\chi(n/g)$ and $l=\operatorname{lcm}(g,h)$, the power Gram at exponent $s\ge2$ is
$$
 \sum_{n\ge1}\frac{F_{g,\chi}(n)\overline{F_{h,\eta}(n)}}{n^s}
 =\frac{\chi(l/g)\overline{\eta(l/h)}}{l^s}
     \sum_{j\ge1}\frac{\chi(j)\overline{\eta(j)}}{j^s}.
$$
The remaining Dirichlet series has an absolutely convergent Euler product. The divisibility identity follows by writing $n=lj$. It permits different moduli for $\chi$ and $\eta$. The rough-cofactor identity in the same module accounts for a future divisor coprime to the smooth multiplier and excluded primes. [Dirichlet-power mode pairing](DivisibilityCharacterGram.lean) · [Native cofactor moments](ValuationCharacterGram.lean)

Write $E_k(x)=\sum_n w_k(n)|x(n)|^2$ and $I_k=\inf_{m\in M}E_k(J_2/\lambda-m)$. The pointwise bound survives minimization over the **entire** mixed closure:
$$
 (1-9^{-k})I\le I_k\le I,\qquad
 0\le I-I_k\le \frac{1000}{961}\,9^{-k}.
$$
The proof of the upper inequality uses the actual Pareto minimizer as a competitor. For the lower inequality each competitor has Pareto cost at least $I$. For a supplied finite mixed trial $m$, one has the usable upper certificate $I\le E_k(J_2/\lambda-m)/(1-9^{-k})$. At $k=8$ the absolute error from the change of weight in the full minimum is less than $2.42\cdot10^{-8}$. Each mixed trial assigns one coefficient to each packet, which fixes all of its character components together. The finite dictionary error is a separate nonnegative term and still requires an estimate to certify the RH endpoint. [Uniform weight, trial and minimum bounds](ParetoCharacterWeight.lean)

## A certified finite example

For the first two mixed conductors the common period is $30$. Wolfram gives the following numerical values for the unnormalized target $J_2$:
$$
 G\approx\begin{pmatrix}1.813799364234&0.793034033542\\0.793034033542&3.303265999194\end{pmatrix},
 \qquad b\approx(-0.213752501557,-0.265338638477)^\top .
$$
The finite capture is $b^\top G^{-1}b\approx0.0351827869918$. Both modes together give
$$
 1.3694666791 < U_{\{6,10\}} < 1.3694666797 .
$$
As a separate symbolic check, Wolfram evaluated the degree-17 polynomial at $k=8$ through Hurwitz zeta values. In this two-packet space the normalized polynomial minimum is $1.36946666084284\ldots$ and its division by $1-9^{-8}$ gives $1.36946669265633\ldots$. The exact Lean expression for the full Pareto two-packet bound is **six_ten_upper**. The displayed decimals have a separate rational certificate. If $a=r+30M$ is the first omitted site of one residue class, then
$$
 \frac{1}{30a}\le \sum_{j\ge0}P(a+30j)\le\frac{1}{30(a+1-30)}.
$$
For a tail site $n$, bound $P(n)$ between $1/[n(n+30)]$ and $1/[(n+1-30)(n+1)]$. Both comparison sums telescope. The certificate encloses every residue mass and minimizes the lower and upper positive quadratic forms separately. It also encloses $\log2$ by the positive series $2\operatorname{arctanh}(1/3)$. The following Python 3 calculation uses only exact integer and rational arithmetic.

~~~python
"""Certify the two-packet Pareto minimum using integer and rational arithmetic."""

from fractions import Fraction

PERIOD = 30
BLOCKS = 10_000
SCALE = 10**24


def packet_row(site):
    parity = site % 2
    return parity, site % 6 - parity - site % 3, site % 10 - parity - site % 5


def residue_mass_bounds(residue):
    first_omitted = residue + PERIOD * BLOCKS
    rounded_head = sum(
        SCALE // (n * (n + 1)) for n in range(residue, first_omitted, PERIOD)
    )
    # The two rational tail bounds telescope along this residue class.
    lower_tail = SCALE // (PERIOD * first_omitted)
    upper_denominator = PERIOD * (first_omitted + 1 - PERIOD)
    upper_tail = (SCALE + upper_denominator - 1) // upper_denominator
    return (
        Fraction(rounded_head + lower_tail, SCALE),
        Fraction(rounded_head + BLOCKS + upper_tail, SCALE),
    )


def minimum(rows, weights):
    def gram(i, j):
        return sum(w * row[i] * row[j] for w, row in zip(weights, rows))

    g66, g610, g1010 = gram(1, 1), gram(1, 2), gram(2, 2)
    b6, b10 = gram(0, 1), gram(0, 2)
    determinant = g66 * g1010 - g610**2
    assert g66 > 0 and determinant > 0
    capture = (g1010 * b6**2 - 2 * g610 * b6 * b10 + g66 * b10**2) / determinant
    return gram(0, 0) - capture


def log_two_bounds(terms):
    x = Fraction(1, 3)
    lower = 2 * sum(x**(2*j + 1) / (2*j + 1) for j in range(terms))
    tail = 2 * x**(2*terms + 1) / ((2*terms + 1) * (1 - x*x))
    return lower, lower + tail


def main():
    rows = [packet_row(r) for r in range(1, PERIOD + 1)]
    lower_weights, upper_weights = zip(*(residue_mass_bounds(r) for r in range(1, PERIOD + 1)))
    lower_log, upper_log = log_two_bounds(24)
    lower = minimum(rows, lower_weights) / upper_log**2
    upper = minimum(rows, upper_weights) / lower_log**2
    assert Fraction(13694666791, 10**10) < lower <= upper < Fraction(13694666797, 10**10)
    print("1.3694666791 < two-packet Pareto upper bound < 1.3694666797")


if __name__ == "__main__":
    main()
~~~

The Lean proof of the scalar series uses direct finite Fourier coefficients. The closed primitive-conductor product in equation (2) of the supplied note is an optional reduction of these coefficients. The decimal cutoff matrices and the specialized Euler-product simplifications in equation (7) retain their symbolic and numerical status.

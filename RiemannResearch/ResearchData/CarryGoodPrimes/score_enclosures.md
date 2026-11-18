# Finite membership in the one-divisor prime sets

Here $b_p$ is the greatest score over old divisors, $G_1$ uses the floor $1/p$, and $A_1$ uses $1/[p(1+H_{A_1}(p))]$. Each row uses the full old divisor space plus $g_p$ to screen the candidate atom $g_{pd}$. The following are external Arb enclosures computed at 160-bit working precision. The separate Lean first-block proof gives $2.950256\le b_3\le2.950261$. [Lean definitions and first block](../../RH/QCRTCarryGoodPrimes.lean)

| $p$ | Maximizing $d$ | Enclosure for $b_p$ | $G_1$ | $A_1$ |
|---:|---:|---:|:---:|:---:|
| 3 | 2 | $[2.95025826876888,2.95025826876890]$ | yes | yes |
| 5 | 3 | $[1.97174889747482,1.97174889747484]$ | yes | yes |
| 7 | 6 | $[0.0991513613988382,0.0991513613988384]$ | no | yes |
| 11 | 3 | $[0.296435089153708,0.296435089153710]$ | yes | yes |
| 13 | 7 | $[0.280279283679085,0.280279283679087]$ | yes | yes |

If $D$ is the product of primes through $p$, the complete $Q$ mass of residue $r$, indexed $1\le r\le D$, is $\zeta(2,r/D)/(D^2\zeta(2))$. Wolfram gives $\sum_{k\ge0}(30k+1)^{-2}=\psi_1(1/30)/900$ for one row of the period-$30$ Gram. At $p=7$, the earlier accepted primes are $3,5$, giving the exact threshold $[7(1+1/3+1/5)]^{-1}=15/161$. [DLMF §25.11](https://dlmf.nist.gov/25.11) · [Wolfram residue sum](https://www.wolframalpha.com/input?i=sum+1%2F%2830k%2B1%29%5E2%2C+k%3D0+to+infinity) · [Wolfram cutoff](https://www.wolframalpha.com/input?i=1%2F%287%2A%281%2B1%2F3%2B1%2F5%29%29)

The script uses python-flint 0.9.0 with FLINT 3.6.0. It forms the Schur complement of the base Gram in the joint Gram of the constant, all base atoms, and all candidate atoms. The constant's screened diagonal is $e_p$. The off-diagonal sign of the carry disappears when the pairing is squared. The comparisons certify every strict maximum, both membership decisions, and positive denominators using ball arithmetic. [Arb arithmetic](https://doi.org/10.1109/TC.2017.2690633)

```python
"""Enclose one-divisor Q scores using complete periodic weights and Arb solves.

Run with python-flint installed. All threshold comparisons use ball arithmetic.
"""
from math import prod
from flint import arb, arb_mat, ctx


def score_block(p, old_primes):
    period = p * prod(old_primes)
    divisors = sorted({prod(q for i, q in enumerate(old_primes) if mask >> i & 1)
                       for mask in range(1, 2 ** len(old_primes))})
    base = divisors + [p]
    conductors = [1] + base + [p * d for d in divisors]
    dimension = len(conductors)
    gram = arb_mat(dimension, dimension)
    scale = arb(2).zeta() * period**2
    for start in range(1, period + 1, 256):
        residues = range(start, min(start + 256, period + 1))
        weights = [arb(2).zeta(arb(r) / period) / scale for r in residues]
        rows = [[arb(1)] * len(weights)]
        rows.extend([[arb(r % d) / d for r in residues] for d in conductors[1:]])
        weighted = [[x * w for x, w in zip(row, weights)] for row in rows]
        gram += arb_mat(weighted) * arb_mat(rows).transpose()
    base_indices = range(1, len(base) + 1)
    test_indices = [0] + list(range(1 + len(base), dimension))
    base_gram = arb_mat([[gram[i, j] for j in base_indices] for i in base_indices])
    cross = arb_mat([[gram[i, j] for j in test_indices] for i in base_indices])
    raw = arb_mat([[gram[i, j] for j in test_indices] for i in test_indices])
    screened = raw - cross.transpose() * base_gram.solve(cross)
    error = screened[0, 0]
    assert error > 0
    scores = []
    for j in range(1, len(test_indices)):
        assert screened[j, j] > 0
        scores.append(screened[0, j]**2 / (error**2 * screened[j, j]))
    winners = [i for i, s in enumerate(scores)
               if all(i == j or s > t for j, t in enumerate(scores))]
    assert len(winners) == 1
    i = winners[0]
    return divisors[i], scores[i]


if __name__ == "__main__":
    ctx.prec = 160
    old = [2]
    mass = arb(0)
    for p in (3, 5, 7, 11, 13):
        divisor, score = score_block(p, old)
        reciprocal = arb(1) / p
        adaptive_floor = reciprocal / (1 + mass)
        assert score > reciprocal or score < reciprocal
        assert score > adaptive_floor or score < adaptive_floor
        fixed, adaptive = score > reciprocal, score > adaptive_floor
        print(p, divisor, score.str(15), fixed, adaptive, flush=True)
        if adaptive:
            mass += reciprocal
        old.append(p)
```

# Simultaneous coprime-pair certificates for rational minimizers

21 October 2026. Source: a direct finite square-completion argument in the
user-directed signed-tail investigation. This note makes no claim of
historical novelty. All divisor atoms are retained in the actual minimizer.

## Verification status of the earlier work

The finite tail, duality, and three-site results were published at
`0305b41a36a6f63d3195449613c1a39e698331cd` after checkpoint
`job_7o8tf3lFETYugP3jOntI51L6Y_XISLcx` succeeded.

The subsequent commit `ed3d1f662c8b8f6e215f9b43859ee019a5612e04` already
formalized the unconditional primorial limit S/R -> -1 and the necessary
relative absorption-error scale. The server record was recovered in this
continuation: checkpoint `job_RvDgLsaJ5yP_uxHEsSYBO1hYt7bQSNBE` succeeded,
validated the aggregate plus seven changed modules, and pushed that exact
commit. Its saved-module audit `job_awqRyI7OtahWXdqkX6zwSEvCMZALDqt6`
reported only propext, Classical.choice, and Quot.sound for the inspected
principal declarations. Thus the ratio limit is now formally established;
the older note's statement that it was informal has been superseded.

## Exact simultaneous-pair identity

Write r_a=1-F_L(a), w_a=1/a^2+2/[L(2a+L)], b=5/(3L^2), and
E=R_L-b. Choose a finite set Q of q with 3<=q<L and gcd(q,L)=1,
and require Q and {q-1:q in Q} to be disjoint. The predecessor map is
injective on Q, and the selected pairs avoid site 1 and the endpoint L.
For even L, distinct coprime sites are odd, so this disjointness is automatic.
The Lean theorem retains disjointness explicitly and checks it by computation
in the concrete certificate below.

The established coprime jump relation gives r_1+r_(q-1)-r_q=1. Put

    h_q = w_(q-1) w_q / (w_(q-1)+w_q),
    A = sum_(q in Q) h_q,
    C_Q = w_1 A/(w_1+A).

Let U be the unused interior sites, excluding 1 and every selected pair.
The new exact identity is

    E-C_Q = sum_(a in U) w_a r_a^2
          + ((w_1+A)r_1-A)^2/(w_1+A)
          + sum_(q in Q) (w_(q-1)r_(q-1)+w_q r_q)^2/(w_(q-1)+w_q).

Each remainder is nonnegative. Hence

    R_L >= b+C_Q,
    0 <= 1+S_L/R_L <= [phi(L)b]/(b+C_Q).

The proof expands the weighted two-point identity

    a u^2+b v^2 = ab(u-v)^2/(a+b)+(au+bv)^2/(a+b),

then completes the common r_1 square. This addresses the shared coordinate
exactly; adding independent three-site lower bounds would count its energy
more than once and would not be valid.

Owners and principal declarations:

- `Analysis/CoprimePairEnergy.lean`: `shared_pair_energy_gap`,
  `shared_pair_energy_lower`, `effectiveEnergy_sub`, and
  `shared_bound_strictly_improves_single`.
- `RH/QRationalCoprimePairs.lean`: `rational_coprime_pairs_gap`,
  `rationalMinimum_coprime_pairs_lower`,
  `rationalSignedTail_coprime_pairs_ratio_bound`, and
  `signed_absorption_fails_of_coprime_pairs`.

## Strict improvement and scope of sharpness

For a selected q, the earlier three-site bound is

    C_{q} = w_1 h_q/(w_1+h_q)
          = 1/(1/w_1+1/w_(q-1)+1/w_q).

The exact improvement is

    C_Q-C_{q} = w_1^2(A-h_q)/[(w_1+A)(w_1+h_q)].

This is strictly positive when a second pair is selected. The generic Lean
strict-improvement theorem requires positive weights and an explicit second
member of Q.

The square identity is sharp for the relaxation retaining only the selected
coprime jump equations. Equality requires zero unused residuals, zero weighted
pair means, and r_1=A/(w_1+A). This characterization is an algebraic reading of
the displayed identity, not a claim that these residuals belong to the complete
divisor model. All other gcd-class and normal-equation constraints can make the
actual minimum larger.

## Stronger seventh-primorial obstruction

For L=510510 and

    Q={19,23,29,31,37,41,43,47,53,59,
       61,67,71,73,79,83,89,97,101,103},

exact arithmetic proves

    S_510510 < -(9999/10000) R_510510.

The Lean declaration `seventh_primorial_twenty_pair_absorption_fails` has no
hypotheses. It uses phi(510510)=92160, the general pair theorem, and kernel-checked
rational normalization. No optimizer coefficients are computed for this period.
The previous factor was 1999/2000. The full rational certificate for -S/R
has approximate displayed value 0.9999000210594624; the strict rational
comparison with 9999/10000 is the certified assertion.

## Independent exact finite checks

The reproducible Python below uses Fraction throughout. It checks the full
normal equations and exact remainder identity for the actual complete-divisor
minimizers at L=6,30,210. No logarithmic-head minimum is computed.

| L | selected pairs | certified E lower bound | certified -S/R lower bound | actual -S/R |
|---:|---:|---:|---:|---:|
| 6 | 1 | 0.03450112385 | -0.1459845181 | -0.01418946515 |
| 30 | 7 | 0.02751332701 | 0.4954972049 | 0.6487786991 |
| 210 | 47 | 0.01633598236 | 0.8892094872 | 0.9348102299 |

Certificates requiring no optimizer solve:

| L | selected pairs | certified -S/R lower bound |
|---:|---:|---:|
| 210 | 10 | 0.8716271138 |
| 2310 | 10 | 0.9845825245 |
| 30030 | 10 | 0.9984247864 |
| 510510 | 10 | 0.9998841937 |
| 510510 | 20 | 0.9999000211 |

All comparisons in the script are exact; the tables only display decimals.
The compact subsidiary bound A>5929/1000000, C_Q>=5929/1005929 also
suffices for the strict 9999/10000 threshold. That shortcut is a Python
subcertificate; the Lean concrete proof normalizes the full weights directly.

## What remains open

These results strengthen a lower bound on R and an upper bound on S.
They do not supply the lower bound on S required for fixed-factor absorption
with a vanishing absolute error. The already verified unconditional ratio
S/R -> -1 implies that every valid error eventually pays any fixed fraction
below (1-theta) of R. In particular, errors o(R) cannot work even cofinally.
Errors tending to zero in absolute size remain possible only if the minimum
tends to zero. The missing substantive result is still an independent upper
estimate forcing R_(primorialPeriod n)->0, or an equivalent arithmetic provider
for the constrained dual upper bound. Neither constant squarefree closure nor
RH is assumed or proved here.

## New verification evidence

Development job `job_HKC02IT4IM9xWYMvWx_hJO1lz6I-u0BX` returned verified=true,
exit code 0, for the combined general algebra, actual-minimizer identity,
normalized bound, strict improvement, and concrete 20-pair obstruction.
The saved modules remove the development candidate's two local linter warnings
and explicitly import their directly used owning modules. Final saved-source
validation and publication are gated by the server checkpoint. Its terminal
job, validation scope, and exact commit are reported to the user separately.
Saved-module audit `job_KNfBYwUiy6-7hs9radU-TL6CNWUc4G86` also succeeded,
verified=true, exit code 0. It built both new modules and inspected the actual
gap, normalized bound, and hypothesis-free concrete theorem. The inspected
strict-improvement, actual-gap, and concrete-obstruction declarations use only
propext, Classical.choice, and Quot.sound. No new-source linter warnings remained.
Python checks are independent finite arithmetic evidence, not Lean verification.

## Reproducible exact checks

Save the following as `coprime_pair_checks.py` and run with Python 3.11 or later.
It writes exact fractions and displayed decimals to `coprime_pair_checks.json`.

```python
"""Exact simultaneous coprime-pair checks for complete-divisor minimizers.

Source: direct square completion in the user-directed 21 October 2026
investigation. This is finite rational arithmetic, not a Lean verification.
The exact solver is reused from tail_experiments.py and included here so this
file can be rerun independently. No logarithmic-head minimum is computed.
"""

from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import sys

sys.set_int_max_str_digits(0)
F = Fraction


def solve(matrix, rhs):
    """Exact Gauss-Jordan solver reused from the previous finite checks."""
    augmented = [list(row) + [value] for row, value in zip(matrix, rhs)]
    n = len(rhs)
    for j in range(n):
        pivot = next(i for i in range(j, n) if augmented[i][j])
        augmented[j], augmented[pivot] = augmented[pivot], augmented[j]
        divisor = augmented[j][j]
        augmented[j] = [value / divisor for value in augmented[j]]
        for i in range(n):
            if i != j:
                multiplier = augmented[i][j]
                if multiplier:
                    augmented[i] = [value - multiplier * source
                                    for value, source in zip(augmented[i], augmented[j])]
    return [row[-1] for row in augmented]


def weight(L, a):
    return F(1, a * a) + F(2, L * (2 * a + L))


def totient(L):
    n, answer, p = L, L, 2
    while p * p <= n:
        if n % p == 0:
            answer -= answer // p
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        answer -= answer // n
    return answer


def coprime_sites(L, count=None):
    result = []
    for q in range(3, L):
        if gcd(q, L) == 1:
            result.append(q)
            if count is not None and len(result) == count:
                return result
    return result


def encoded(value):
    return {"exact": str(value), "decimal": float(value)}


def certificate(L, sites):
    assert len(sites) == len(set(sites))
    assert all(3 <= q < L and gcd(q, L) == 1 for q in sites)
    predecessors = {q - 1 for q in sites}
    assert predecessors.isdisjoint(sites)
    w1 = weight(L, 1)
    h = {q: weight(L, q - 1) * weight(L, q) /
         (weight(L, q - 1) + weight(L, q)) for q in sites}
    A = sum(h.values(), F(0))
    inverse_square_A = sum((F(1, (q - 1)**2 + q**2) for q in sites), F(0))
    assert A >= inverse_square_A
    lower = w1 * A / (w1 + A)
    b = F(5, 3 * L * L)
    boundary = totient(L) * b
    rho = 1 - boundary / (b + lower)
    single = {q: w1 * hq / (w1 + hq) for q, hq in h.items()}
    assert all(lower >= value for value in single.values())
    if len(sites) >= 2:
        assert all(lower > value for value in single.values())
    for q, hq in h.items():
        assert lower - single[q] == w1**2 * (A - hq) / ((w1 + A) * (w1 + hq))
        old_K = 1 / w1 + 1 / weight(L, q - 1) + 1 / weight(L, q)
        assert single[q] == 1 / old_K
    result = {
        "L": L,
        "sites": sites,
        "phi": totient(L),
        "conductance": encoded(A),
        "inverse_square_conductance_lower": encoded(inverse_square_A),
        "energy_lower": encoded(lower),
        "minimum_lower": encoded(b + lower),
        "minus_signed_tail_over_minimum_lower": encoded(rho),
        "best_selected_single_site_lower": encoded(max(single.values(), default=F(0))),
        "strictly_improves_every_selected_single_site": len(sites) >= 2,
        "rho_gt_9999_over_10000": rho > F(9999, 10000),
        "margin_over_9999_over_10000": encoded(rho - F(9999, 10000)),
    }
    return result


def actual_minimum_check(L):
    divisors = [d for d in range(2, L + 1) if L % d == 0]
    w = {a: weight(L, a) for a in range(1, L + 1)}
    g = {a: [F(a % d, d) for d in divisors] for a in range(1, L + 1)}
    gram = [[sum(w[a] * g[a][i] * g[a][j] for a in w)
             for j in range(len(divisors))] for i in range(len(divisors))]
    rhs = [sum(w[a] * g[a][i] for a in w) for i in range(len(divisors))]
    coefficients = solve(gram, rhs)
    residual = {a: 1 - sum(x * y for x, y in zip(g[a], coefficients)) for a in w}
    normal = all(sum(w[a] * residual[a] * g[a][j] for a in w) == 0
                 for j in range(len(divisors)))
    R = sum(w[a] * residual[a]**2 for a in w)
    b = F(5, 3 * L * L)
    E = R - b
    sites = coprime_sites(L)
    cert = certificate(L, sites)
    A = F(cert["conductance"]["exact"])
    lower = F(cert["energy_lower"]["exact"])
    selected = {1} | set(sites) | {q - 1 for q in sites}
    unused = set(range(1, L)) - selected
    unused_energy = sum((w[a] * residual[a]**2 for a in unused), F(0))
    center_gap = ((w[1] + A) * residual[1] - A)**2 / (w[1] + A)
    pair_gap = sum(((w[q - 1] * residual[q - 1] + w[q] * residual[q])**2 /
                    (w[q - 1] + w[q]) for q in sites), F(0))
    tail, tails = F(0), {}
    for a in range(L, 0, -1):
        tail += w[a] * residual[a]
        tails[a] = tail
    S = sum((tails[a] for a in range(2, L + 1) if gcd(a, L) == 1), F(0))
    checks = {
        "all_divisor_normal_equations": normal,
        "endpoint_residual": residual[L] == 1,
        "all_selected_coprime_jumps": all(
            residual[1] + residual[q - 1] - residual[q] == 1 for q in sites),
        "exact_nonnegative_gap": E - lower == unused_energy + center_gap + pair_gap,
        "all_gap_terms_nonnegative": min(unused_energy, center_gap, pair_gap) >= 0,
        "minimum_lower": b + lower <= R,
        "signed_identity": R + S == totient(L) * b,
        "signed_ratio_certificate": -S / R >= F(cert["minus_signed_tail_over_minimum_lower"]["exact"]),
    }
    assert all(checks.values()), checks
    return {
        "L": L,
        "divisor_atoms": len(divisors),
        "selected_pair_count": len(sites),
        "checks": checks,
        "R": encoded(R),
        "E": encoded(E),
        "S": encoded(S),
        "energy_lower": encoded(lower),
        "unused_energy": encoded(unused_energy),
        "center_gap": encoded(center_gap),
        "pair_gap": encoded(pair_gap),
        "minus_S_over_R": encoded(-S / R),
        "certificate": cert,
    }


def main():
    actual = []
    for L in (6, 30, 210):
        item = actual_minimum_check(L)
        actual.append(item)
        print(json.dumps({"actual_L": L, "all_checks_passed": all(item["checks"].values()),
                          "selected_pairs": item["selected_pair_count"],
                          "R": item["R"]["decimal"],
                          "energy_lower": item["energy_lower"]["decimal"]}), flush=True)
    certificates = []
    for L, count in ((210, 10), (2310, 10), (30030, 10), (510510, 10), (510510, 20)):
        item = certificate(L, coprime_sites(L, count))
        assert len(item["sites"]) == count
        certificates.append(item)
        print(json.dumps({"certificate_L": L, "pair_count": count,
                          "rho": item["minus_signed_tail_over_minimum_lower"]["decimal"],
                          "rho_gt_9999_over_10000": item["rho_gt_9999_over_10000"]}), flush=True)
    assert certificates[-1]["rho_gt_9999_over_10000"]
    # A compact rational subcertificate avoids the very large exact weight
    # denominators and still proves the same strict 9999/10000 obstruction.
    L = 510510
    A0 = F(certificates[-1]["inverse_square_conductance_lower"]["exact"])
    assert A0 > F(5929, 1000000)
    simple_energy = F(5929, 1005929)
    b = F(5, 3 * L * L)
    simple_rho = 1 - totient(L) * b / (b + simple_energy)
    assert simple_rho > F(9999, 10000)
    simple = {"L": L, "conductance_lower": "5929/1000000",
              "energy_lower": encoded(simple_energy),
              "rho_lower": encoded(simple_rho),
              "rho_gt_9999_over_10000": True}
    output = {"verification": "Exact Python Fraction checks; not a Lean verification",
              "actual_minimizers": actual, "certificates": certificates,
              "compact_seventh_primorial_subcertificate": simple}
    path = Path(__file__).with_name("coprime_pair_checks.json")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(str(path), flush=True)


if __name__ == "__main__":
    main()
```

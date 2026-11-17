# Floating-point occurrence diagnostic reproduction

The following is the complete source executed locally. Save the code block as
`occurrence_diagnostics.py` and run it with Python, NumPy, SciPy and SymPy.
The JSON records the versions used. This is documentation of an external
experiment, not an executable Lean provider.

```python
#!/usr/bin/env python3
"""Floating-point diagnostics, not a proof or an interval certificate.

Source: sdf_modified.pdf, sections 14.9 and 14.14. The full progression
weight is evaluated using the digamma formula. Output includes plain and
weighted fiber means, with an optional exact-arithmetic-form global charge
constraint. All arithmetic in this script is IEEE float64.
"""
import json
import math
import platform
from pathlib import Path

import numpy as np
import scipy
from scipy.special import digamma
import sympy
from sympy import primerange


def stage(x):
    P = math.prod(primerange(1, x + 1))
    r = np.arange(1, P, dtype=np.int64)
    g = np.gcd(r, P)
    w = (digamma((r + 1) / P) - digamma(r / P)) / P
    target = np.cumsum(g == 1, dtype=float) - 1
    free = np.flatnonzero(g > x)
    ends = np.r_[free[1:], len(r)]
    # Direct block summation avoids subtracting two nearly equal cumulative masses.
    mass = np.add.reduceat(w, free)
    moment = np.add.reduceat(w * target, free)
    block_mean = moment / mass
    coeff = np.diff(np.r_[0., block_mean])
    labels = g[free]
    _, idx, counts = np.unique(labels, return_inverse=True, return_counts=True)
    atom_mean = np.bincount(idx, weights=coeff) / counts
    D = float(np.sum((coeff - atom_mean[idx]) ** 2))
    fitted = np.zeros_like(target)
    fitted[free] = coeff
    fitted = np.cumsum(fitted)
    qocc = float(np.sum(w * (target - fitted) ** 2))

    def trial(u):
        increment = coeff - u[idx]
        residual = np.zeros_like(target)
        residual[free] = increment
        residual = np.cumsum(residual)
        return dict(green_energy=float(np.sum(w * residual ** 2)),
                    total_increment=float(np.sum(increment)))

    candidates = []
    for exponent in [0., .5, 1., 1.5, 2.]:
        omega = r[free].astype(float) ** -exponent
        W = np.bincount(idx, weights=omega)
        mean = np.bincount(idx, weights=omega * coeff) / W
        for constrained in [False, True]:
            u = mean.copy()
            if constrained:
                lagrange = (np.sum(coeff) - np.dot(counts, mean)) / np.sum(counts ** 2 / W)
                u += lagrange * counts / W
            candidates.append(dict(exponent=exponent, charge_constraint=constrained, **trial(u)))
    return dict(x=x, P=P, occurrence_energy=qocc,
                unweighted_return_dispersion=D,
                mean_coefficient_green_trial=trial(atom_mean)['green_energy'],
                candidate_trials=candidates)


if __name__ == '__main__':
    result = dict(status='floating-point diagnostic only',
                  runtime=dict(python=platform.python_version(), numpy=np.__version__,
                               scipy=scipy.__version__, sympy=sympy.__version__),
                  stages=[stage(x) for x in [5, 7, 11, 13, 17]])
    Path('occurrence_diagnostics.json').write_text(json.dumps(result, indent=2) + '\n')
    for row in result['stages']:
        best = min(row['candidate_trials'], key=lambda c: c['green_energy'])
        print(json.dumps({k: v for k, v in row.items() if k != 'candidate_trials'} | {'best_trial': best}))
```

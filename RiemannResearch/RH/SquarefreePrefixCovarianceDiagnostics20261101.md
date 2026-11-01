# Squarefree prefix covariance: numerical reproduction

Date: 1 November 2026. Status: exploratory float64; no interval certification.

The complete-Q Gram and multiplier moments use analytically complete period
weights. The physical head and the displayed block are finite because the
quantities being evaluated are finite; a physical tail truncation is never
substituted for a full Gram or target moment. All active composite squarefree
conductors are included. The Schur calculation retains every high conductor
through its head-null contrast with the chosen legal anchor.

This extends the code and weight formulas in
[SquarefreePrefixResponseDiagnostics20261030.md](SquarefreePrefixResponseDiagnostics20261030.md).
See [the research report](SquarefreePrefixCovarianceResearch20261101.md) for proofs,
limits of the estimate, and the Open arithmetic provider.

Runtime: NumPy 2.3.5, SciPy 1.17.0, threadpoolctl. Save the following standalone
code as squarefree_prefix_covariance.py and run python squarefree_prefix_covariance.py.
The final M=128 block at N=160 or N=240 can extend beyond the stage index;
the canonical projection is defined at every physical site.

The computed dispersion is evaluated by WJ-T^2. For H=1 it is mathematically
zero; a floating-point value around -1e-19 is roundoff. The loss covariance
matrix is formed by subtracting complete projected covariance from the exact
centered-source covariance. Eigenvalues and equality discrepancies are
consistency diagnostics, not rigorous enclosures or asymptotic evidence.

## Reproduction code

```python
"""Float64 checks using the complete-Q period Gram from the prior diagnostics."""
import json
import math
import numpy as np
import scipy.linalg as la
from threadpoolctl import threadpool_limits
from scipy.special import digamma, polygamma

ZETA2 = math.pi**2 / 6


def squarefree(n):
    return all(n % (p*p) for p in range(2, math.isqrt(n)+1))


def weights(L):
    x = np.arange(1,L+1,dtype=float)
    q = polygamma(1,x/L)/(ZETA2*L*L)
    qb = q + (digamma(x/L)-digamma((x+1)/L))/(ZETA2*L)
    return x,q,qb


class CompleteGram:
    def __init__(self, maximum):
        self.ds = np.array([d for d in range(2,maximum+2) if squarefree(d)],dtype=int)
        k = len(self.ds)
        self.G, self.H = np.zeros((k,k)),np.zeros((k,k))
        self.mu, self.nu = np.zeros(k),np.zeros(k)
        self.built = 0

    def through(self,N):
        count = int(np.searchsorted(self.ds,N+1,side='right'))
        for i in range(self.built,count):
            d = int(self.ds[i])
            x,q,qb = weights(d)
            gd = np.remainder(x,d)/d
            self.mu[i], self.nu[i] = gd@q, gd@qb
            for j in range(i+1):
                e = int(self.ds[j])
                x,q,qb = weights(math.lcm(d,e))
                both = (np.remainder(x,d)/d)*(np.remainder(x,e)/e)
                self.G[i,j] = self.G[j,i] = both@q
                self.H[i,j] = self.H[j,i] = both@qb
        self.built = count
        return (self.ds[:count],self.G[:count,:count],self.H[:count,:count],
                self.mu[:count],self.nu[:count])



def investigate(N, cache):
    ds, G, GB, mu, nu = cache.through(N)
    chol = la.cho_factor(G, lower=True)
    solve = lambda b: la.cho_solve(chol, b)
    alpha = solve(mu)
    eps = float(1-mu@alpha)
    out = {"N":N, "conductors":len(ds), "epsilon":eps, "blocks":[]}
    for M in [16,32,64,128]:
        if M>N:
            continue
        H = int(M/(6+math.log(M)))
        n = np.arange(M+1,2*M+1,dtype=float)
        m = np.arange(1,H+1,dtype=float)
        Rh = (m[:,None]%ds)/ds
        Rn = (n[:,None]%ds)/ds
        Qh = 1/(ZETA2*m*m)
        r = 1-Rh@alpha
        z0 = Rh.T@(Qh*r)
        zb = Rh.T@(Qh*r/(m+1))
        x0, xb = solve(z0), solve(zb)
        T = Rn@xb-(Rn@x0)/(n+1)
        E0, Eb = float(z0@x0), float(zb@xb)
        delta0 = float(E0-np.sum(Qh*(Rh@x0)**2))
        deltab = float(Eb-np.sum(Qh*(Rh@xb)**2))
        bound = 8*ZETA2*M*M*(deltab+delta0/(M+2)**2)
        # All cross-prefix covariances are retained in this matrix.
        zs = np.cumsum((Qh*r)[:,None]*Rh,axis=0).T
        C = zs.T@solve(zs)
        u = np.cumsum(Qh*r*r)
        Cbase = u[np.minimum.outer(np.arange(H),np.arange(H))]-np.outer(u,u)/eps
        L = Cbase-C
        terms = ((Qh*r)[:,None]*(Rh@solve(Rn.T)))
        prefixes = np.cumsum(terms,axis=0)
        wi = 1/(m+2)
        xi = prefixes/(m+1)[:,None]
        wend = (H+1)*(1/(H+2)-1/(n+1))
        xend = prefixes[-1]/(H+1) if H else np.zeros_like(n)
        W = wi.sum()+wend
        J = np.sum(wi[:,None]*xi*xi,axis=0)+wend*xend*xend
        D = (W*J-T*T)
        # Compression E-E^2 is the complete off-head energy, with no tail cutoff.
        E = np.sqrt(Qh)[:,None]*Rh@solve(Rh.T)*np.sqrt(Qh)[None,:]
        bh = np.sqrt(Qh)*r/(m+1)
        defect = float(bh@(E-E@E)@bh)
        out["blocks"].append(dict(M=M,H=H,block_sum=float(T@T),
            raw_abel=float(np.sum(W*J)),dispersion=float(np.sum(D)),
            delta_B=deltab,delta_0=delta0,block_bound=bound,
            M_delta_B=M*deltab,captured_B=Eb,
            compression_defect_error=abs(defect-deltab),
            loss_covariance_min_eigenvalue=float(la.eigvalsh(L)[0]),
            moment_error=float(np.max(np.abs(T-(np.sum(wi[:,None]*xi,axis=0)+wend*xend)))) ))
    if N==240:
        n=221
        m=np.arange(1,n,dtype=float)
        R=(m[:,None]%ds)/ds
        vn=(n%ds)/ds
        r=1-R@alpha
        terms=(r/(ZETA2*m*m))*(R@solve(vn))
        ranges=[(1,1),(2,3),(4,7),(8,15),(16,31),(32,63),(64,127),(128,220)]
        out["aligned_site"]=dict(n=n,ranges=[dict(lo=a,hi=b,value=float(np.sum(terms[a-1:b]*(1/(m[a-1:b]+1)-1/(n+1))))) for a,b in ranges])
        # Full (n-1)-head scalar Abel dispersion.
        A=np.cumsum(terms)
        w=1/(m+2); x=A/(m+1)
        T=float(np.sum(w*x)); W=float(w.sum()); J=float(np.sum(w*x*x))
        out["aligned_site"].update(T=T,W=W,J=J,D=W*J-T*T,D_over_WJ=(W*J-T*T)/(W*J))
        # Schur elimination retains every large conductor via its head-null basis.
        H=110
        low=np.flatnonzero(ds<=H); high=np.flatnonzero(ds>H); anchor=high[0]
        eye=np.eye(len(ds))
        rho=np.column_stack([ds[anchor]*eye[:,anchor]]+[ds[i]*eye[:,i]-ds[anchor]*eye[:,anchor] for i in low])
        tau=np.column_stack([eye[:,i]-(ds[anchor]/ds[i])*eye[:,anchor] for i in high if i!=anchor])
        Ew=tau.T@G@tau
        psi=rho-tau@la.solve(Ew,tau.T@G@rho,assume_a="pos")
        S=psi.T@G@psi
        mh=m[:H]; Rh=R[:H]; Qh=1/(ZETA2*mh*mh); rh=r[:H]
        z=Rh.T@(Qh*rh)
        q=(Rh@rho).T@(Qh*rh)
        SchurA=float((vn@psi)@la.solve(S,q,assume_a="pos"))
        directA=float(vn@solve(z))
        out["aligned_site"].update(prefix_H=H,Schur_prefix=SchurA,direct_prefix=directA,Schur_error=abs(SchurA-directA))
    return out

if __name__=="__main__":
    with threadpool_limits(limits=1):
        cache=CompleteGram(240)
        result=[investigate(N,cache) for N in [80,160,240]]
    print(json.dumps(result,indent=2))
```

## Recorded output

```json
[
  {
    "N": 80,
    "conductors": 49,
    "epsilon": 0.00729568853590945,
    "blocks": [
      {
        "M": 16,
        "H": 1,
        "block_sum": 4.6768107075098866e-05,
        "raw_abel": 4.676810707509879e-05,
        "dispersion": -7.501866411365919e-20,
        "delta_B": 1.0231861138413558e-06,
        "delta_0": 4.092744455365423e-06,
        "block_bound": 0.003489489680345136,
        "M_delta_B": 1.6370977821461693e-05,
        "captured_B": 1.823501853501651e-05,
        "compression_defect_error": 3.3881317890172014e-21,
        "loss_covariance_min_eigenvalue": 3.517533867588145e-06,
        "moment_error": 3.209238430557093e-17
      },
      {
        "M": 32,
        "H": 3,
        "block_sum": 0.00019456234479461822,
        "raw_abel": 0.00022324992986564896,
        "dispersion": 2.8687585071030728e-05,
        "delta_B": 5.033911212786565e-07,
        "delta_0": 2.8244654991986073e-06,
        "block_bound": 0.006816270638859714,
        "M_delta_B": 1.6108515880917007e-05,
        "captured_B": 2.1821345759965594e-05,
        "compression_defect_error": 6.670384459627615e-21,
        "loss_covariance_min_eigenvalue": 9.009158587010339e-09,
        "moment_error": 7.101524229780054e-17
      },
      {
        "M": 64,
        "H": 6,
        "block_sum": 0.008708931475139082,
        "raw_abel": 0.01205608983591596,
        "dispersion": 0.00334715836077688,
        "delta_B": 3.858772969679555e-06,
        "delta_0": 0.00012913182337762004,
        "block_bound": 0.20959037050130813,
        "M_delta_B": 0.0002469614700594915,
        "captured_B": 2.7718750194334172e-05,
        "compression_defect_error": 1.6940658945086007e-21,
        "loss_covariance_min_eigenvalue": 6.757127869573909e-11,
        "moment_error": 1.1362438767648086e-16
      }
    ]
  },
  {
    "N": 160,
    "conductors": 98,
    "epsilon": 0.006123771763566488,
    "blocks": [
      {
        "M": 16,
        "H": 1,
        "block_sum": 3.0126325907943325e-05,
        "raw_abel": 3.0126325907943213e-05,
        "dispersion": -1.1250979819701261e-19,
        "delta_B": 7.188455857693586e-07,
        "delta_0": 2.8753823430774345e-06,
        "block_bound": 0.0024515620563755587,
        "M_delta_B": 1.1501529372309738e-05,
        "captured_B": 1.3255437924617221e-05,
        "compression_defect_error": 1.1540823906339842e-20,
        "loss_covariance_min_eigenvalue": 2.527018761434102e-06,
        "moment_error": 5.182486384480711e-17
      },
      {
        "M": 32,
        "H": 3,
        "block_sum": 8.535941250481543e-05,
        "raw_abel": 0.00010263328299528048,
        "dispersion": 1.7273870490465055e-05,
        "delta_B": 3.1793769154744966e-07,
        "delta_0": 1.7223666311916958e-06,
        "block_bound": 0.004304383076931141,
        "M_delta_B": 1.017400612951839e-05,
        "captured_B": 1.5673561772117313e-05,
        "compression_defect_error": 1.1752582143153417e-20,
        "loss_covariance_min_eigenvalue": 2.610690146935027e-09,
        "moment_error": 1.1839487723541708e-16
      },
      {
        "M": 64,
        "H": 6,
        "block_sum": 0.004156267112033519,
        "raw_abel": 0.005815784640820794,
        "dispersion": 0.0016595175287872754,
        "delta_B": 2.664723138829386e-06,
        "delta_0": 9.107323201176839e-05,
        "block_bound": 0.14475871485825845,
        "M_delta_B": 0.0001705422808850807,
        "captured_B": 2.0165126589668185e-05,
        "compression_defect_error": 5.929230630780102e-21,
        "loss_covariance_min_eigenvalue": 3.092752352193859e-11,
        "moment_error": 1.726049858596923e-16
      },
      {
        "M": 128,
        "H": 11,
        "block_sum": 0.030628019070826802,
        "raw_abel": 0.04141337781285224,
        "dispersion": 0.01078535874202544,
        "delta_B": 3.1467228376549763e-06,
        "delta_0": 0.00015160128057577882,
        "block_bound": 0.6803826224849253,
        "M_delta_B": 0.00040278052321983697,
        "captured_B": 2.1556715040596376e-05,
        "compression_defect_error": 2.414043899674756e-20,
        "loss_covariance_min_eigenvalue": 1.102900874021264e-11,
        "moment_error": 1.6653345369377348e-16
      }
    ]
  },
  {
    "N": 240,
    "conductors": 149,
    "epsilon": 0.005353392610074947,
    "blocks": [
      {
        "M": 16,
        "H": 1,
        "block_sum": 1.8934898069036616e-05,
        "raw_abel": 1.89348980690365e-05,
        "dispersion": -1.1405827061018908e-19,
        "delta_B": 5.466910858211205e-07,
        "delta_0": 2.186764343284482e-06,
        "block_bound": 0.0018644436984660447,
        "M_delta_B": 8.747057373137927e-06,
        "captured_B": 1.030929465035409e-05,
        "compression_defect_error": 5.823351512373315e-21,
        "loss_covariance_min_eigenvalue": 1.954997966330493e-06,
        "moment_error": 1.0180658399638887e-16
      },
      {
        "M": 32,
        "H": 3,
        "block_sum": 5.895766829410624e-05,
        "raw_abel": 7.109448780314279e-05,
        "dispersion": 1.2136819509036553e-05,
        "delta_B": 2.3987722462872925e-07,
        "delta_0": 1.3029217628462425e-06,
        "block_bound": 0.0032476054776508275,
        "M_delta_B": 7.676071188119336e-06,
        "captured_B": 1.2132146877769746e-05,
        "compression_defect_error": 8.099752558119247e-21,
        "loss_covariance_min_eigenvalue": 8.497530737459644e-09,
        "moment_error": 1.0104764247564901e-16
      },
      {
        "M": 64,
        "H": 6,
        "block_sum": 0.002497520043486265,
        "raw_abel": 0.0035855576251799057,
        "dispersion": 0.0010880375816936403,
        "delta_B": 1.995346813760558e-06,
        "delta_0": 6.884978150715874e-05,
        "block_bound": 0.10840353475877812,
        "M_delta_B": 0.00012770219608067572,
        "captured_B": 1.5694477352971552e-05,
        "compression_defect_error": 2.964615315390051e-21,
        "loss_covariance_min_eigenvalue": 1.2660549639256774e-10,
        "moment_error": 3.41740524767431e-16
      },
      {
        "M": 128,
        "H": 11,
        "block_sum": 0.01601818422837062,
        "raw_abel": 0.02198836253024488,
        "dispersion": 0.005970178301874263,
        "delta_B": 2.2893057272584657e-06,
        "delta_0": 0.00011032662446663238,
        "block_bound": 0.4949928107181986,
        "M_delta_B": 0.0002930311330890836,
        "captured_B": 1.6792881653772488e-05,
        "compression_defect_error": 1.2705494208814505e-21,
        "loss_covariance_min_eigenvalue": 4.50540041707535e-11,
        "moment_error": 4.193694003173931e-16
      }
    ],
    "aligned_site": {
      "n": 221,
      "ranges": [
        {
          "lo": 1,
          "hi": 1,
          "value": -0.006379895556097261
        },
        {
          "lo": 2,
          "hi": 3,
          "value": -0.0014773221163101743
        },
        {
          "lo": 4,
          "hi": 7,
          "value": -0.01738282248364517
        },
        {
          "lo": 8,
          "hi": 15,
          "value": -0.012256073214257293
        },
        {
          "lo": 16,
          "hi": 31,
          "value": -0.007992612420434045
        },
        {
          "lo": 32,
          "hi": 63,
          "value": -0.002441793187031259
        },
        {
          "lo": 64,
          "hi": 127,
          "value": -0.0012247548683222544
        },
        {
          "lo": 128,
          "hi": 220,
          "value": -4.226689642617026e-05
        }
      ],
      "T": -0.04919754074252364,
      "W": 4.482143608149426,
      "J": 0.0006759481307744688,
      "D": 0.0006092985786790642,
      "D_over_WJ": 0.2011087776669389,
      "prefix_H": 110,
      "Schur_prefix": -0.7636121166977552,
      "direct_prefix": -0.7636121166977498,
      "Schur_error": 5.440092820663267e-15
    }
  }
]
```

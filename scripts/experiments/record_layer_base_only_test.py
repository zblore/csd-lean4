"""
Record layer (MD-1), Phase 1 — decisive test: does a BASE-ONLY preparation density
reproduce Born for N>=3, or is the many-to-one fibre of Sigma needed?

By unitary covariance any base-only prep is rho_psi(phi) = g(|<psi|phi>|^2), a single
g:[0,1]->R>=0. Born condition (context-fixed Fubini-Study/Voronoi regions Omega_i(M),
reduced by covariance to M = computational basis):
    E_{phi~mu_FS}[ g(|<psi|phi>|^2) * 1(argmax_j |phi_j|^2 = i) ] = |psi_i|^2   for all psi,i.
Linear in g -> non-negative least-squares feasibility (Monte-Carlo on CP^{d-1}).

Diagnostic: r_unc (signed lstsq) is the noise floor; r_nn (g>=0) vs r_unc decides.
  qubit d=2 (base-only KNOWN to work): r_nn ~ noise  -> validates the test.
  qutrit d=3: r_nn plateaus ~10x noise, stable under more samples -> base-only FAILS -> fibre needed.
NOTE: min(g_unc)<0 is a RED HERRING (lstsq returns min-norm soln; negative even when a
non-negative one exists, as the qubit shows). Rely on r_nn, not min(g).

Result (2026-07-25, seed 0): OUTCOME B for FS-Voronoi. See specs/record-layer-plan.md §3.
Requires numpy, scipy.
"""
import numpy as np
from scipy.optimize import nnls

def run(d, Ns, K, Mpsi, seed=0):
    rng = np.random.default_rng(seed)
    Z = rng.standard_normal((Ns,d)) + 1j*rng.standard_normal((Ns,d))
    Z /= np.linalg.norm(Z,axis=1,keepdims=True)
    argmax = np.argmax(np.abs(Z)**2, axis=1)          # comp-basis Voronoi cell
    edges = np.linspace(0,1,K+1)
    PSI = rng.standard_normal((Mpsi,d)) + 1j*rng.standard_normal((Mpsi,d))
    PSI /= np.linalg.norm(PSI,axis=1,keepdims=True)
    A=[]; b=[]
    for t in range(Mpsi):
        psi = PSI[t]; x = np.abs(Z@psi.conj())**2
        bi = np.clip(np.searchsorted(edges,x,side='right')-1, 0, K-1)
        for i in range(d):
            A.append(np.bincount(bi[argmax==i], minlength=K).astype(float)/Ns)
            b.append(abs(psi[i])**2)
    A=np.array(A); b=np.array(b)
    gu,*_ = np.linalg.lstsq(A,b,rcond=None); ru = np.linalg.norm(A@gu-b)/np.sqrt(len(b))
    gn,_ = nnls(A,b,maxiter=20000);          rn = np.linalg.norm(A@gn-b)/np.sqrt(len(b))
    return ru, rn

if __name__ == "__main__":
    print(" d  Ns        K   r_unc(signed=noise)  r_nn(g>=0)   verdict")
    for d in (2,3):
        for Ns in (400_000, 1_600_000):
            ru,rn = run(d,Ns,40,80)
            v = "base-only OK" if rn < 3*ru+1e-3 else "BASE-ONLY FAILS -> fibre"
            print(f" {d}  {Ns:>8}  40   {ru:.5f}             {rn:.5f}     {v}")

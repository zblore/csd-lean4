"""
Record layer (MD-1), Phase 2b' — the DYNAMICAL fibre model (first-passage race).

Measurement as a first-passage race on the fibre:
  Sigma = CP^{n-1} x F, base pinned to [psi]; fibre carries n clocks. Clock i runs at speed
  b_i and fires at time xi_i / b_i (xi_i ~ Exp(1)); outcome = first to fire.
  P(first = j) = b_j EXACTLY (competing-exponential-clocks / Gumbel-max).

Three CSD-native features (not injected noise):
  (1) DYNAMICAL: a race/first-passage flow, outcome = first jump (the corpus's de-isolation
      completion), not a static Gumbel sample.
  (2) The SQUARE is the KAHLER MOMENT MAP: speed b_i = |<e_i|psi>|^2 = momentMap([psi])_i, the
      torus T^n action z->|z_i|^2 (corpus momentMap_mk_eq_inner_sq). Verified below.
  (3) The exponential fibre measure is FORCED, not chosen: for iid linear clocks, first-to-fire
      = b_i holds iff waiting times are exponential (memoryless/Poisson) -> the quantum-jump form.

OPEN (the reconstruction step): derive the race (rates = moment map, exponential clocks) from a
genuine de-isolation interaction H_int(M) + typicality on the fibred Sigma. See
specs/record-layer-plan.md §3b. Requires numpy.
"""
import numpy as np
def race(b, Ns, rng):
    xi = rng.random((Ns,len(b)))          # uniform -> -log -> Exp(1) waiting seeds
    fire = -np.log(xi)/b[None,:]
    out = np.argmin(fire,axis=1)
    return np.array([np.mean(out==i) for i in range(len(b))])
if __name__=="__main__":
    rng=np.random.default_rng(3); d=3; Ns=2_000_000
    for t in range(3):
        Z=rng.standard_normal(d)+1j*rng.standard_normal(d); psi=Z/np.linalg.norm(Z)
        Q,_=np.linalg.qr(rng.standard_normal((d,d))+1j*rng.standard_normal((d,d)))
        b=np.abs(Q.conj().T@psi)**2                    # b_i = |<e_i|psi>|^2 = moment map
        f=race(b,Ns,rng)
        print(f"Born(moment map)={np.round(b,4)}  race-freq={np.round(f,4)}  max|err|={np.max(np.abs(f-b)):.4f}")

# Bohm, Nelson, and CSD — what the continuity equation gives, and what it does not

**Row:** [`BACKLOG.md`](BACKLOG.md) #46 (Foundations / Positioning; end goal *One QM, many
formulations* · *Reviewer-proofing*). Written 2026-09-28 with the Lean brick
[`Mathlib/Analysis/Calculus/SchrodingerCurrent.lean`](../CsdLean4/Mathlib/Analysis/Calculus/SchrodingerCurrent.lean).

## Why this row exists

A reader who has met Bohmian mechanics asks the obvious question: *CSD says there is one trajectory
and the wavefunction is not the ontology — how is that not Bohm?* The answer is short, but it is only
worth giving if the shared mathematics is actually in the corpus rather than asserted. This row put
the shared mathematics in: the continuity equation and the two readings of it that the two
single-trajectory formulations of quantum mechanics are built on.

## What is proved

In one dimension, units `ℏ = m = 1`, for any `ψ(t, x)` satisfying `i ∂_t ψ = −½ ∂²_x ψ + V ψ` at the
point in question with `V` real:

| Statement | Name |
|---|---|
| `∂_x J = Im(ψ̄ ∂²_x ψ)`, the current's divergence | `hasDerivAt_probCurrent` |
| `∂_t ρ = 2 Re(ψ̄ ∂_t ψ)`, the density's time derivative | `hasDerivAt_probDensity_time` |
| **`∂_t ρ + ∂_x J = 0`**, the continuity equation | ★★ `continuity_equation` |
| `J = R² ∂_x S` in polar form `ψ = R e^{iS}` | ★ `probCurrent_polar` |
| **`∂_t ρ + ∂_x(ρ v) = 0`** with `v = ∂_x S` — **Bohm's equivariance** | ★★ `continuity_polar` |
| `dρ/dt = −ρ ∂_x v` along a trajectory with `ẋ = v` — equivariance in Lagrangian form | ★★ `hasDerivAt_density_along_trajectory` |
| `ρ b = ρ v + ½ ∂_x ρ = ρ (v + ½ ∂_x log ρ)`, Nelson's flux and osmotic drift | `nelsonFlux`, `nelsonFlux_eq_mul_drift` |
| **`∂_t ρ = −∂_x(ρ b) + ½ ∂²_x ρ`** — the Fokker–Planck equation of Nelson's diffusion, solved by `\|ψ\|²` | ★★ `nelson_fokkerPlanck` |

The two formulations share one identity and differ only in how they read the flux: Bohm splits it as
`ρ v` and reads `v` as a velocity; Nelson splits it as `ρ(v + ½ ∂_x log ρ) − ½ ∂_x ρ` and reads the
first factor as a drift with a diffusion against it.

## What is not proved, and why

* **The diffusion process itself.** `nelson_fokkerPlanck` is the Fokker–Planck *equation*. Nelson's
  theorem — that a diffusion process with that drift has `|ψ|²` as its law at every time — needs
  stochastic differential equations, which Mathlib does not have at the pin. The row keeps that half
  unclaimed.
* **Bohmian trajectories exist.** The Lagrangian statement takes a trajectory as given. The flow of
  `v = ∂_x S` is singular at the nodes of `ψ`, and global existence is a genuine theorem (Berndl et
  al. 1995) that is not attempted.
* **One dimension only**, and the Schrödinger equation is a *hypothesis* at the point, not a solution
  produced by the corpus's semigroup (`Analysis/Semigroup/SchrodingerSchwartz.lean` gives the strong
  `L²` derivative; reading it pointwise is a regularity theorem).

## The contrast with CSD — the answer to the reviewer

Everything below is positioning, not a Lean claim.

1. **Where the trajectory lives.** Bohm's configuration `x(t)` lives in the configuration space of
   the system and is *guided* by `ψ`, which is a second ontological ingredient with its own
   (Schrödinger) law. Nelson's is a diffusion in the same space. CSD's single trajectory lives in
   `Σ`, and `ψ` is not part of the ontology: the sector's geometry is
   (`LF4/SectorManifold.lean`, `Instances/ProjectiveSpace*`), and the wavefunction enters as a label
   of an epistemic region, never as a guiding field.
2. **What the dynamics is.** Bohm's velocity field is read off `∇S/m` — the wavefunction's phase.
   CSD's isolated dynamics is the Hamiltonian flow of the sector's own symplectic structure
   (`hamiltonianFlow_sectorEnergy_schrodinger`, `LF4/ArenaSymplectic.lean`), with no guiding field to
   read.
3. **What selects an outcome.** Bohm: the initial configuration, sampled from `|ψ|²` by hypothesis
   (equivariance keeps it there — the theorem above). Nelson: the noise. CSD: the **record** — the
   ontic selection in `Σ` of which epistemic region the trajectory realises (`RecordLayer/`), with
   the Born weights *derived* as typicality volumes rather than postulated as a sampling hypothesis
   (`qubitBorn`, `fs_born_volume_ratio_N`).
4. **What equivariance is for.** In Bohm, equivariance is what makes the `|ψ|²` hypothesis
   consistent in time; the hypothesis itself is external. In CSD the analogous statement is that the
   ontic measure is invariant under the flow (Liouville, `Q29`), and the Born weights come out of the
   measure rather than being preserved after being assumed.
5. **Relaxation.** Valentini's route — a non-equilibrium density relaxing to `|ψ|²` — is the
   programme's own open row `R-019` (#18), and it is open in both settings for the same reason: it
   needs first-passage asymptotics, not a continuity equation.

## References

D. Bohm, *A suggested interpretation of the quantum theory in terms of "hidden" variables*,
Phys. Rev. 85 (1952) 166, §4; E. Nelson, *Derivation of the Schrödinger equation from Newtonian
mechanics*, Phys. Rev. 150 (1966) 1079; K. Berndl, D. Dürr, S. Goldstein, G. Peruzzi, N. Zanghì,
*On the global existence of Bohmian mechanics*, Comm. Math. Phys. 173 (1995) 647;
A. Valentini, *Signal-locality, uncertainty, and the subquantum H-theorem* (1991) — `R-019`.

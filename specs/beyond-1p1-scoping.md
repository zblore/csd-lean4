# Beyond 1+1 dimensions: scoping note (BACKLOG #289)

**Status:** SCOPED 2026-11-04 at the author's go, after a survey of the 1+1 line's modules
(`CV/DiracClockChain`, `DiracPacket`, `DiracPacketLimit`, `DiracMassless`; `RecordLayer/Dirac*`,
`FrameCovariance`, `ChainCone`, `SelectionOrder`, `CoupledDetector`, `CoupledLiouville`) and of the
pinned Mathlib. Claims about the corpus were read from theorem types and definitions. Nothing here
is built. #289 is split into rows #292–#301 below; the author picks.

## 1. The question

[`records-to-spacetime-status.md`](records-to-spacetime-status.md) lists what the record layer
proves in 1+1: observers recover Lorentz kinematics from their records with explicit errors, no
record statistic singles out a frame, spacelike write order is invisible, entangled pairs carry a
hidden slicing, one click, detectors that push. #289 asks for the same statements with `d` space
dimensions, `d = 2, 3`. What does a second space dimension add that the line has not met?

## 2. What the survey found

1. **Everything below the kinematics is typed to one dimension.** The chain is `diracHam : Matrix
   (ZMod L × Fin 2) (ZMod L × Fin 2) ℂ`; the packets, translation phase, detectors and record
   windows (`encounter_record_window`) take states on `(ZMod L × Fin 2) × Fin 2`; `lorentzBoost` and
   `onticCell` take events in `ℝ × ℝ`. About 19,000 lines of modules mention `ZMod L` directly.
2. **Fermion doubling is not a wall for the record kinematics.** The 1+1 chain already has a
   doubler: `modeS = 2J sin k` vanishes at `k = π` as well as `k = 0`. The line never meets it,
   because packets are windowed at physical momenta `|p| ≤ P` while the doubler sits at `π/a → ∞`,
   and the free evolution conserves momentum. In `d` dimensions the `2^d − 1` doublers sit at the
   zone's corners, equally far away. Doubling matters for interacting matter that can transfer
   momentum near `π/a`, and for chirality (Nielsen–Ninomiya). Neither is used by #292–#298. Removing
   doublers with a Wilson term costs accuracy: it adds about `r c a p²/2` to the energy in physical
   units, an `O(a)` error where the naive chain's is `O(a²)`. Hence #299 is optional.
3. **Mathlib has no Lorentz group** (none at the pinned Mathlib), and Physlib is an export target,
   not a dependency. A minimal one is owed: boosts along a unit vector on `ℝ × EuclideanSpace ℝ (Fin
   d)`, the Minkowski form, proper time.
4. **Covariance needs no Wigner rotation.** Every record the line uses is a proper-time reading at
   an encounter, which is a Lorentz scalar. A chart computed from such readings is frame independent
   to the readings' errors, exactly as `record_statistic_covariant` argues in 1+1. Thomas–Wigner
   rotation changes how two frames' axes compare, not what any record reads.
5. **The clock results should transfer by the norm.** The `d`-dimensional dispersion is `E = √(μ² +
   |s|²)` with `s_i = 2J sin k_i`, which is `dispE μ |s|`. `abs_clockRate_div_sub_le` and `vRel` are
   stated in `dispE μ s`. Expected, not checked: they apply with `s := |s|`.
6. **One genuinely new physical fact: the lattice picks out directions.** For a massless messenger,
   `|s|² = (c/a)² Σ_i sin²(a p n_i) = c²p²(1 − (ap)²/3 · Σ_i n_i⁴ + …)`, so its speed along a unit
   direction `n` depends on `n` at order `(ap)²` (`Σ n_i⁴` is `1` on an axis, `1/d` on the
   diagonal). In 1+1 the lattice showed only as a frame (`lattice_frame_residue`); in `d ≥ 2` it
   also shows as preferred directions, at the same order. This is the rotational residue #289 named.
7. **The numerical arenas need not be redone.** The 1+1 line has both a numerical instance
   (`dirac_two_charts`, ~23%) and a symbolic scaling theorem (`radar_lorentz_scaling`). The scaling
   theorem consumes three chain facts: messenger speed, clock dilation and record windows. Carrying
   those three facts to `d` dimensions carries the theorem. A numerical instance in `d ≥ 2` is #300,
   optional.
8. **The spatial chart needs more than one observer.** Radar from one observer gives the distance
   `(r − e)/2`, not the direction. The standard construction is trilateration by `d + 1` co-moving
   reference observers in general position, each measuring its distance by radar.

## 3. The split

Core (#292–#298), in dependency order. Every one is stuck only on its price.

1. **#292 Minkowski kinematics in `d+1`** (M). Boosts along unit vectors, the Minkowski form
   preserved, proper time invariant, relative speed from four-velocities; a boost along the
   separation reverses spacelike order, and none reverses timelike order.
2. **#293 The spatial radar chart** (M–L; needs #292). Trilateration by `d+1` co-moving observers is
   exact; a moving group's chart is a Lorentz transformation of a resting group's; the residual is
   linear in the reading errors with a geometry constant; the `d+1` `radar_lorentz_exact` and
   `radar_lorentz_scaling`.
3. **#294 The lattice Dirac Hamiltonian in `d` dimensions** (M). For any Clifford family (`α_i`, `β`
   Hermitian, anticommuting, squaring to one): Hermitian, nearest-neighbour, plane-wave modes `(H(k)
   + E) e₀` exact eigenvectors, dispersion `dispE μ |s|`, clock dilation; instances `d = 2` (Pauli,
   two components) and `d = 3` (four components).
4. **#295 The anisotropy residue** (M; needs #294). Group velocity as a vector, `|v_g| ≤ c`, the
   massless speed along `n` within `O((ap)²)` of `c` with the `Σ n_i⁴` term explicit, and a rotated
   preparation's velocities within `O(a²)` of the rotated velocities (the rotational
   `lattice_frame_residue`).
5. **#296 Packets in `d` dimensions** (L; needs #294, #295). One translation phase per axis, each
   drifting at the group velocity's component; normalisation, localisation independent of `L`, the
   scaled and massless limits (`dirac_packet_limit`, `dirac_massless_limit`).
6. **#297 Records and the cone on any nearest-neighbour lattice** (M; needs #294). Generalise the
   detector, record-window and `ChainCone` modules from `ZMod L × Fin 2` to any finite site set with
   a nearest-neighbour graph, then instantiate on the `d`-dimensional torus.
7. **#298 The `d+1` capstone** (M; needs #292–#297). The chain's records give a trilateration chart
   within `ε` of a Lorentz transformation below a resolution (`radar_lorentz_scaling`);
   `record_statistic_covariant`, `chain_record_kick_order` and `spacelike_boost_changes_outcomes` in
   `d+1`.

Optional, for the author to decide:

8. **#299 Doublers removed** (Wilson or staggered) with the error that costs (M). Optional by §2.2:
   the record kinematics do not use it.
9. **#300 A numerical arena in `2+1`**, the analogue of `dirac_two_charts` (XL). Optional by §2.7:
   the scaling theorem does not need it.
10. **#301 The coupled detector and its Liouville theorem in `d` dimensions** (M): determinant one
    by Jacobi's formula, the field being trace-free. Optional: the status note uses 1+1's #251 and
    #291.

The core prices sum to about the XL #289 carried, now split into pieces that are each stuck only on
their size.

## 4. Recommendation

Start with #292 → #293. They are symbolic, need no lattice, and deliver what #289 named: the `3+1`
`radar_lorentz_exact`. Then #294 → #295, which yields the one new physical fact (§2.6), the
lattice's preferred directions at `O((ap)²)`. Do #296 and #297 next, and #298 last.

## 5. What this does not reach

* **Spin and rotations of the device.** The internal clock is two levels and carries no spin. Spin
  under rotations, and the device's orientation as a record, are not scoped.
* **Gravity, curved charts, and accelerated observer groups.** The reference observers are inertial
  and co-moving.
* **Generation.** As in 1+1, detector laws are stated where not generated, and no `H_int` generates
  the record cells (R-016).

References: `specs/BACKLOG.md` #289, #292–#301, #38, #39, ~~#285~~, ~~#287~~;
[`records-to-spacetime-status.md`](records-to-spacetime-status.md);
[`records-to-spacetime-scoping.md`](records-to-spacetime-scoping.md); `CV/DiracClockChain.lean`
(`diracHam`, `modeS`, `dispE`); `RecordLayer/FrameCovariance.lean` (`lattice_frame_residue`,
`record_statistic_covariant`); `RecordLayer/DiracTwoCharts.lean` (`radar_lorentz_exact`,
`radar_lorentz_scaling`); H. B. Nielsen, M. Ninomiya, Nucl. Phys. B 185 (1981) 20; K. G. Wilson,
Erice lectures 1975 (Plenum 1977); B. Coll, J. M. Pozo, Class. Quantum Grav. 23 (2006) 7395
(relativistic positioning); `specs/future-work.md`.

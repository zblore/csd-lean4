# EMPIRICAL.md — index of the empirical validation suite

**This is the reader's jumping-in point for every empirical test in the corpus.**
Each row names the Lean file, the headline theorem(s), the claim, and the original
physics source. Every theorem listed here is **foundational-triple-only**
(`propext, Classical.choice, Quot.sound`) and regression-pinned in
[`CsdLean4/Tests/AxiomAudit.lean`](CsdLean4/Tests/AxiomAudit.lean) via `#guard_msgs`
against `#print axioms`. Build with `lake build` (library) and `lake build CsdLeanTests`
(the pins).

The suite splits into the two branches described in
[`README.md`](README.md) (Empirical section) and
[`specs/qm-empirical-tests.md`](specs/qm-empirical-tests.md) (the roadmap and per-item
status). For the axiom posture and the two-strata (operational vs ontic) reading, see
[`AXIOMS.md`](AXIOMS.md).

## The two layers

- **QM-validity layer** (`CsdLean4/Empirical/QM/`): pure theorems about Hilbert spaces,
  vectors, and operators. Inputs are abstract (`EuclideanSpace ℂ (Fin n)`, Pauli
  matrices, isometries); proofs are linear algebra and inner-product geometry. Answers
  "does the standard QM formalisation produce the predicted number?"
- **CSD-ontic layer** (`CsdLean4/Empirical/CSD/`): the same numerical predictions read
  through the ontic substrate. Two sub-kinds:
  - **Bridge transports**: each QM-validity statement carried through a
    `CSDBridge.Context D` bundle (the LF2 `SectorData` + measure-bridge data), providing
    the structural slot for the ontic interpretation.
  - **Volume-frequency series**: the Born number is *derived*, not transported, as a
    Fubini-Study typicality volume on the ontic `Σ`. These are carving-free and
    Gleason-free (no appeal to `busch_effect_gleason`). Honest residue: in every concrete
    instance the flow is currently the identity, so no measurement dynamics is yet
    exercised; the Born value is derived from the posited sector geometry on `Σ`, which is
    the standing assumption these results rest on (see `README.md` headline and `AXIOMS.md`).

---

## QM-validity branch (`CsdLean4/Empirical/QM/`)

| Test | File | Headline theorem(s) | Claim | Source |
|---|---|---|---|---|
| Bell / CHSH | `Bell.lean` | `chsh_singlet_tsirelson_bound`, `chsh_qm_tsirelson_bound`, `chsh_classical_bound_violated`, `chsh_inner_bound` | CHSH on the singlet attains the Tsirelson value `2√2`; the classical bound `2` is violated; Khalfin-Tsirelson upper bound `≤ 2√2` for any four unit vectors (and its QM form) | Bell 1964; CHSH 1969; Tsirelson 1980; Aspect 1982 |
| No-signalling | `Bell.lean` | `no_signalling_alice`, `no_signalling_bob`, `singlet_marginal_alice`, `singlet_marginal_bob` | Each wing's marginal is independent of the other's setting; singlet marginals are `1/2` | Aspect 1982; loophole-free Hensen/Giustina/Shalm 2015 |
| No-cloning | `NoCloning.lean` | `no_cloning_two_state`, `no_universal_cloner_of_witness` | An isometry cloning two states forces overlap `∈ {0,1}`; no universal cloner exists | Wootters-Zurek 1982; Dieks 1982 |
| No-deleting | `NoDeleting.lean` | `no_deleting_two_state`, `no_universal_deleter_of_witness` | Dual of no-cloning: deleting forces overlap `∈ {0,1}`; no universal deleter | Pati-Braunstein 2000 |
| No-broadcasting | `NoBroadcasting.lean` | `pure_marginal_confinement` | A bipartite PSD operator with a pure first-factor marginal is confined to that pure sector (the squeeze behind "broadcasting a pure state = cloning it") | Barnum-Caves-Fuchs-Jozsa-Schumacher 1996 |
| No-communication | `NoCommunication.lean` | `no_communication`, `no_communication_reduced`, `bob_expectation_invariant` | Alice's local unitary leaves every Bob-side expectation, and Bob's reduced state, invariant | Ghirardi-Rimini-Weber 1980; Eberhard 1978 |
| Robertson uncertainty | `Uncertainty.lean` | `robertson_uncertainty`, `robertson_core` | `Var(A)·Var(B) ≥ ¼\|⟨[A,B]⟩\|²` for symmetric operators | Robertson 1929 |
| Stern-Gerlach | `SternGerlach.lean` | `born_zPlus_zPlus`, `born_xPlus_zPlus`, `born_z_basis_complete`, `born_x_basis_complete` | Spin Born values on `\|+ẑ⟩`: `P(↑\|ẑ)=1`, `P(↑\|x̂)=1/2`; basis completeness | Stern-Gerlach 1922 |
| Malus's law | `Malus.lean` | `malus_law`, `malus_basis_complete`, `malus_pi_div_two` | `P(+_z\|θ) = cos²(θ/2)`; recovers the two SG values at `θ=0, π/2` | Malus 1809 (spin-1/2 form) |
| Hardy non-locality | `Hardy.lean` | `no_lhv_hardy`, `HardyQM.exists_hardy_realisation`, `HardyQMMax.hardyMax_probability_eq` | Hardy's ladder: a paradoxical outcome with no local-hidden-variable assignment; the optimal `≈ 9%` probability `(5√5−11)/2` | Hardy 1992, 1993 |
| Unambiguous discrimination | `USD.lean` | `usd_unambiguous_1`, `usd_unambiguous_2`, `usd_success`, `usd_complete`, `usdPOVM` | Zero-error discrimination of two non-orthogonal states via a genuine non-projective POVM; success `1−s`; completeness `E₁+E₂+E?=I` | Ivanovic 1987; Dieks 1988; Peres 1988 |
| GHZ paradox | `Multipartite/GHZ.lean` | `ghz_expectation_xxx`, `ghz_expectation_xyy`/`yxy`/`yyx`, `no_lhv_assignment_for_ghz` | All-or-nothing 3-qubit correlations `⟨XXX⟩=+1`, `⟨XYY⟩=⟨YXY⟩=⟨YYX⟩=−1`, with no consistent LHV assignment | Greenberger-Horne-Zeilinger 1989; Mermin 1990; Pan et al. 2000 |
| Kochen-Specker | `Contextuality/KS18.lean` | `no_value_assignment_18_9`, `ks_no_value_assignment_cabello18`, `cabello_pairwise_orthogonal_in_basis` | No non-contextual value assignment on the Cabello 18-vector configuration in `ℝ⁴` | Kochen-Specker 1967; Cabello 1996 |
| Mermin-Peres square | `Contextuality/MerminPeres.lean` | `no_lhv_mermin_peres`, `mermin_peres_R0`..`C2` | The magic-square observables have no consistent local value assignment | Mermin 1990; Peres 1990 |
| Superdense coding | `Resources/SuperdenseCoding.lean` | `encode_I`/`X`/`Z`/`XZ`, `bell_basis_orthonormal` | The four local-Pauli images of `\|Φ⁺⟩` are the four orthonormal Bell states | Bennett-Wiesner 1992 |
| Teleportation | `Resources/Teleportation.lean` | `teleState_factorises`, `teleportation_bell_expansion`, `teleportation_branch_recovers_input` | The four corrections `{I,Z,X,ZX}` recover the input per Bell-measurement branch (branch-conditional QM-validity layer) | Bennett et al. 1993 |
| Quantum money | `Crypto/QuantumMoney.lean` | `quantum_money_unforgeable`, `wiesner_nonorthogonal` | Forgery would clone non-orthogonal Wiesner states, contradicting no-cloning | Wiesner 1983 |
| E91 device-independent | `Crypto/E91.lean` | `lhvCHSH_abs_le_two`, `lhvCHSH_lt_tsirelson`, `e91_no_lhv_reproduces_singlet` | A measure-theoretic LHV model obeys the CHSH bound `\|S\|≤2`; the singlet attains `2√2`, so no LHV reproduces it (eavesdropper-detectable) | Ekert 1991; CHSH 1969 |
| Gate library | `Gates/{SingleQubit,TwoQubit,MultiQubit,BellPrep}.lean` | `qmH_mul_self`, `qmS_sq`, `qmT_sq`, `qmCNOT_mul_self`, `qmSWAP_mul_self`, `qmCZ_mul_self`, `qmToffoli_mul_self`, `qmFredkin_mul_self`, `qmBellPrep_yields_phiplus` | Hadamard/phase/Pauli involutions and orders; CNOT/SWAP/CZ/Toffoli/Fredkin self-inverse; Bell preparation yields `\|Φ⁺⟩` | Standard |
| QEC: 3-qubit bit-flip code | `QEC/ThreeQubit.lean` | `three_qubit_corrects_single_bitflip`, `syndrome_X1`/`X2`/`X3`, `stab_*_fixes_logical` | `\|ψ⟩↦a\|000⟩+b\|111⟩` corrects any single `X` error: stabilisers `Z₁Z₂,Z₂Z₃` fix the codespace, the four errors give distinct syndromes `(±,±)`, and each `X` is self-inverse (recovery). The first QEC theorem. | Shor 1995 |
| QEC: 3-qubit phase-flip code | `QEC/PhaseFlip.lean` | `three_qubit_corrects_single_phaseflip`, `syndromePF_*`, `stab_*_fixes_logicalPF` | The Hadamard dual: `\|ψ⟩↦a\|+++⟩+b\|---⟩` corrects any single `Z` error (stabilisers `X₁X₂,X₂X₃`, errors `{I,Z₁,Z₂,Z₃}`, same syndrome/recovery structure). | Shor 1995 |

Namespace note: the earliest files use `CSD.Empirical.<Topic>` (Bell, NoCloning, NoDeleting,
Uncertainty, SternGerlach, Hardy, GHZ, KochenSpecker, MerminPeres, QuantumMoney); later
files use `CSD.Empirical.QM.<Topic>` (NoBroadcasting, NoCommunication, USD, E91,
Resources/*, Gates/*). The fully-qualified names above (taken from the AxiomAudit pins)
are canonical.

---

## CSD-ontic branch (`CsdLean4/Empirical/CSD/`)

**Coverage relative to the QM branch.** Every QM-validity test now has a CSD-branch
counterpart (a bridge transport, a derived volume reading, or both). USD has no bridge
transport but is covered by `USDVolume.lean` (the derived volume reading). The trine and
SIC POVMs exist only in the CSD branch (their POVM content lives inside the volume files),
with no separate `QM/` file. The bridge transports reduce to their QM-side theorem by
field extraction; the genuinely-ontic realisability is the disclosed LF4 obligation in
[`BRIDGE-OBLIGATIONS.md`](BRIDGE-OBLIGATIONS.md) (E91 carries no such obligation, by
design — see its row).

### Bridge transports (QM-validity statements carried through `CSDBridge.Context D`)

| Test | File | Headline theorem | Note |
|---|---|---|---|
| Bell singlet chain | `Bell.lean` | `bell_singlet_frequency_convergence` | Singlet kernel `(1 − st a·b)/4` via the LF1↔LF2↔LF3 chain |
| No-cloning bundle | `NoCloning.lean` | `no_csd_cloning_bundle` | Ontic-bundle reading of no-cloning |
| No-deleting bundle | `NoDeleting.lean` | `no_csd_deleting_bundle` | |
| No-broadcasting | `NoBroadcasting.lean` | `csd_no_broadcasting` | Pure-marginal confinement on the CSD substrate |
| No-communication | `NoCommunication.lean` | `csd_no_communication` | Bob's expectation invariant under Alice's local unitary |
| Teleportation | `Resources/Teleportation.lean` | `csd_teleportation_branch_recovers_input` | Branch-conditional input recovery (LF5 for collapse) |
| E91 security | `Crypto/E91.lean` | `csd_lhv_chsh_bound` | Any local-realist reading of the source obeys `\|S\|≤2`; CSD reaches `2√2` (no LF4 obligation) |
| Robertson | `Uncertainty.lean` | `csd_robertson_uncertainty` | |
| Stern-Gerlach | `SternGerlach.lean` | `csd_sg_born_xPlus_zPlus`, `csd_sg_born_x_basis_complete` | Transport tag (cf. the derived form below) |
| Superdense coding | `Resources/SuperdenseCoding.lean` | `csd_sdc_encode_X`, `csd_sdc_bell_basis_orthonormal` | |
| Quantum money | `Crypto/QuantumMoney.lean` | `no_csd_quantum_money_forger` | |
| Mermin-Peres | `Contextuality/MerminPeres.lean` | `no_csd_mermin_peres_assignment` | |
| Hardy | `Hardy.lean` | `no_csd_hardy_assignment` | |
| Kochen-Specker | `Contextuality/KS18.lean` | `no_csd_ks_assignment_bundle` | |
| GHZ | `Multipartite/GHZ.lean` | `no_csd_ghz_lhv_bundle` | |
| Gates | `Gates/{Framework,SingleQubit,TwoQubit,MultiQubit,BellPrep}.lean` | (transport) | Bridge readings of the QM gate library |
| Bridge scaffolding | `Framework.lean` | `CSDBridge.Context` | The bundle type itself (infrastructure, not a test) |

Several bundles carry load-bearing, externally-supplied realisability fields (the ledger
is [`BRIDGE-OBLIGATIONS.md`](BRIDGE-OBLIGATIONS.md)).

### Volume-frequency series (Born numbers *derived* as Fubini-Study volumes)

Carving-free and Gleason-free: each Born value is realised as a Fubini-Study typicality
volume on the ontic `Σ`, and empirical frequencies (LF1 strong law) converge to it.
The first five are projective qubit measurements; the next three are non-projective qubit
POVMs via canonical Naimark dilation; the last is the first **non-qubit (`N = 3`)** entry,
a non-projective qutrit POVM.

| Test | File | Headline theorem(s) | Derived value |
|---|---|---|---|
| Stern-Gerlach | `SternGerlachVolume.lean` | `csd_sg_volume_certain`, `csd_sg_volume_half` | `P(↑\|ẑ)→1`, `P(↑\|x̂)→1/2` |
| Malus's law | `MalusVolume.lean` | `csd_malus_law` | `P(↑\|θ)→cos²(θ/2)` |
| Bell singlet (joint) | `BellVolume.lean` | `bell_singlet_born_frequency_volume`, `bell_singlet_volume_correlation` | joint weights `(1∓cos θ)/4` on `ℂℙ³`; `⟨σ_a σ_b⟩=−cos θ` |
| GHZ | `GHZVolume.lean` | `ghz_born_frequency_volume`, `ghz_volume_correlation` | GHZ stabiliser Born weights and correlations |
| Hardy | `HardyVolume.lean` | `hardy_max_born_frequency_volume`, `hardy_max_volume_probability` | the optimal Hardy probability `(5√5−11)/2` |
| Trine POVM | `TrineVolume.lean` | `trine_complete`, `trine_weight_eq`, `trine_born_frequency_volume` | `pₖ=(2/3)‖⟨ψₖ,ψ⟩‖²` on dilated `ℂℙ⁵` (first non-projective entry) |
| USD POVM | `USDVolume.lean` | `usd_weight_e1`, `usd_weight_e2`, `usd_born_frequency_volume` | conclusive weights `a‖⟨ψₖ^⊥,ψ⟩‖²` on dilated `ℂℙ⁵` |
| SIC POVM | `SICVolume.lean` | `sic_outer_sum`, `sic_inner_normSq`, `sic_weight_eq`, `sic_born_frequency_volume` | tetrahedral `pₖ=(1/2)‖⟨ψₖ,ψ⟩‖²`, equiangular `\|⟨ψⱼ,ψₖ⟩\|²=1/3`, on dilated `ℂℙ⁷` |
| Unsharp qutrit POVM (**N=3**) | `QutritPOVMVolume.lean` | `noisy_complete`, `noisy_weight_eq`, `noisy_born_frequency_volume` | `Eₖ=(1−ε)\|k⟩⟨k\|+(ε/3)I₃`; `pₖ=(1−ε)‖⟨k,ψ⟩‖²+ε/3`, on dilated `ℂℙ⁸` (first non-qubit entry) |
| d=3 SIC / Hesse POVM (**N=3**) | `SIC3Volume.lean` | `sic3_complete`, `sic3_inner_normSq`, `sic3_weight_eq`, `sic3_born_frequency_volume` | 9 Weyl–Heisenberg states `Eₖ=(1/3)\|ψₖ⟩⟨ψₖ\|`, equiangular `\|⟨ψⱼ,ψₖ⟩\|²=1/4`; `pₖ=(1/3)‖⟨ψₖ,ψ⟩‖²`, on dilated `ℂℙ²⁶` (first *symmetric* non-qubit entry) |
| d=3 complete-MUB POVM (**N=3**) | `MUB3Volume.lean` | `mub3_complete`, `mub3_unbiased`, `mub3_weight_eq`, `mub3_born_frequency_volume` | 4 mutually unbiased bases (12 vectors) `Eₖ=(1/4)\|vₖ⟩⟨vₖ\|`, unbiased `\|⟨v,w⟩\|²=1/3` across bases; `pₖ=(1/4)‖⟨vₖ,ψ⟩‖²`, on dilated `ℂℙ³⁵` |

The trine, USD, and SIC entries span the canonical minimal qubit POVM family: minimal
symmetric (trine), unambiguous discrimination (USD), and symmetric informationally
complete (SIC). The unsharp and Hesse-SIC qutrit POVMs are the first entries exercising
the machinery past the qubit (`N = 3`, dilated `ℂℙ⁸` and `ℂℙ²⁶`); the d=3 SIC is the
genuine symmetric informationally-complete qutrit measurement (the Weyl–Heisenberg orbit
of the Hesse fiducial, equiangular at `1/(d+1) = 1/4`). The general (non-projective) ontic
Born = Kähler-volume machinery they instantiate lives in `CsdLean4/LF4/POVM*.lean` (see
`README.md` LF4 POVM row).

---

## See also

- [`README.md`](README.md) — authoritative status overview (layer tables, axiom posture).
- [`specs/qm-empirical-tests.md`](specs/qm-empirical-tests.md) — the roadmap, per-item
  status tags, and the planned-but-not-yet-done items (BB84/B92, weak-measurement
  paradoxes, algorithms).
- [`AXIOMS.md`](AXIOMS.md) — the two standing axioms and the operational/ontic two-strata
  reading.
- [`CLAUDE.md`](CLAUDE.md) — architecture and module-chain guide.

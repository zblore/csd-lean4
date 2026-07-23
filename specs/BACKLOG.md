# BACKLOG — the single canonical open-items list

> **This is the ONE place open work lives.** Do not add TODO / future-work / "next
> steps" / open items to any other `.md`. The per-phase plans (`LF*-plan`, `shor-plan`,
> `povm-plan`, …) are **historical execution logs** — frozen; read them for how a
> completed layer was built, not for what is open. The status/claims docs
> (`reconstruction-status`, `connectivity-manifest`, `PLACEHOLDERS`, `AXIOMS`,
> `BRIDGE-OBLIGATIONS`) describe *what is proved*; they point here for *what is next*.
>
> Effort key: **S** hrs–day · **M** days–2wk · **L** weeks · **XL** Mathlib-scale.
> Last updated 2026-07-21.

---

## M — genuinely closeable, real content

| Item | Status / what's needed | Former source |
|---|---|---|
| ~~**Choi converse** (PSD Choi ⇒ Kraus)~~ | **DONE 2026-07-19** (`LF2/ChoiConverse.lean`). `choi_iff_posSemidef`: a matrix on `Fin M × Fin N` is a Kraus family's Choi matrix **iff** PSD. The feared "vectorization iso" was definitional (the Choi index *is* a product), so the content was the spectral `Kᵢ=√λᵢ·unvec(eᵢ)` reconstruction (`choiOfKraus_krausOfChoi` + `IsHermitian.eq_eigen_outer`). Foundational triple. | `qi-qec-roadmap.md` |
| ~~**Gisin's theorem** (pure entangled ⇒ CHSH violation)~~ | **DONE 2026-07-19** (`LF6/GisinTheorem.lean`). `gisin_chsh_violation`: every entangled `Ψ(c,s)=c\|00⟩+s\|11⟩` (`0<c,0<s`) violates CHSH — the physical `⟨Ψ\|σ·a⊗σ·b\|Ψ⟩` combination `> 2`. Built directly on the existing `psQubit_pauli_correlation`; the feared "general Schmidt decomposition" wasn't needed (the real-Schmidt two-qubit state + its correlation were already in `PartialSchmidtCorrelation.lean`). Trig-free `c,s`-dependent witness giving `2√(1+(2cs)²)`. Closes LF6-6. Foundational triple. | `lf6-plan.md` (LF6-8) |
| ~~**Busch–Gleason** (effect-Gleason, finite-dim)~~ | **DONE 2026-07-21** — see the "Discharge `busch_effect_gleason`" row below. Axiom deleted; corpus now imports **zero** axioms. | `AXIOMS.md §2.2` |
| ~~**Separate the ecdsa.fail track**~~ | **DONE 2026-07-20** — extracted to its own repository and removed from this one (see the section below). | `ecdsafail-two-track.md` |

## L — weeks

| Item | Status / what's needed | Former source |
|---|---|---|
| **Operator convexity → unconditional SSA** | **Parked on an instance wall.** Detailed ladder (steps 0→7) in `operator-convexity-plan.md`; the immediate blocker is step 0 (ℂ-smul Löwner monotonicity + spectrum-restricted `affine_output`; the `PartialOrder ℂ` cascade). Endpoint: discharge `hDPI` in `strong_subadditivity_of_relEntropy_monotone`. | `operator-convexity-plan.md` |
| **GKSL / Lindblad open-systems tier** (LF6-9) | **Generator tier DONE 2026-07-20** (`LF6/LindbladGenerator.lean`): the general GKSL generator `ℒ(ρ)=−i[H,ρ]+Σₖ(LₖρLₖ†−½{Lₖ†Lₖ,ρ})` + trace-annihilation (`lindbladGenerator_trace`), Hermiticity-preservation, CP of the jump part (`lindblad_dissipation_posSemidef`, reusing the Choi/Kraus witness); dephasing shown to **be** a GKSL instance (`dephasingGenerator_eq_lindblad`) and to **solve** its master equation (`dephasingChannel_master_equation`). **Remaining (genuinely Mathlib-scale):** CP of the *exponentiated* `e^{tℒ}` for arbitrary generators (matrix-exp positivity, L2-operator norm scope). Unblocks LF6-2 full + Metrology A4. | `lf6-plan.md` |
| **§14 observable correspondence — general-N, all self-adjoint** | **DONE 2026-07-22** (`LF4/ObservableCorrespondenceN.lean`). `observable_correspondence_diagonal`: for any `N` and any real eigenvalue vector `lam`, `⟨ψ, diagonal(lam·) ψ⟩ = ∑ₖ lam k · vol(bornRegionN ψ k)` — the Hilbert expectation of a diagonal observable is the eigenvalue-weighted sum of its ontic Born-region Fubini–Study volumes (`diag_expectation` Hilbert side + `fsMeasure_bornRegionN` unifying `fs_born_volume_ratio_N`/`_apex` via `Fin.lastCases`). Foundational triple, AxiomAudit-pinned, carving-free, Gleason-free. Generalises the single-qubit `sg_observable_correspondence` to all N + all eigenvalues. Both the pointwise-volume form (`observable_correspondence_diagonal`) and the **canonical integral form** (`observable_correspondence_diagonal_integral`: `⟨ψ,Aψ⟩ = ∫ A_ontic dμ` with `A_ontic = ∑ₖ lam k·𝟙_{Rₖ}` an explicit measurable Σ-function, `bornRegionN_measurableSet`) are landed. **Now extended to ALL self-adjoint observables** (`hermitian_observable_correspondence` / `_integral`): via the spectral theorem `A = U·diag(λ)·Uᴴ`, `⟨ψ,Aψ⟩ = ∑ₖ λₖ·vol(bornRegionN φ k)` where `φ = Uᴴψ` is the state transported by the spectral unitary (`hermitian_expectation_transport` + isometry `transport_norm`) — no separate §13 Σ-flow machinery needed. §14 observable correspondence **fully discharged**. Foundational triple, AxiomAudit-pinned. | `LF4-todo §14` |
| **§14 *states* obligation** | NoBroadcasting / SuperdenseCoding / Teleportation cite §14 for **state/projector** realisation (distinct from the observable-correspondence). No LF4 content to cite → needs genuine new state-realisation content. | `BRIDGE-OBLIGATIONS.md` |
| **Lévy / spherical isoperimetry** (TH-1) | Canonical-typicality concentration (single-state typicality). Mathlib lacks spherical isoperimetry; the mean is proved. Optional strengthening. | `thermo-plan.md` |
| **Continuity-only Stone** | The non-C¹ Stone strengthening (drop the smoothness hypothesis). The C¹ case is done. | `future-work.md` (W5-S2) |

## XL — Mathlib-scale (depth, not correctness)

| Item | Status | Former source |
|---|---|---|
| **Manifold exterior calculus** (Kähler `dω=0`, symplectic gradient — KG-1/2/3) | Genuine upstream gap; the volume is forced and the pointwise Kähler core is proved, so this is formalization-depth, not a correctness gap. | `future-work.md` (KG-1/2/3) |
| ~~Pointwise Birkhoff ergodic theorem~~ | **Do not pursue** — the single-flow route is a proved dead-end CSD does not take (NG1). | — |

## Research — physics-first, not formalization tasks

| Item | Note | Source |
|---|---|---|
| **A5 sector origin** (derive `(Σ, π, G)` from primitive ontology) | The one genuine ★ open frontier. `flow_admits_invariant_ne_fubiniStudy` proves a single flow can't do it. | `reconstruction-status.md §7` |
| **Track B — quantum relaxation** (Valentini H-theorem) | The only route to *new predictions* past the "empirically identical" ceiling. | `project` note |
| **CV chain** — continuous spectra | Extend Born-as-volume past finite `ℂℙⁿ`. Foundations begun (`CsdLean4/CV/`). | `project` note |

## Hardening / conventions (from the 2026-07-20 Lean-QIT / Physlib comparison — `CONVENTIONS.md §8`)

| Item | What / why | Size |
|---|---|---|
| ~~**Zero-`axiom` CI gate**~~ | **DONE 2026-07-21**. `check-claims.sh` now sets `DECLARED_AXIOMS=""` and fails on ANY `^axiom ` under `CsdLean4/` (the whitelist is empty now that `busch_effect_gleason` is discharged). Gates the Physlib route. (`CONVENTIONS.md §8.1`) | **S** |
| ~~**Discharge `busch_effect_gleason`**~~ | **DONE 2026-07-21 — axiom deleted, corpus imports ZERO axioms.** Proved as `OperationalPackage.effect_gleason_representation` (`LF2/EffectGleason.lean`, foundational-triple, AxiomAudit-pinned); the `axiom` was removed from `BornWrapper.lean` and its consumers `born_form_of_package` / `pure_state_born_weights_of_certainty` relocated to `EffectGleason.lean` (signatures unchanged). Step 4 pieces: `qmatrix_posSemidef`, `qmatrix_trace_one`, `qdensity`, `qdensity_unique` (via the polarisation lemma `matrix_eq_zero_of_quadForm_zero`). Guards updated (`check-claims.sh` zero-axiom gate, `AxiomAudit` pins, `AXIOMS.md §2.2`). Full history below. — Finite-dim effect-Gleason → "three axioms, zero imported". **Steps 1–2 LANDED** (`LF2/EffectGleason.lean`, 2026-07-20): step 1 foundational layer (`Effect.smul`, `p_zero`, `p_mono`, `p_smul_add`, `p_smul_mono`) + **step 2 homogeneity** `p(t•E)=t·p E` on `[0,1]` (`p_smul_homog`, via `smulVal_natMul`→`smulVal_rat`→`smulVal_homog`, the monotone-Cauchy density squeeze) — all foundational-triple, no `sorry`. **Step 3 spectral reduction LANDED**: `p_finsetSum` (finite additivity), `Effect.eigenvalues_le_one`, `Effect.sum_eigenEffect_M`, `p_eq_eigen_sum` (`p(E)=∑ᵢλᵢ·p(\|eᵢ⟩⟨eᵢ\|)`) — reduces the problem to `p` on rank-one projectors, foundational-triple, no `sorry`. **Step 3b polarisation identities LANDED**: `outerProduct_parallelogram` (`|u+v⟩⟨u+v|+|u−v⟩⟨u−v|=2|u⟩⟨u|+2|v⟩⟨v|`, cross terms cancel) + `outerProduct_polarization_real` — the algebraic core letting `p` inherit the parallelogram law, foundational-triple, no `sorry`. **Step 3b groundwork LANDED**: `outerEffect` (sub-unit rank-one `\|v⟩⟨v\|` for any `‖v‖≤1`, via `1-\|v⟩⟨v\|=(1-\|v̂⟩⟨v̂\|)+(1-‖v‖²)\|v̂⟩⟨v̂\|`), `outerProduct_smul`, and `p_outerEffect_smul` (degree-2 homogeneity `p(\|c·v⟩⟨c·v\|)=c²·p(\|v⟩⟨v\|)`) — foundational-triple, no `sorry`. **Step 3b `p`-parallelogram LANDED**: `one_sub_two_outerProduct_posSemidef` (CS sum-of-projectors `≤I`, not the feared eigenvalue bound) + `p_outerEffect_sqrt2` (√2-doubling) + **`p_parallelogram`** (`p(|u+v⟩⟨u+v|)+p(|u−v⟩⟨u−v|)=2p(|u⟩⟨u|)+2p(|v⟩⟨v|)` for `‖u‖²+‖v‖²≤½`) — foundational-triple, no `sorry`. **Step 3b-final (ρ-build) LANDED 2026-07-21**: `qform` (`q v=‖v‖²·p(\|v̂⟩⟨v̂\|)`, the degree-2 homogeneous extension off the unit ball) with `qform_eq_p` / `qform_smul` / **`qform_parallelogram`** (unrestricted parallelogram law); the Jordan–von Neumann core `qpolar_add_half`→**`qpolar_add_left`** (bi-additivity) and **`qpolar_smul_real`** (`ℝ`-homogeneity) via the new general lemma **`additive_bounded_linear`** (bounded additive `ℝ→ℝ` is linear — replaces the classical *continuity* step, which is unavailable since `p` is an arbitrary assignment, by the bound `0≤q≤‖·‖²`); the complex polarisation **`qsesq`** `S(u,v)=¼f(u,v)−(i/4)f(u,i·v)` shown sesquilinear (`qsesq_add_right`, `qsesq_smul_right`, `qsesq_conj_symm`) with `qsesq_self : S(v,v)=q v`; and the matrix **`qmatrix`** `R j k=S(eⱼ,eₖ)`, Hermitian (`qmatrix_isHermitian`), with **`p_outerEffect_eq_trace`** (`p(\|v⟩⟨v\|)=Tr(R·\|v⟩⟨v\|)`) and — through the spectral reduction — **`p_eq_trace` : `p E = Tr(R·E)` for EVERY effect**. All foundational-triple, no `sorry`. **Remaining (step 4 only):** `R.PosSemidef` (from `OP.nonneg`), `R.trace=1` (from `OP.total_one`), uniqueness (non-degenerate trace pairing) → package `R` as a `DensityOperator` and rewrite the axiom as a theorem in `BornWrapper.lean`; then update `AXIOMS.md §2.2` + add the zero-`axiom` CI rule. Cosmetic for CSD (NG2) but clears the last `axiom` + gates Physlib. | **S–M** |
| **`REFERENCES.json` + line-precise citations** | Machine-readable provenance; docstrings cite `[Key, file:Lstart-Lend]` incl. exact CSD-preprint lines. Biggest auditability win. (`§8.2`) | **M** |
| **`_statement`/`_of_`/final-theorem pattern** | Turn `BRIDGE-OBLIGATIONS.md` prose into explicit `_of_` hypotheses; discharging an obligation = removing a hypothesis. (`§8.3`) | **M** (incremental) |
| **`autoImplicit=false` + module-system migration + tagged Mathlib pin** | Mechanical hardening; fold into the next toolchain/module-system pass (needs a full green build each). (`§8.4`) | **S**/**L** |

---

## ecdsa.fail — EXTRACTED to a separate repository (2026-07-20)

**DONE.** The ecdsa.fail / ECDLP quantum-cryptanalysis track has been extracted to its own
repository and removed from this one. What was removed: the code (`CsdLean4/Ecdsafail/`, 23
files), its docs (`specs/ecdsa/`), the `Ecdsafail` `lean_lib` target (`lakefile.toml`), and
the `check-claims` exclude path. The new repo carries a **copy** of the shared
reversible-arithmetic DSL (`Mathlib/QuantumInfo/Reversible/`, 20 of 26 modules in Ecdsafail's
transitive closure) pinned to the same Mathlib commit.

**Stays here:** the `Reversible/` DSL — it is shared with core-QM (Shor +
`MeasurementGidneyAdder`/`Uncompute*`) and is not ecdsa-specific.

---

## Done this session (2026-07-19)

Honesty guard (`check-claims.sh`) · Track A#1 Schrödinger derivation · Track A#2 Kähler de-vacuum · A5/L7 ergodic bracket · §13.2 all 9 gates · §14 measurement connections (SG/Uncertainty/Hardy) · Mach–Zehnder · Double-slit + complementarity · **composite mixed-Born on `DensityOperatorIx`** (SL-T3 T9) · **Choi converse — Choi's theorem CP⟺PSD** (`LF2/ChoiConverse.lean`) · **Gisin's theorem — every entangled pure two-qubit state violates CHSH** (`LF6/GisinTheorem.lean`, closes LF6-6) · **Lindblad/GKSL generator tier** (`LF6/LindbladGenerator.lean`, LF6-9 generator level).

## Settled non-goals — do not re-litigate (see `reconstruction-status.md §7a`)

- **NG1** — single-flow / Birkhoff / ergodic route to Born: proved dead-end; CSD forces typicality by the LLN.
- **NG2** — Busch–Gleason "needed for CSD": no; the ontic Born rule is Gleason-free.

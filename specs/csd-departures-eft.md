# CSD-vs-QM departures, EFT corrections, and the falsification programme

The "beyond reproducing QM" thread: where CSD could *differ* from QM (and so become
falsifiable rather than equivalent), the EFT correction structure, and the negative-test
content. Distinct from [`qm-empirical-tests.md`](qm-empirical-tests.md) (reproduce QM) and
[`qi-qec-roadmap.md`](qi-qec-roadmap.md) (QI breadth). Created 2026-06-04.

## 0. The honest headline

As **formalised**, the corpus proves **CSD = QM exactly** at leading order: QM = volume
ratios on `Σ`, Born derived as the Fubini–Study typicality volume for general `N`,
Gleason-free. Every candidate departure below is a **structural debt** (`V ≈ 1−I`, `G3b`,
`D1`, finite-N), flagged but **not numerically pinned**. So the falsification programme is
**theory-gated** — owed by the paper sequence before the Lean side can certify a correction
— exactly as D1 and A5 are. This file maps what *would* be needed and where Lean slots in.

## 1. Candidate departures and their experimental handles

| Debt | CSD departure | Experimental handle | Status |
|---|---|---|---|
| **G3b** (Born = volume) | If the typicality measure is `μ = μ_FS + ε·δμ` (only *approximately* Fubini–Study), Born is only approximately second-order ⇒ a small **non-zero third-order (Sorkin) interference term** | **Triple-slit interference** (Sinha et al.); current bound `~10⁻²–10⁻³`. The sharpest, most concrete CSD-vs-QM test. | correction not pinned |
| **V ≈ 1−I** | A departure from QM's *exact* wave–particle duality `V² + D² = 1` toward a linear/approximate form | Interferometric **visibility vs which-path information** | correction not pinned; TN0 §9.3 forwarding remark owed |
| **D1 / determinism** | LF1 assumes i.i.d. (pairwise-independent) preparation sampling. A substrate with memory / finite mixing time ⇒ deviations from i.i.d. shot noise | **Temporal correlations in measurement records**; sub/super-Poissonian fluctuations beyond the SLLN rate. Near-term, high-statistics. | the most "CSD-honest" departure; not pinned |
| **Finite-N / EFT cutoff** | A fundamental finiteness of `Σ = ℂℙ^{N−1}` ⇒ saturation at extreme dimension | **Very-high-dimensional entanglement**; look for a Hilbert-dimension cutoff | see §3 |
| Gravity / entanglement geometry | CSD's ontic stance on gravity-from-entanglement may fix a specific answer | **Gravitationally-induced entanglement (BMV/GIE)** | long-horizon; the place CSD is *meant* to differ most |

**The Lean role**, once a correction is pinned: parametrise it (`μ = μ_FS + ε·δμ`), prove
`Born = leading + ε·correction`, expose the correction as a named "CSD ≠ QM" theorem. The
test infrastructure is already required to *not* assume `CSD = QM` identically
(`qm-empirical-tests.md §5.2`).

## 2. Negative tests

Two meanings:

**(a) Reproduce QM's nulls** — mostly done (no-go cluster). The one genuinely *CSD-specific*
negative theorem still owed is the **microstate-copy argument**: CSD naively looks like it
should permit cloning (copy the sampled microstate); the content is that *copying a sampled
microstate does not reproduce the quantum measure* `μ_prep` on the second factor. A formal
version — "no `Σ`-level copy reproduces `μ_prep`" — would be the first negative theorem that
*uses* the ontic substrate (`π`-equivariance, measure-preservation) rather than transporting
a Hilbert no-go. This is where a real `Σ`-side field finally earns its keep.

**(b) Falsification nulls** — bounds on superluminal signalling, non-linearity,
non-unitarity, spontaneous-collapse rates, macrorealism (Leggett–Garg). For CSD these are
consistency checks; the interesting case is where CSD predicts *non-null* against QM's null,
which is §1.

## 3. EFT structure

CSD as a **finite EFT of an ontic structure**: a power-counting scheme with leading order =
QM and corrections suppressed by a cutoff; "finite" = no UV divergences because
`Σ = ℂℙ^{N−1}` is compact and finite-dimensional.

### 3.1 What "finite" buys, and what it does not (the scale picture)

The finiteness is naturally **grounded in cosmology, not posited arbitrarily**: a positive
cosmological constant forces a finite-dimensional Hilbert space. The de Sitter horizon has
finite entropy `S_dS = A/4 = π/(Λ ℓ_P²) ≈ 10¹²²` (Planck units), so by the holographic /
Banks–Fischler–Bousso argument the Hilbert dimension of the observable universe is
`dim ~ exp(S_dS) ~ exp(10¹²²)`, finite. The natural identification for CSD:

```
N  ↔  exp(S_dS) ~ exp(10¹²²),    Λ = the IR regulator making N finite,
                                 ℓ_P = the UV resolution floor.
```

So "Planck (UV) to cosmological-constant (IR)" is exactly the window in which a finite `N`
is *required*. The corpus's compact `Σ = ℂℙ^{N−1}` is the realisation. (This `N ↔ exp(S_dS)`
identification is the steelman that the formalism + standard QG results *imply*; confirm it
against the actual paper text before relying on it.)

**What finite-`N` actually gives: bounded, discrete observable *spectra* — not lattice
spacetime.** Every observable is a finite Hermitian matrix, so its spectrum is discrete and
bounded (a maximum and minimum, finitely many levels); for astronomically large `N` the
spacing looks continuous. So "continuous but limited" is correct *of observable values*, not
of spacetime points. **"Lattice" is the wrong word:** a literal spacetime lattice breaks
Lorentz invariance (preferred frame, modified dispersion — killed by astrophysical timing
tests) and misplaces the discreteness in spacetime, whereas CSD's primitive is `Σ` (the
ontic *state* space) and spacetime is meant to emerge from entanglement geometry. The right
concept is **finite information capacity / a minimum-resolution continuum** (GUP-style
minimum length, no sites): lattice-like in *counting* (finite cells), not in *structure*.

### 3.2 The expansion parameter is `E/E_Planck`, not `1/N`

`1/N`-as-Hilbert-dimension **fails as the EFT parameter in both directions**: the
cosmological `N ~ exp(10¹²²)` makes `1/N` corrections `~ exp(−10¹²²)` (unobservable beyond
meaning), while the *system* Hilbert dimension (`N = 2` for a qubit) would predict order-`1/2`
deviations from Born that are manifestly not seen. So the corpus's general-`N` cluster being
*exact at each fixed `N`* is correct and `1/N` is **not** the correction tower.

The physically correct power-counting is the standard EFT ratio **`E/E_Planck`**: corrections
suppressed by powers of energy over the UV cutoff, tiny at lab energies (`~10⁻¹⁷` at a TeV),
visible only in high-energy / ultra-high-precision regimes. The finite-sample `1/√(trials)`
(from the deterministic-substructure debt, §1) is a *separate*, near-term parameter that
needs no Planck-scale energies.

- **Leading order = QM** — done.
- **Subleading = the novel prediction** — owed, theory-gated; the leading `E/E_Planck` term is
  the distinguishing experiment (feeds the G3b / V≈1−I handles in §1).

### 3.3 The honest consequence

The finiteness tied to `Λ` is a **consistency virtue** (no UV catastrophe, finite
information, well-defined Hilbert space) **rather than a source of visible departures** — its
corrections are cosmologically suppressed. The *testable* departures come from a different
place: `E/E_Planck` (extreme energy) or, more near-term, the deterministic-substructure /
finite-sample statistics (§1), which require no Planck-scale energies at all. Deepest
theory-gated item: the EFT power-counting (the operator tower and matching) must be *defined*
by the paper sequence before Lean can formalise a correction.

## 4. The through-line (why this is the priority that is not yet Lean-ready)

Algorithms, stabilisation (`qi-qec-roadmap.md §3`), and the departures here converge on the
**same two missing structures**: the **dynamics layer** (`Φ ≠ id`; D1 + the LF5
measurement-update sub-layer) and the **finite-N / finite-sample correction tower** (this
file). The corpus is a complete, verified account of the *leading-order static* theory. The
next era is (i) turning on dynamics, and (ii) the first correction beyond leading order —
the only place CSD becomes *falsifiable against* QM rather than *equivalent to* it.

Priority verdict: the falsification programme (§1, §3) is the most foundationally valuable
work, but it is **theory-gated** — it needs the papers to pin a correction first. The
Lean-ready work that *exercises the same dynamics layer* is **stabilisation and algorithms**
(operational faces of D1), not more static examples. So the practical next step remains the
QI-breadth tranche that touches dynamics, while the departures here wait on the theory.

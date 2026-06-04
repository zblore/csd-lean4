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

- **Expansion parameter** — candidates: `1/N` (dimension / finite-N cutoff) and
  `1/√(trials)` (finite-sample). The corpus's general-`N` Born-from-volume cluster is
  currently *exact at each fixed `N`*: the leading order *for all N*, but **not yet an
  expansion in `N`**. An EFT formalisation treats `N → ∞` as the QM limit and `1/N` as the
  first correction tower. This is a genuinely new direction — `N` is a fixed parameter
  today, not an EFT variable.
- **Leading order = QM** — done.
- **Subleading = the novel prediction** — owed, theory-gated; the leading correction *is* the
  distinguishing experiment (feeds the G3b / V≈1−I handles in §1).
- **"Finite" as a falsifiable claim** — no continuum/QFT UV catastrophe; a fundamental
  finiteness testable in principle at extreme dimension/energy.

Deepest theory-gated item: the EFT power-counting must be *defined* by the paper sequence
before Lean can formalise a correction.

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

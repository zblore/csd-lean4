# CsdLean4/Interop — adapters to external Lean libraries

Created 2026-08-06 (architecture decision: one unified CSD repository, external
libraries underneath as dependencies). **Documentation-only for now** — no external
dependency exists yet (`csd-lean4` is on Lean 4.33.0 stable as of 2026-08-10; Physlib
still on 4.32.0, expected to bump ~8 days after the 4.33.0 release), so this
directory holds no `.lean` files until the first provider lands.

Policy (canonical statement: `specs/external-library-map.md`; charter:
`specs/CSD-CHARTER.md` §"Repository architecture"):

- External libraries (Physlib for physical systems/dynamics/chaos models; Lean-QIT or
  Physlib-QuantumInfo for information theory) own **generic objects**; `csd-lean4` owns
  the **CSD theorems about them**.
- When an external type is adopted, the adapter between it and the canonical internal
  interface lives here (`Interop/Physlib/`, `Interop/LeanQIT/`) — one provider per
  capability layer, never two competing state/channel types through the corpus.
- Until then, generic objects the CSD layer needs are declared as small abstract
  interfaces near their use sites (e.g. the planned `FloquetEvolution`), marked
  `upstream-candidate`, and instantiated from the existing local machinery.

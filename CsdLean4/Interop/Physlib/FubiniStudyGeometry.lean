/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import CsdLean4.Mathlib.Analysis.InformationGeometry.FubiniStudyFisherRao
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFubiniStudyRiemannian
public import CsdLean4.Mathlib.Geometry.Manifold.Instances.ProjectiveSpaceFisherRao
public import CsdLean4.Mathlib.Analysis.SpecialFunctions.JapaneseBracketEuclidean

/-!
# Physlib export root: the Fubini–Study geometry of `ℂℙⁿ` and its Fisher–Rao bridge

**Category:** Special (a convenience re-export; the review scope of the Physlib export).

This module contains no mathematics. Its import closure within `CsdLean4/Mathlib/` is exactly
the material offered to Physlib (`leanprover-community/physlib`) for the Fisher information
work of PR #1652: the manifold structure of `ℂℙⁿ` with its affine atlas, differential forms and
the exterior derivative, the symplectic and Kähler structure, the Fubini–Study form, metric and
volume, the torus moment map, and the bridge

    `fsMetric x u v = fisherRaoInner (toOpenSimplex x) (momentDeriv x u) (momentDeriv x v)`

for `u` horizontal at a point of the regular stratum
(`Projectivization.fsMetric_eq_fisherRaoInner`), with its vector-level form
`FisherRao.fisherRaoInner_bornDeriv` on the open simplex of `FisherRao.lean`.

`scripts/export-physlib.sh` computes that closure, slices it in dependency order, renames the
modules to the Physlib layout, checks the result mentions nothing CSD-specific outside
provenance notes, builds it against Physlib's Mathlib pin, and writes
`CsdLean4/Interop/Physlib/MANIFEST.md`, the page a reviewer reads first. Nothing in the closure
imports a CSD layer (`scripts/check-import-hygiene.sh`, rule 4).

When Physlib has merged the tree and this repository depends on Physlib, this directory gains
the one-line adapters between the two libraries' quantum-state types and the export script
retires. Until then it is the window, not the wall.
-/

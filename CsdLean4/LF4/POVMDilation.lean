import CsdLean4.LF2.POVM
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# LF4: Naimark dilation of a POVM and the Born transfer

**Category:** 3-Local (LF4 dilation layer on the LF2 `POVM` type).

This is **P.2** of the POVM tranche (`specs/povm-plan.md`): the abstract Naimark
data and the Born transfer, the bridge that turns a (non-projective) POVM Born
weight into a **projective** Born weight on a dilated space, where the achieved
`fs_born_volume_ratio_N` result reads it as a Fubini–Study volume.

## Naimark dilation

A POVM `{Eᵢ}` on `ℂ^N` is the compression of a projective measurement on the
dilated space `ℂ^N ⊗ ℂ^ι`: there is an isometry `V : ℂ^N → ℂ^N ⊗ ℂ^ι`
(`Vᴴ V = I`) such that `Eᵢ = Vᴴ Πᵢ V`, where `Πᵢ = I_N ⊗ |i⟩⟨i|` (`blockProj i`)
is the rank-`N` ancilla-`i` projector. Then the **Born transfer**

```
⟨ψ, Eᵢ ψ⟩ = ⟨Vψ, Πᵢ (Vψ)⟩
```

makes the POVM weight the *projective* Born weight of the dilated state `Vψ`
against `Πᵢ` — a coarse (rank-`N`) projective outcome, i.e. a union of rank-1
computational-basis cells on `ℂℙ^{N·|ι|−1}`.

`NaimarkDilation P` carries the dilation as **supplied data** (an isometry `V`
with the pullback property), not constructed here — dilations are non-unique
(honest-scope note in the plan). The canonical construction from `√Eᵢ` (which
inhabits this structure for every POVM) is the separate existence half (P.5).

`born_transfer` mirrors `Empirical/QM/Bell.lean`'s `inner_alphaVec_betaVec`:
push `V` across the inner product via the matrix↔operator adjoint bridge
(`toEuclideanLin_conjTranspose_eq_adjoint`), fold the three operator
applications with `toLpLin_mul_same`, and collapse with the pullback identity.
-/

open Matrix
open scoped Kronecker

namespace CSD
namespace LF4

open CSD.LF2

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **ancilla-`i` block projector** `Πᵢ = I_N ⊗ |i⟩⟨i|` on the dilated index
`Fin N × ι`. In the computational basis it is `∑ₙ |e_{(n,i)}⟩⟨e_{(n,i)}|`, the
rank-`N` projector onto the `i`-th ancilla level. -/
noncomputable def blockProj (N : ℕ) (i : ι) : Matrix (Fin N × ι) (Fin N × ι) ℂ :=
  (1 : Matrix (Fin N) (Fin N) ℂ) ⊗ₖ Matrix.single i i 1

/-- **Naimark dilation of a POVM (supplied data).** An isometry
`V : ℂ^N → ℂ^N ⊗ ℂ^ι` (`Vᴴ V = I`) whose conjugation of the ancilla block
projectors recovers the effects: `Vᴴ Πᵢ V = Eᵢ`. This is the defining Naimark
property; the family `{Πᵢ}` is a genuine projective measurement on the dilated
space (`∑ᵢ Πᵢ = I_N ⊗ I_ι = I`), and `V` compresses it to `{Eᵢ}`. -/
structure NaimarkDilation (P : POVM N ι) where
  /-- The dilation isometry, as a matrix `ℂ^N → ℂ^{N×ι}`. -/
  V : Matrix (Fin N × ι) (Fin N) ℂ
  /-- `V` is an isometry: `Vᴴ V = I`. -/
  isom : Vᴴ * V = 1
  /-- Naimark pullback: each effect is the compression of an ancilla projector. -/
  pullback : ∀ i, Vᴴ * blockProj N i * V = (P.E i).M

namespace NaimarkDilation

/-- **Born transfer.** The POVM Born weight `⟨ψ, Eᵢ ψ⟩` equals the *projective*
Born weight `⟨Vψ, Πᵢ (Vψ)⟩` of the dilated state `Vψ` against the ancilla block
projector `Πᵢ` on `ℂ^N ⊗ ℂ^ι`. This is the bridge onto the projective-Born surface
that `fs_born_volume_ratio_N` reads as a Fubini–Study volume (P.3).

Proof: the matrix↔operator adjoint bridge moves `V` across the inner product,
`toLpLin_mul_same` folds `Vᴴ · Πᵢ · V`, and `pullback` collapses it to `Eᵢ`. -/
theorem born_transfer (P : POVM N ι) (D : NaimarkDilation P)
    (ψ : EuclideanSpace ℂ (Fin N)) (i : ι) :
    P.weight ψ i
      = RCLike.re (inner ℂ (Matrix.toEuclideanLin D.V ψ)
          (Matrix.toEuclideanLin (blockProj N i) (Matrix.toEuclideanLin D.V ψ))) := by
  unfold POVM.weight
  congr 1
  symm
  -- ⟨Vψ, Πᵢ(Vψ)⟩ = ⟨ψ, Vᴴ Πᵢ V ψ⟩ = ⟨ψ, Eᵢ ψ⟩.
  rw [← LinearMap.adjoint_inner_right (Matrix.toEuclideanLin D.V),
    show (Matrix.toEuclideanLin D.V).adjoint = Matrix.toEuclideanLin (D.V)ᴴ from
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint D.V).symm,
    show Matrix.toEuclideanLin (D.V)ᴴ
          (Matrix.toEuclideanLin (blockProj N i) (Matrix.toEuclideanLin D.V ψ))
        = Matrix.toEuclideanLin ((D.V)ᴴ * blockProj N i * D.V) ψ from by
      simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply],
    D.pullback i]

end NaimarkDilation
end LF4
end CSD

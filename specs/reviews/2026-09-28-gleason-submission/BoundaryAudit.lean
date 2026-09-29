import CsdLean4.Mathlib.Analysis.InnerProductSpace.Gleason.Piron

open scoped InnerProductSpace

namespace SubmissionBoundaryAudit

/-- The total normalization used by coldest degenerates at the pole. -/
theorem coldest_at_pole (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    Gleason.coldest p p = 0 := by
  simp [Gleason.coldest, hp]

/-- At the pole the descent is the whole hemisphere, not a great semicircle. -/
theorem descent_at_pole (p : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1) :
    Gleason.descent p p = Gleason.northern p := by
  ext t
  simp [Gleason.descent, coldest_at_pole p hp]

/-- At an equatorial starting point the descent is the whole equator. -/
theorem descent_at_equator (p s : EuclideanSpace ℝ (Fin 3))
    (hp : ‖p‖ = 1) (hs : ⟪p, s⟫_ℝ = 0) :
    Gleason.descent p s = Gleason.equator p := by
  have hc : Gleason.coldest p s = p := by
    simp [Gleason.coldest, hs, hp]
  ext t
  simp only [Gleason.descent, Gleason.northern, Gleason.equator, Set.mem_ofPred_eq,
    hc, real_inner_comm t p]
  constructor
  · rintro ⟨⟨ht, _⟩, hz⟩
    exact ⟨ht, hz⟩
  · rintro ⟨ht, hz⟩
    exact ⟨⟨ht, hz.ge⟩, hz⟩

end SubmissionBoundaryAudit

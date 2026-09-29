# Full supporting-code review — 5f77294d

Date: 2026-09-28. Read together with the submission report and source manifest.
All 16 local modules (8,001 lines) received a full code/comment read across this review session
and its continuation. This is a manual mathematical assessment, backed by fresh compilation
and the saved probes; it is not a second independent review or a formal proof of the review.

## CKM core

- **Sphere (380 lines):** checked frame-space operations, orthonormal completion, evenness,
  four-point identities and the strict-margin near-maximum/orthogonal-near-minimum argument.
  Nonempty sphere and the required bounds support the supremum/infimum uses. One-sided
  approximation lemmas do not require an otherwise missing boundedness assumption: an
  unbounded image also supplies the requested one-sided witnesses. Nonnegative frame functions
  are bounded by their weight. The regularity claim in the header needs the nonnegativity
  qualification (CR-GLEASON-008).
- **Piron (621):** checked the gnomonic normalization and nonzero denominators, the complex
  tangent-plane identification, cosine positivity for the chosen number of spiral steps,
  radius growth bound, and two-step ray construction. The equatorial target is treated
  separately; the geometric theorem excludes the pole. Total helper definitions at the pole
  do not describe a unit coldest vector or a semicircle. BoundaryAudit proves the pole and
  equatorial degeneracies (CR-GLEASON-008).
- **Warmup (362):** checked the floor/fractional-part extension of interval additivity,
  including the carry and endpoint cases. The second warmup avoids the countable exceptional
  set using an uncountable interval, establishes rational homogeneity on the allowed points,
  then squeezes by monotonicity. The final triple pins the affine coefficient; continuity is
  not assumed. Zero rational and endpoint values are covered separately.
- **SimpleFrame (560):** checked exact and approximate descent inequalities; pole exclusions
  match the geometric hypotheses. Latitude fibres are nonempty and bounded before taking
  their extrema. Ordered disjoint gaps give countably many exceptional latitudes. Warmup II
  and density of the complement remove those exceptions, including endpoints; evenness
  extends from the northern hemisphere. The constant case precedes division by the range.
- **Extremal (617):** checked maximum attainment without assuming continuity of the frame
  function. Compactness gives convergence of sphere points; convergence of their function
  values is proved independently by squeezing. A compact product box supplies a filter
  cluster point, not sequential compactness of an uncountable product. Closed finite frame
  equations and equator constraints survive the limit. Frequent coordinate approximation
  combines with eventual bounds, and a fixed two-step descent controls the accumulated error.
  The minimum follows by negating the bounded frame function.
- **General (696):** checked selection of orthogonal maximum/minimum axes using the extrema
  theorem and the near-orthogonal-minimum estimate. The residual has weight zero, is bounded,
  and changes sign under the relevant quarter-turn. If nonzero it has a positive maximum.
  The circle lemma treats the parallel-normal degeneracy separately; four normals and
  Parseval force that maximizer onto an axis where the residual vanishes. The final matrix is
  an explicit sum of weighted outer products. The file explicitly describes its endgame as
  differing from the paper. The reflection helper's prose needs a unit-normal qualification.

## Complex projection route and shared reconstruction

- **ProjectionPackage (380):** checked the total matrix assignment, projection-only premises,
  complement-derived upper bound, finite orthogonal sums, rank-one outer products and phase
  invariance. The real restriction's weight is proved basis independent by a Gram identity;
  it is not assumed to equal one on a proper subspace. Nonnegativity transports on unit vectors.
- **FrameFunction (627):** checked phase extraction and conjugation signs in the Hermitian
  plane coefficient, including zero coefficients before division. Real-plane regularity gives
  the full complex-plane formula via phase invariance. The global homogeneous extension
  handles zero and dependent vector pairs separately before Gram–Schmidt; its docstring
  overstates availability of an orthonormal pair in dimension one. Triple extension uses
  N >= 3. Restriction of the core matrix recovers the two diagonal and midpoint coefficients.
- **Polarization (475):** checked bounded additive implies real linear, the complex
  polarization sign, sesquilinearity, Hermitian symmetry, and matrix reconstruction including
  off-diagonal entries. The bound rules out pathological merely additive real maps.
- **Descent (265):** checked scaling from sphere to all vectors, recovery from real quadratic
  values for Hermitian matrices, PSD, trace, uniqueness, and spectral descent from rank-one
  projectors to arbitrary projections through eigenvalues zero or one.
- **Reduction (76) and Core (61):** checked that the conditional core interface is actually
  supplied by the proved CKM theorem and the exported representation has no remaining core
  assumption. Probability assignments on projections are not projection-valued measures;
  the nonnegative source theorem is Gleason 2.8 (CR-GLEASON-007).

## Real routes

- **Real (1,016):** checked the projection package and finite additivity, real Gram transport,
  restriction, real polarization, homogeneous extension, dependent/independent plane cases,
  triple extension, PSD/trace/uniqueness and spectral descent. The roadmap has old names only
  (CR-GLEASON-006).
- **RealFrame (338):** checked basis reindexing and orthogonal completion, evenness and bounds,
  and basis-independent restriction using a fixed complement. Weight zero is handled before
  positive-weight normalization; negative weight is impossible for nonnegative input. The
  conclusion is PSD with trace W, not necessarily a normalized density matrix.

## Busch route, reconciled with current source

- **BornWrapper (481):** reread the current source rather than crediting the older branch
  review. Effects mean PSD E and PSD (I-E); density means PSD and complex trace one. Redundant
  Hermitian/upper-bound fields do not add mathematical assumptions. Checked complements,
  unitary conjugation, finite-index outer products, trace/overlap and spectral identities.
  Certainty of a rank-one outcome forces the complementary PSD sandwich to have zero trace,
  hence vanish; the PSD null-vector identity removes cross terms and the rank-one sandwich
  gives uniqueness. The header's imported-axiom claim is false on this snapshot. Historical
  text, the covariance discussion and moved-declaration pointers need reconciliation with the
  prior review-branch cleanup (CR-LF2-007).
- **EffectGleason (1,046):** reread the complete refactored file. Difference effects give
  monotonicity; scalar additivity gives rational homogeneity; a two-sided monotone squeeze
  gives real homogeneity, including endpoints and zero probabilities. Finite additivity keeps
  partial sums below I using positivity of omitted terms. Eigenvalues lie in [0,1]; spectral
  reduction uses genuine effects. The Cauchy–Schwarz bound justifies both sums in the local
  parallelogram identity. A strictly positive common scale extends it to arbitrary vectors.
  Complex phases disappear from outer products. The shared engine then constructs the matrix;
  its PSD, complex trace one and uniqueness are derived, not supplied by input. The proof
  works in dimensions one and two; normalized zero-dimensional inputs are impossible.
  Compatibility wrappers retain an unnecessary dimension bound, but the main theorem does
  not. No continuity or commutativity assumption is hidden in the effect assignment.

## Scope and disposition

No theorem-level mathematical defect found. The newly noticed domain descriptions are fixed
in a proposed comment-only patch, with degenerate geometry checked by Lean. Existing main vs
review-branch API/comment differences remain explicit in the report. No claim is made that
all CSD event-to-effect assumptions or independence claims are validated by this theorem review.

The review examined the code's argument rather than requiring line-by-line identity with a
published proof. The Gleason/Busch statement comparison is linked in the report. The CKM paper
was located, but its scanned pages were not fully text-accessible in this session; the review
does not certify every historical section reference or novelty/priority claim in the headers.

# Archived: monodromy route to nonsplitting (Zariski Theorem 4.2.2)

This directory preserves the **partial monodromy formalization** of Zariski's nonsplitting
theorem (the route the thesis takes for Theorem 4.2.2 / Axiom 1
`irreducible_section_single_root_deg`). It was set aside in favour of the **Newton–Puiseux**
route, which closes *both* remaining Zariski axioms (nonsplitting *and* order-invariance) from a
single parametrization and bypasses the geometric loop-deformation. See the project memory for the
strategic decision.

These files are **not part of the build** (removed from `Mccalum.lean`). They are kept as a
documented, working partial proof. To reactivate, move them back under `Mccalum/Generalized/` and
re-add the imports to `Mccalum.lean`. They were green and axiom-clean when archived.

## Contents

### `ComplexCovering.lean` — the branched root-covering (M2, complete)
Reusable analytic infrastructure + the covering map:
- `analytic_root_section_complex` — complex analytic IFT (local holomorphic root section at a simple
  root). **Likely reusable for the Puiseux convergence bridge.**
- `local_disjoint_root_sections`, `separable_distinct_simple_roots`, `evalFamily_continuous`,
  `evalFamily_analyticAt`, `evalFamily_fderiv_t` — generic analytic/algebra tools.
- `rootVariety`, `rootProj`, `rootProj_isProperMap`/`isClosedMap`, `rootProj_openPartialHomeomorph`,
  `rootProj_isCoveringMapOn`, `rootProj_isCoveringMap_restrict` — the full covering map over the
  separable locus (monodromy-specific; orphaned by the Puiseux route).

### `Monodromy.lean` — transitive monodromy + contradiction kernel (M3/M4, partial)
- `path_confined_to_open`, `path_endpoint_not_in_other`, `liftPath_confined` — the topological
  confinement kernel ("the lift stays in one disc").
- `monodromy_exchange_contradiction` — the step-4 contradiction skeleton.
- `transitive_monodromy_of_pathConnected` — path-connected covering ⟹ transitive monodromy
  (the topological half of Lemma 4.2.5).

## What was *not* built (the monodromy route's remaining pieces)
- The connectedness kernel: irreducible Weierstrass ⟹ root variety path-connected over `{disc≠0}`
  (the Bochner–Martin [BMA48] content).
- The geometric loop deformation `Γ → Γ''` in the generalized setting.

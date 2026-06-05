# Plan: finishing Conclusion 1 (nonsplitting / `irreducible_section_single_root_deg`) via the thesis proof

**Goal.** Discharge the last axiom on which *Conclusion 1* of Zariski 4.1.1 depends,
`irreducible_section_single_root_deg` (A4-deg), by porting the thesis's own proof of
**Theorem 4.2.2** (nonsplitting) — the transitive-monodromy + homotopy-deformation argument —
rather than the alternative clopen-split shortcut.

**Why this route.** The thesis (`thesis/thesis.tex`) contains a complete, correct proof, which is a
large advantage for the formalization. Its logical core is *already formalized* (archived), and the
one piece that was missing when it was archived — the connectedness kernel of Lemma 4.2.5 — is exactly
what the Newton–Puiseux subproject (`Mccalum/Puiseux/RootCover.lean`) now proves. So the monodromy
route and the Puiseux work **converge**: the Puiseux connectedness result unblocks the monodromy proof,
and the Puiseux parametrization remains the route to *Conclusion 2* (order-invariance). Nothing is
wasted.

---

## Where this sits in the overall development

Conclusion 1's whole chain is already proved **except** `irreducible_section_single_root_deg`:

- A2 factorization `weierstrass_irreducible_factorization` — axiom (have).
- A4-deg `irreducible_section_single_root_deg` — **the target of this plan**.
- A5 `irreducible_factors_section_share_root` — **proved** (`ZariskiNonsplitting.lean`).
- packaging `zariski_single_branch` / `zariski_nonsplitting` — **proved**.

In the thesis, A4-deg *is* the per-irreducible-factor argument inside the proof of Theorem 4.2.2
(`thesis.tex:2693–2740`). Steps 10–11 of that proof (distinct-factor reconciliation by resultant, and
the `ψ` packaging) are already done in Lean. We port the one remaining block.

### Thesis geometry (decoding `thesis.tex:2680–2740`)

Base `Δ₁ ⊆ ℂⁿ⁻¹`, coordinates `(z, z_{n-1})`: `z ∈ ℂⁿ⁻²` is the **section parameter** (`= y`),
`z_{n-1}` the **single transverse coordinate**, `z_n` the **root variable** (`t`). The discriminant is in
the normal form `F = z_{n-1}^r · N` (`N` non-vanishing), so the discriminant locus is the smooth
hyperplane `H* = {z_{n-1}=0}` — this is the codim-1 equisingular structure, and it matches the kernel
base `Fin 1 → ℂ` (the transverse coordinate).

### Codimension (the `e` parameter), and Case I / Case II

`CParam s e = (Fin s → ℂ) × (Fin e → ℂ)`, section `{e-block = 0}`. Here `s = dim S` and
**`e = codim(S) = (r−1) − s`**, which is `≥ 2` whenever `s ≤ r−3`. The pipeline genuinely reaches
`e ≥ 2`. The thesis handles this exactly as a two-case split (`thesis.tex:2187–2412`):

- **Case I (`e = 1`, `s = n−2`)** = Theorem 4.2.1/4.2.2 = the **homotopy proof** (M1–M4 below). The
  discriminant is in normal form `z_{n-1}^r·N` directly.
- **Case II (`e ≥ 2`)** = reduce to Case I via a **blow-up**, which here is an *explicit quadratic
  substitution* (not scheme-theoretic):
  ```
  Q(z, z_{s+1},…,z_{n-1}) = (z, z_{s+1}·z_{n-1}, …, z_{n-2}·z_{n-1}, z_{n-1}).
  ```
  With `h'(Z,Z_n) = h(Q(Z),Z_n)`, quasi-homogeneity of the Taylor terms gives
  `disc(h') = F∘Q = Z_{n-1}^r·N(Z)`, `N(0) ≠ 0` — i.e. **the blow-up converts the codim-≥2
  discriminant into the codim-1 normal form**. Apply Case I to `h'`, then push the conclusion down:
  `ψ(z) := ψ'(z,0,…,0)` (for Conclusion 1 the pushdown is immediate, `thesis.tex:2414–2418`).

**Architectural decision:** retarget the homotopy proof (M1–M4) at **`e = 1`**, where the thesis
argument lives natively and the normal form is free, and add the blow-up as a **separate reduction
layer** (M5b) that turns the general-`e` statement into the `e = 1` one. This mirrors the thesis's
Case I / Case II structure exactly.

---

## The proof maps to these tasks

Thesis step (`thesis.tex:2693–2740`) → Lean obligation → status:

| Thesis step | Content | Status |
|---|---|---|
| factor `h = h₁⋯hₖ` | A2 | axiom (have) |
| **Lemma 4.2.5** root-exchange `Γ_{hᵢ}[α]=β` | transitive monodromy of the irreducible cover | topological half **DONE** (`transitive_monodromy_of_pathConnected`); algebraic kernel **NOW available** via `clopen_split_contradiction'` (Puiseux) |
| step 4: discs `Dⱼ` + transverse disc `D'`, `mⱼ` roots in `Dⱼ` | bivariate root continuity (Rouché) | **NEW** (M2) |
| step 7: homotopy `H(s,t)` (collapse `z→w`) | explicit deformation `Γ→Γ'` in `U` | **NEW** (M3) |
| step 8: homotopy `K(s,t)` (radial → circle) | explicit deformation `Γ'→Γ''` | **NEW** (M3) |
| step 9: confinement contradiction | lift of `Γ''` stuck in `D₁`, ends at `β∈D₂` | logical core **DONE** (`monodromy_exchange_contradiction`, `liftPath_confined`) |
| step 10: factors reconcile (resultant) | A5 | **PROVED** |
| step 11: `ψ` holomorphic | `a₁(w,0)=-mψ` | **PROVED** |

Genuinely-new work is concentrated in **M1 (path-connectedness bridge), M2 (Rouché separation),
M3 (the two explicit homotopies)**, plus **M5 (normal form + blow-up)**. The contradiction skeleton
and everything downstream already exist.

---

## Phases

### M0 — Reactivate & re-scope *(mechanical)*
- Move `archive/monodromy/Monodromy.lean` back to `Mccalum/Generalized/Monodromy.lean`, re-add its
  import to `Mccalum.lean`.
- Deduplicate `transitive_monodromy_of_pathConnected` (identical copy already lives in
  `Mccalum/Puiseux/Covering.lean`); have `Monodromy.lean` import `Mccalum.Puiseux.Covering` and drop
  the local copy.
- Confirm green + axiom-clean (`#print axioms` on `monodromy_exchange_contradiction`).
- `ComplexCovering.lean` is already in the build.

### M1 — Lemma 4.2.5 (transitive monodromy / root exchange) *(the key synergy)*
The piece the archive README lists as "not built (Bochner–Martin content)"; now suppliable.

- **M1-kernel-fix (DONE).** Discovered `clopen_split_contradiction'` was **vacuous**: it required a
  clopen of the *full branched* `rootVariety`, but over a disc the branch point `(0,0)` glues every
  colliding sheet, forcing one side of any split empty (so `1 ≤ d_A ∧ 1 ≤ d_B` is unsatisfiable, and
  the docstring's own task C4.2 was impossible). Fixed by re-parameterizing the factor/count chain
  (`factor_coeff_analyticAt`, `sheet_mem_locally_const`, `aRootCount_eventually_*`,
  `factor_coeff_extends`, `exists_factor_weierstrass`, `clopen_split_factorization`,
  `clopen_split_contradiction'`) by an **open separable base `U`**, consuming a clopen of the
  *punctured* cover via `IsClopenOverBase q U A := IsClopen (Subtype.val ⁻¹' A : Set ↥(rootProj q ⁻¹' U))`
  and the helper `clopen_mem_const_over_sub`; `exists_local_root_sections` now returns `V ⊆ U`. Green,
  non-vacuous. (`Mccalum/Puiseux/RootCover.lean`.)
- **M1a (DONE).** `rootCover_preconnected` (`Mccalum/Generalized/Monodromy.lean`): for irreducible `q`,
  the cover over a punctured separable preconnected base `U ∈ 𝓝[≠]0` is `PreconnectedSpace`. Proof via
  `preconnectedSpace_iff_clopen`: a clopen split gives `A`, `Aᶜ` nonempty ⟹ (helper
  `rootCover_count_pos_freq`: count locally constant on connected `U`, positive at a witness sheet) two
  `∃ᶠ` positive counts ⟹ `clopen_split_contradiction'`. Axiom-clean.
- **M1b (DONE).** `rootCover_pathConnected`: the cover over `U` is `PathConnectedSpace`. Needed a
  general lemma `IsLocalHomeomorph.locPathConnectedSpace` (missing from Mathlib — local homeo pulls back
  local path-connectedness, proved via `LocPathConnectedSpace.of_bases` + the chart's `symm`-image),
  plus `rootCover_isCoveringMap` (from `rootProj_isCoveringMap_restrict`), `IsOpen.locPathConnectedSpace`
  for the base `↥U`, M1a for preconnectedness, and nonemptiness (`IsAlgClosed.exists_root`).
- **M1c (DONE).** `rootCover_exchange` (= Lemma 4.2.5): two sheets over the same base point are joined
  by a base loop whose lift carries one to the other — `transitive_monodromy_of_pathConnected` applied
  to the covering map with M1b's `PathConnectedSpace`. **The previously-"not built" Bochner–Martin
  content is now proved.**
- **Status: M1 COMPLETE.** All of `IsLocalHomeomorph.locPathConnectedSpace`, `rootCover_preconnected`,
  `rootCover_pathConnected`, `rootCover_isCoveringMap`, `rootCover_exchange` are green and axiom-clean
  (`Mccalum/Generalized/Monodromy.lean`).

### M2 — Rouché cluster separation (thesis step 4) *(new, standard)*
- `hᵢ(w,z_n)` has `l` distinct roots `αⱼ` (mult `mⱼ`) ⟹ disjoint discs `Dⱼ` and a transverse disc `D'`
  such that for every `w_{n-1}∈D'`, exactly `mⱼ` roots lie in `Dⱼ`. Argument principle / Hurwitz — the
  project already has the argument principle (Weierstrass-division proof), so this reuses it.
- Output: the `Dⱼ` (the disjoint opens `A=D₁`, `B=D₂`) + the confinement hypothesis
  `hconf : ∀t, φ''(t) ∈ ⋃ⱼ Dⱼ`.
- **Risk:** medium. Bivariate root-continuity bookkeeping.

### M3 — The two explicit homotopies (thesis steps 7–8) *(the genuine geometric work)*
The thesis gives explicit formulas:
- `H(s,t) = ((1−s)Γ(t)+s·w, Γ_{n-1}(t))` — collapse section component to `w`, untouched `z_{n-1}` ⟹
  stays in `U={z_{n-1}≠0}` (uses the normal form: `disc≠0 ⇔ z_{n-1}≠0`).
- `K(s,t) = (w, (1−s)Γ_{n-1}(t) + s·Γ_{n-1}(t)|w'_{n-1}|/|Γ_{n-1}(t)|)` — radial push onto the circle
  `|z_{n-1}|=|w'_{n-1}|`, stays in `U`.
- Obligations: each continuous, valued in `U`, `HomotopicRel {0,1}`; compose to `Γ.HomotopicRel Γ'' {0,1}`
  with `Γ''` on the small circle. Mathlib `ContinuousMap.HomotopyRel` / `Path.Homotopy`.
- **Risk:** medium–high — the fiddly part, but bounded: the maps are explicit and the downstream
  interface (`monodromy_exchange_contradiction`'s `hhom`, `hconf`, `heA`, `heβB`) is already fixed.

### M4 — Assemble the single-factor result *(wiring)*
- Combine M1 (`Γ`, `Γ_{hᵢ}[α]=β`) + M3 (`Γ≃Γ''`) + M2 (`hconf`, `D₁`, `D₂`) into
  `monodromy_exchange_contradiction` (done) ⟹ each irreducible factor has a single distinct root over `H*`.
- This is the codim-1 (`e=1`) form of `irreducible_section_single_root_deg`.

### M5 — Normal form + blow-up to the general-`e` axiom
- **M5a (`e = 1` normal form):** derive `disc = z_{n-1}^r·N`, `N` non-vanishing, from the
  constant-ambient-order hypothesis. This is the Weierstrass-factorization equivalence: `disc` vanishes
  on the section so `z_{n-1} | disc`; factor `disc = z_{n-1}^r·N` with `z_{n-1} ∤ N`; then
  `ord_{(y,0)}(disc) = r + ord_{(y,0)}(N)`, so *constant order ⇔ `N(y,0) ≠ 0` for all `y` ⇔ normal form*.
  Feeds M1–M4.
- **M5b (Case II, `e ≥ 2 → e = 1`):** the explicit quadratic substitution `Q`. Concrete algebra:
  1. `h∘Q` is a Weierstrass polynomial in the blown-up coords;
  2. `disc(h∘Q) = Z_{n-1}^r·N` with `N(0) ≠ 0` (quasi-homogeneity of Taylor terms);
  3. invoke the `e = 1` result;
  4. pushdown `ψ = ψ'(·,0,…,0)` + root-transport (clean for Conclusion 1; the order-invariance
     transport, `thesis.tex:2419+`, belongs to Conclusion 2).
- **Risk:** M5a trivial; M5b is concrete polynomial algebra, not abstract blow-up geometry.

---

## Dependency graph

```
RootCover.clopen_split_contradiction' (Puiseux, proved) ─► M1 (Lemma 4.2.5) ──┐
ComplexCovering (covering map, DONE)                    ─► M1, M2             ├─► M4 ─► A4-deg (e=1)
Monodromy.monodromy_exchange_contradiction (DONE) ◄───────────────────────────┘        │
M2 (Rouché) ─► M4 ;  M3 (homotopies) ─► M4                                             ▼
M5a (normal form) ─► M1–M4 ;  M5b (blow-up) ─────────────────────► irreducible_section_single_root_deg
                                                                        │
                              A5 (proved) + zariski_single_branch (proved)
                                                                        ▼
                                                       Conclusion 1 fully axiom-free
```

**Reuse / no waste:** Conclusion 2 (`zariski_order_invariant_in_graph`) is unaffected and shares
infrastructure — the Puiseux parametrization `φ` (Covering + Basic) is its route, reusing the same
`ComplexCovering` covering map and `Covering.lean` monodromy. M1 even *consumes* the Puiseux
connectedness result.

## Already-proved assets to reuse

- `Mccalum/Generalized/ComplexCovering.lean` — branched root covering: `rootProj_isCoveringMap_restrict`,
  `analytic_root_section_complex`, local sections.
- `archive/monodromy/Monodromy.lean` (→ reactivated) — `path_confined_to_open`, `liftPath_confined`,
  `monodromy_exchange_contradiction`, `transitive_monodromy_of_pathConnected`.
- `Mccalum/Puiseux/RootCover.lean` — `clopen_split_contradiction'` (connectedness kernel).
- `ZariskiNonsplitting.lean` — A5 + packaging (steps 10–11).

## References
- `thesis/thesis.tex:2540–2765` — Theorems 4.2.1/4.2.2, Lemmas 4.2.4/4.2.5, the homotopy proof.
- `thesis/thesis.tex:2187–2412` — Theorem 4.1.1, Case I / Case II (blow-up).
- `thesis/generalized/proof_corrected.md` — ambient order, the elimination-ideal → disc transfer
  (upstream of this axiom; does not affect M1–M4).

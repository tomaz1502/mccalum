import Mccalum.Generalized.RootSectionsAlgebra

/-!
# Single-cluster composition (part 1): disc-order ⟹ root structure

Chains the **Zariski axiom** (`zariski_root_sections`) with the proven **F2** root-extraction
(`weierstrass_section_isRoot`, `weierstrass_section_rootMultiplicity`): from the hypothesis that the
discriminant has constant vanishing order along the section (the output of
`DiscOrder.weierstrassDisc_order_const_along_section`), produce the holomorphic root sections `ψᵢ`
together with the full root/multiplicity structure of the section polynomial.

This is the "back half" of the single-cluster chain `descent → DiscOrder → Zariski → F2 → F1`.
-/

noncomputable section

open Polynomial Filter
open scoped Topology

/-- **Cluster root structure (single branch, Theorem 4.1.1).** From `disc(h) ≢ 0` and constant
discriminant order along the section, the section Weierstrass polynomial has a single holomorphic
root section `ψ` (the unique root, nonsplitting) of multiplicity `m`. Thin wrapper over
`zariski_single_branch`. -/
theorem cluster_root_structure {s e : ℕ} (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc_ne : order ℂ (weierstrassDiscFn m a) (0 : CParam s e) ≠ ⊤)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ ψ : (Fin s → ℂ) → ℂ,
      AnalyticAt ℂ ψ 0 ∧ ψ 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ α = ψ y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
        (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ y) = m) :=
  zariski_single_branch m hm a ha_an ha0 hdisc_ne hdisc

end

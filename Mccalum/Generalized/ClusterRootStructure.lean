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

/-- **Cluster root structure.** From constant discriminant order along the section, the section
Weierstrass polynomial's roots over the section are finitely many holomorphic sections `ψᵢ` with
constant positive multiplicities (`∑ = m`), distinct as branches, exhausting the roots (everywhere
near `0`) and realizing the multiplicities (wherever the `ψᵢ` values are distinct). -/
theorem cluster_root_structure {s e : ℕ} (m : ℕ) (hm : 0 < m)
    (a : Fin m → (CParam s e → ℂ)) (ha_an : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (hdisc : ∀ᶠ y in 𝓝 (0 : Fin s → ℂ),
      order ℂ (weierstrassDiscFn m a) ((y, 0) : CParam s e)
        = order ℂ (weierstrassDiscFn m a) (0 : CParam s e)) :
    ∃ (r : ℕ) (ψ : Fin r → ((Fin s → ℂ) → ℂ)) (mult : Fin r → ℕ),
      (∀ i, AnalyticAt ℂ (ψ i) 0) ∧ (∀ i, ψ i 0 = 0) ∧ (∀ i, 0 < mult i) ∧
      (∑ i : Fin r, mult i = m) ∧
      (∀ i j, i ≠ j → ¬ (ψ i =ᶠ[𝓝 (0 : Fin s → ℂ)] ψ j)) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), ∀ α : ℂ,
        (weierstrassPoly m a ((y, 0) : CParam s e)).IsRoot α ↔ ∃ i, α = ψ i y) ∧
      (∀ᶠ y in 𝓝 (0 : Fin s → ℂ), Function.Injective (fun i => ψ i y) →
        ∀ i, (weierstrassPoly m a ((y, 0) : CParam s e)).rootMultiplicity (ψ i y) = mult i) := by
  obtain ⟨r, ψ, mult, hψ_an, hψ0, hmult_pos, hsum, hdistinct, hfac⟩ :=
    zariski_root_sections m hm a ha_an ha0 hdisc
  refine ⟨r, ψ, mult, hψ_an, hψ0, hmult_pos, hsum, hdistinct, ?_, ?_⟩
  · filter_upwards [hfac] with y hfy α
    exact weierstrass_section_isRoot y hfy hmult_pos α
  · filter_upwards [hfac] with y hfy hinj i
    exact weierstrass_section_rootMultiplicity y hfy hinj i

end

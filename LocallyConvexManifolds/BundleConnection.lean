/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.ConnectionForm
import LocallyConvexManifolds.VectorBundle

/-!
# Connections on vector bundles

A connection on a vector bundle `V` with fiber `F` over a manifold `M` modeled on `E` is given in
the trivialization over each chart `i` by symbols `Γᵢ(y)(a, ξ) ∈ F`, bilinear in `a ∈ E` and
`ξ ∈ F` (`IsLocalSymbol`), subject to the **gauge transformation law**
`Γⱼ(τ y)(dτ(y) a, g(y) ξ) = g(y) Γᵢ(y)(a, ξ) + (∂_a g)(y) ξ`,
where `τ = j ∘ i⁻¹` and `g(y) ξ = g_{ij}(i⁻¹ y) ξ` is the coordinate change of the bundle
(`BundleConnection`). For the tangent bundle this is the change of charts law of the Christoffel
symbols (`Connection.toBundleConnection`).

The covariant derivative of a section is `∇_X s = ds · X − Γ(X, s)` in a trivialization
(`localCovDerivB`); it transforms covariantly, `∇_{Xⱼ} sⱼ(τ y) = g(y) ∇_{Xᵢ} sᵢ(y)`
(`localCovDerivB_transition`). The curvature is `∇_X ∇_Y s − ∇_Y ∇_X s − ∇_[X,Y] s =
R(X, Y) s` (`localCovDerivB_curv`), where `R = Ω` is the curvature form of
`LocallyConvexManifolds.ConnectionForm`.

## Main results

* `curvature_gauge` (local) and `BundleConnection.curvLoc_transition`: **the curvature is a
  tensor**, `Ωⱼ(τ y)(dτ u, dτ v)(g ξ) = g Ωᵢ(y)(u, v) ξ`. In contrast with the connection form,
  the inhomogeneous terms cancel. The proof evaluates the curvature formula on constant fields and
  sections in the chart `i` and on their images in the chart `j`, so it uses neither partitions of
  unity nor bump functions, which need not exist on locally convex manifolds;
* `BundleConnection.dLoc_curvLoc`: the second Bianchi identity in every trivialization;
* `Connection.curvLoc_transition`: the curvature of a connection on `M` is a tensor.

No completeness of `E` or `F` is assumed.
-/

open Set Function Filter
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

section Calculus

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Product rule for fiber maps**: if `(y, ξ) ↦ G(y) ξ` is `C¹` and linear in `ξ`, then
`d(y ↦ G(y) s(y))(v) = (∂_v G)(y) s(y) + G(y)(ds(y) v)`. -/
theorem dMB_fiber_comp {G : E → F → F} {s : E → F} {T U : Set E} (hT : IsOpen T)
    (hU : IsOpen U) (hUT : U ⊆ T)
    (hG : ContDiffMBOn 1 (fun p : E × F ↦ G p.1 p.2) (T ×ˢ univ))
    (hadd : ∀ y ∈ T, ∀ ξ η, G y (ξ + η) = G y ξ + G y η)
    (hsmul : ∀ y ∈ T, ∀ (c : ℝ) ξ, G y (c • ξ) = c • G y ξ)
    (hs : ContDiffMBOn 1 s U) {y : E} (hy : y ∈ U) (v : E) :
    dMB (fun z ↦ G z (s z)) (y, v) = dMB (fun z ↦ G z (s y)) (y, v) + G y (dMB s (y, v)) := by
  have hTU : IsOpen (T ×ˢ (univ : Set F)) := hT.prod isOpen_univ
  have hpair : ContDiffMBOn 1 (fun z ↦ (z, s z)) U :=
    ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU hs
  have hcomp := ContDiffMBOn.dMB_comp (g := fun p : E × F ↦ G p.1 p.2) hTU hG hpair
    (fun z hz ↦ ⟨hUT hz, mem_univ _⟩) hy v
  have hdpair : dMB (fun z ↦ (z, s z)) (y, v) = (v, dMB s (y, v)) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt y v).prodMk (hs.hasDirDerivAt hy v)).dMB_eq
  have hsplit : (v, dMB s (y, v)) = (v, (0 : F)) + (0, dMB s (y, v)) := by simp
  have hbase : dMB (fun p : E × F ↦ G p.1 p.2) ((y, s y), (v, 0)) =
      dMB (fun z ↦ G z (s y)) (y, v) := by
    simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  have hfib : HasDirDerivAt (fun p : E × F ↦ G p.1 p.2) (y, s y) (0, dMB s (y, v))
      (G y (dMB s (y, v))) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hadd y (hUT hy),
      hsmul y (hUT hy), add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  change dMB ((fun p : E × F ↦ G p.1 p.2) ∘ fun z ↦ (z, s z)) (y, v) = _
  rw [hcomp, hdpair, hsplit, hG.dMB_add hTU ⟨hUT hy, mem_univ _⟩, hbase, hfib.dMB_eq]

/-- The local covariant derivative of a section: `∇_X s = ds · X − Γ(X, s)`. -/
def localCovDerivB (Γ : E → E → F → F) (X : E → E) (s : E → F) (y : E) : F :=
  dMB s (y, X y) - Γ y (X y) (s y)

/-- **The covariant derivative of sections transforms covariantly**: if the symbols obey the gauge
transformation law, `Xⱼ(τ y) = dτ(y) Xᵢ(y)` and `sⱼ ∘ τ = g · sᵢ`, then
`∇_{Xⱼ} sⱼ(τ y) = g(y) ∇_{Xᵢ} sᵢ(y)`. -/
theorem localCovDerivB_transition {τ : E → E} {G : E → F → F} {Γᵢ Γⱼ : E → E → F → F}
    {Xᵢ Xⱼ : E → E} {sᵢ sⱼ : E → F} {T U V : Set E} (hT : IsOpen T) (hU : IsOpen U)
    (hV : IsOpen V) (hUT : U ⊆ T) (hτ : ContDiffMBOn 1 τ T) (hUV : MapsTo τ U V)
    (hG : ContDiffMBOn 1 (fun p : E × F ↦ G p.1 p.2) (T ×ˢ univ))
    (hadd : ∀ y ∈ T, ∀ ξ η, G y (ξ + η) = G y ξ + G y η)
    (hsmul : ∀ y ∈ T, ∀ (c : ℝ) ξ, G y (c • ξ) = c • G y ξ)
    (hsᵢ : ContDiffMBOn 1 sᵢ U) (hsⱼ : ContDiffMBOn 1 sⱼ V)
    (hΓ : ∀ y ∈ U, ∀ a ξ, Γⱼ (τ y) (dMB τ (y, a)) (G y ξ) =
      G y (Γᵢ y a ξ) + dMB (fun z ↦ G z ξ) (y, a))
    {y : E} (hy : y ∈ U) (hX : Xⱼ (τ y) = dMB τ (y, Xᵢ y))
    (hs : ∀ y ∈ U, sⱼ (τ y) = G y (sᵢ y)) :
    localCovDerivB Γⱼ Xⱼ sⱼ (τ y) = G y (localCovDerivB Γᵢ Xᵢ sᵢ y) := by
  have hev : sⱼ ∘ τ =ᶠ[𝓝 y] fun z ↦ G z (sᵢ z) :=
    eventuallyEq_of_mem (hU.mem_nhds hy) fun z hz ↦ hs z hz
  have hd : dMB sⱼ (τ y, dMB τ (y, Xᵢ y)) =
      dMB (fun z ↦ G z (sᵢ y)) (y, Xᵢ y) + G y (dMB sᵢ (y, Xᵢ y)) := by
    rw [← ContDiffMBOn.dMB_comp hV hsⱼ (hτ.mono hUT) hUV hy, dMB_congr_of_eventuallyEq hev,
      dMB_fiber_comp hT hU hUT hG hadd hsmul hsᵢ hy]
  have hsub : G y (dMB sᵢ (y, Xᵢ y) - Γᵢ y (Xᵢ y) (sᵢ y)) =
      G y (dMB sᵢ (y, Xᵢ y)) - G y (Γᵢ y (Xᵢ y) (sᵢ y)) := by
    have h := hadd y (hUT hy) (dMB sᵢ (y, Xᵢ y) - Γᵢ y (Xᵢ y) (sᵢ y)) (Γᵢ y (Xᵢ y) (sᵢ y))
    rw [sub_add_cancel] at h
    rw [h]
    abel
  rw [localCovDerivB, localCovDerivB, hX, hd, hs y hy, hΓ y hy, hsub]
  abel

namespace IsLocalSymbol

variable {Γ : E → E → F → F} {U : Set E}

/-- **Product rule for the symbols**: the derivative of `y ↦ Γ(y)(A y, B y)` is
`∂_v Γ(A y, B y) + Γ(dA(y) v, B y) + Γ(A y, dB(y) v)`. -/
theorem dMB_apply (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) {A : E → E} {B : E → F}
    (hA : ContDiffMBOn 1 A U) (hB : ContDiffMBOn 1 B U) {y : E} (hy : y ∈ U) (v : E) :
    dMB (fun z ↦ Γ z (A z) (B z)) (y, v) =
      symbD Γ y v (A y) (B y) + Γ y (dMB A (y, v)) (B y) + Γ y (A y) (dMB B (y, v)) := by
  have hUU : IsOpen (U ×ˢ (univ : Set (E × F))) := hU.prod isOpen_univ
  have hΓ1 : ContDiffMBOn 1 (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ) := hΓ.smooth 1
  have htrip : ContDiffMBOn 1 (fun z ↦ (z, (A z, B z))) U :=
    ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU (hA.prodMk hU hB)
  have hcomp := ContDiffMBOn.dMB_comp (g := fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2)
    (f := fun z ↦ (z, (A z, B z))) hUU hΓ1 htrip (fun z hz ↦ ⟨hz, mem_univ _⟩) hy v
  have hdtrip : dMB (fun z ↦ (z, (A z, B z))) (y, v) = (v, (dMB A (y, v), dMB B (y, v))) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt y v).prodMk
      ((hA.hasDirDerivAt hy v).prodMk (hB.hasDirDerivAt hy v))).dMB_eq
  have hsplit : (v, (dMB A (y, v), dMB B (y, v))) =
      ((v, ((0 : E), (0 : F))) + ((0 : E), (dMB A (y, v), (0 : F)))) +
        ((0 : E), ((0 : E), dMB B (y, v))) := by simp
  have hp : (y, (A y, B y)) ∈ U ×ˢ (univ : Set (E × F)) := ⟨hy, mem_univ _⟩
  have hbase : dMB (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) ((y, (A y, B y)), (v, (0, 0))) =
      symbD Γ y v (A y) (B y) := by
    simp only [symbD, dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  have hleft : HasDirDerivAt (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (y, (A y, B y))
      (0, (dMB A (y, v), 0)) (Γ y (dMB A (y, v)) (B y)) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hΓ.add_left, hΓ.smul_left,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hright : HasDirDerivAt (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (y, (A y, B y))
      (0, (0, dMB B (y, v))) (Γ y (A y) (dMB B (y, v))) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hΓ.add_right, hΓ.smul_right,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  change dMB ((fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) ∘ fun z ↦ (z, (A z, B z))) (y, v) = _
  rw [hcomp, hdtrip, hsplit, hΓ1.dMB_add hUU hp, hΓ1.dMB_add hUU hp, hbase, hleft.dMB_eq,
    hright.dMB_eq]

/-- **The local curvature formula for vector bundles**: for `C²` fields and sections,
`∇_X ∇_Y s − ∇_Y ∇_X s − ∇_[X,Y] s = Ω(X, Y) s` pointwise. -/
theorem localCovDerivB_curv (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) {X Y : E → E} {s : E → F}
    (hX : ContDiffMBOn 2 X U) (hY : ContDiffMBOn 2 Y U) (hs : ContDiffMBOn 2 s U) {y : E}
    (hy : y ∈ U) :
    localCovDerivB Γ X (localCovDerivB Γ Y s) y - localCovDerivB Γ Y (localCovDerivB Γ X s) y -
        localCovDerivB Γ (localBracket X Y) s y =
      bundleCurv Γ y (X y) (Y y) (s y) := by
  have hUU : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hW : ∀ {A : E → E}, ContDiffMBOn 2 A U → ∀ v,
      dMB (localCovDerivB Γ A s) (y, v) =
        (dMB (dMB s) ((y, A y), (v, 0)) + dMB s (y, dMB A (y, v))) -
          (symbD Γ y v (A y) (s y) + Γ y (dMB A (y, v)) (s y) + Γ y (A y) (dMB s (y, v))) := by
    intro A hA v
    have hA1 : ContDiffMBOn 1 A U := hA.of_le (by norm_num)
    have hs1 : ContDiffMBOn 1 s U := hs.of_le (by norm_num)
    have hpair : ContDiffMBOn 1 (fun y' ↦ (y', A y')) U :=
      ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU hA1
    have hds : ContDiffMBOn 1 (dMB s) (U ×ˢ univ) := hs.2.2
    have hc1 : ContDiffMBOn 1 (fun y' ↦ dMB s (y', A y')) U :=
      ContDiffMBOn.comp (g := dMB s) (f := fun y' ↦ (y', A y')) hU hUU hds hpair
        fun y' hy' ↦ ⟨hy', mem_univ _⟩
    have hc2 : ContDiffMBOn 1 (fun y' ↦ Γ y' (A y') (s y')) U :=
      hΓ.contDiffMBOn_comp hU ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U) hA1 hs1 hU
        fun _ h ↦ h
    have h1 := hc1.hasDirDerivAt (k := 0) hy v
    have h2 := hc2.hasDirDerivAt (k := 0) hy v
    change dMB (fun y' ↦ dMB s (y', A y') - Γ y' (A y') (s y')) (y, v) = _
    rw [(h1.sub h2).dMB_eq, dMB_dMB_comp_apply hU hU subset_rfl hs hA1 hy,
      hΓ.dMB_apply hU hA1 hs1 hy]
  obtain ⟨Ls, hLs⟩ := (hs.of_le (by norm_num) : ContDiffMBOn 1 s U).exists_clm hU hy
  have e1 : localCovDerivB Γ X (localCovDerivB Γ Y s) y =
      dMB (localCovDerivB Γ Y s) (y, X y) - Γ y (X y) (localCovDerivB Γ Y s y) := rfl
  have e2 : localCovDerivB Γ Y (localCovDerivB Γ X s) y =
      dMB (localCovDerivB Γ X s) (y, Y y) - Γ y (Y y) (localCovDerivB Γ X s y) := rfl
  have e3 : localCovDerivB Γ (localBracket X Y) s y =
      dMB s (y, localBracket X Y y) - Γ y (localBracket X Y y) (s y) := rfl
  have hsubl : ∀ x a a' ξ, Γ x (a - a') ξ = Γ x a ξ - Γ x a' ξ := fun x a a' ξ ↦ by
    rw [sub_eq_add_neg, hΓ.add_left, ← neg_one_smul ℝ a', hΓ.smul_left, neg_one_smul,
      ← sub_eq_add_neg]
  rw [e1, e2, e3, hW hY, hW hX, hs.dMB_dMB_symm hU hy (Y y) (X y)]
  simp only [localCovDerivB, localBracket, bundleCurv, hsubl, hΓ.sub_right, ← hLs, map_sub]
  abel

/-- The covariant derivative of a `C^{k+1}` section along a `C^k` field is `C^k`. -/
theorem contDiffMBOn_localCovDerivB (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) {X : E → E}
    {s : E → F} {k : ℕ} (hX : ContDiffMBOn k X U) (hs : ContDiffMBOn (k + 1) s U) :
    ContDiffMBOn k (localCovDerivB Γ X s) U := by
  have hUU : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hds : ContDiffMBOn k (dMB s) (U ×ˢ univ) := hs.2.2
  have h1 : ContDiffMBOn k (fun y ↦ dMB s (y, X y)) U :=
    ContDiffMBOn.comp (g := dMB s) (f := fun y ↦ (y, X y)) hU hUU hds
      (((ContinuousLinearMap.id ℝ E).contDiffMBOn k U).prodMk hU hX) fun y hy ↦ ⟨hy, mem_univ _⟩
  have h2 : ContDiffMBOn k (fun y ↦ Γ y (X y) (s y)) U :=
    hΓ.contDiffMBOn_comp hU ((ContinuousLinearMap.id ℝ E).contDiffMBOn k U) hX
      (hs.of_le (by omega)) hU fun _ h ↦ h
  have hsub := ContDiffMBOn.comp (F₁ := F × F) hU isOpen_univ
    ((ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
    (h1.prodMk hU h2) (mapsTo_univ _ _)
  exact ContDiffMBOn.congr_of_isOpen hU (fun y _ ↦ by simp [localCovDerivB]) hsub

end IsLocalSymbol

/-- **The curvature is a tensor** (local form). Let `τ : U → V` be smooth with smooth left
inverse `σ : V → U`, let `(y, ξ) ↦ G(y) ξ` be smooth and linear in `ξ`, and let the symbols
`Γᵢ` on `U` and `Γⱼ` on `V` be related by the gauge transformation law. Then
`Ωⱼ(τ y)(dτ u, dτ v)(G(y) ξ) = G(y) Ωᵢ(y)(u, v) ξ`.

The proof applies the curvature formula `localCovDerivB_curv` to the constant fields `u`, `v`
and the constant section `ξ` on `U`, and to their images `dτ(σ z) u`, `dτ(σ z) v`,
`G(σ z) ξ` on `V`, and uses that covariant derivatives and brackets transform covariantly. -/
theorem curvature_gauge {τ σ : E → E} {G : E → F → F} {Γᵢ Γⱼ : E → E → F → F} {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hτ : SmoothMBOn τ U) (hσ : SmoothMBOn σ V)
    (hτUV : MapsTo τ U V) (hσVU : MapsTo σ V U) (hστ : ∀ y ∈ U, σ (τ y) = y)
    (hG : SmoothMBOn (fun p : E × F ↦ G p.1 p.2) (U ×ˢ univ))
    (hadd : ∀ y ∈ U, ∀ ξ η, G y (ξ + η) = G y ξ + G y η)
    (hsmul : ∀ y ∈ U, ∀ (c : ℝ) ξ, G y (c • ξ) = c • G y ξ)
    (hΓᵢ : IsLocalSymbol Γᵢ U) (hΓⱼ : IsLocalSymbol Γⱼ V)
    (hΓ : ∀ y ∈ U, ∀ a ξ, Γⱼ (τ y) (dMB τ (y, a)) (G y ξ) =
      G y (Γᵢ y a ξ) + dMB (fun z ↦ G z ξ) (y, a))
    {y : E} (hy : y ∈ U) (u v : E) (ξ : F) :
    bundleCurv Γⱼ (τ y) (dMB τ (y, u)) (dMB τ (y, v)) (G y ξ) = G y (bundleCurv Γᵢ y u v ξ) := by
  have hUU : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hUF : IsOpen (U ×ˢ (univ : Set F)) := hU.prod isOpen_univ
  have hsub : ∀ z ∈ U, ∀ ξ η, G z (ξ - η) = G z ξ - G z η := fun z hz ξ η ↦ by
    have h := hadd z hz (ξ - η) η
    rw [sub_add_cancel] at h
    rw [h]
    abel
  -- the fields and sections in the two charts
  set Xᵢ : E → E := fun _ ↦ u
  set Yᵢ : E → E := fun _ ↦ v
  set sᵢ : E → F := fun _ ↦ ξ
  set Xⱼ : E → E := fun z ↦ dMB τ (σ z, u)
  set Yⱼ : E → E := fun z ↦ dMB τ (σ z, v)
  set sⱼ : E → F := fun z ↦ G (σ z) ξ
  have hdτ : ∀ k, ContDiffMBOn k (dMB τ) (U ×ˢ univ) := fun k ↦ (hτ (k + 1)).2.2
  have hvec : ∀ (w : E) k, ContDiffMBOn k (fun z ↦ dMB τ (σ z, w)) V := fun w k ↦
    ContDiffMBOn.comp (g := dMB τ) (f := fun z ↦ (σ z, w)) hV hUU (hdτ k)
      ((hσ k).prodMk hV (contDiffMBOn_const k w V)) fun z hz ↦ ⟨hσVU hz, mem_univ _⟩
  have hXⱼ : ∀ k, ContDiffMBOn k Xⱼ V := hvec u
  have hYⱼ : ∀ k, ContDiffMBOn k Yⱼ V := hvec v
  have hsⱼ : ∀ k, ContDiffMBOn k sⱼ V := fun k ↦
    ContDiffMBOn.comp (g := fun p : E × F ↦ G p.1 p.2) (f := fun z ↦ (σ z, ξ)) hV hUF (hG k)
      ((hσ k).prodMk hV (contDiffMBOn_const k ξ V)) fun z hz ↦ ⟨hσVU hz, mem_univ _⟩
  have hXᵢ : ∀ k, ContDiffMBOn k Xᵢ U := fun k ↦ contDiffMBOn_const k u U
  have hYᵢ : ∀ k, ContDiffMBOn k Yᵢ U := fun k ↦ contDiffMBOn_const k v U
  have hsᵢ : ∀ k, ContDiffMBOn k sᵢ U := fun k ↦ contDiffMBOn_const k ξ U
  have hXrel : ∀ z ∈ U, Xⱼ (τ z) = dMB τ (z, Xᵢ z) := fun z hz ↦ by simp [Xⱼ, Xᵢ, hστ z hz]
  have hYrel : ∀ z ∈ U, Yⱼ (τ z) = dMB τ (z, Yᵢ z) := fun z hz ↦ by simp [Yⱼ, Yᵢ, hστ z hz]
  have hsrel : ∀ z ∈ U, sⱼ (τ z) = G z (sᵢ z) := fun z hz ↦ by simp [sⱼ, sᵢ, hστ z hz]
  -- covariant derivatives transform covariantly
  have htr : ∀ {Aᵢ Aⱼ : E → E} {tᵢ tⱼ : E → F}, ContDiffMBOn 1 tᵢ U → ContDiffMBOn 1 tⱼ V →
      (∀ z ∈ U, tⱼ (τ z) = G z (tᵢ z)) → ∀ z ∈ U, Aⱼ (τ z) = dMB τ (z, Aᵢ z) →
      localCovDerivB Γⱼ Aⱼ tⱼ (τ z) = G z (localCovDerivB Γᵢ Aᵢ tᵢ z) :=
    fun htᵢ htⱼ hrel z hz hA ↦ localCovDerivB_transition hU hU hV subset_rfl (hτ 1) hτUV (hG 1)
      hadd hsmul htᵢ htⱼ hΓ hz hA hrel
  have hrelX : ∀ z ∈ U, localCovDerivB Γⱼ Xⱼ sⱼ (τ z) = G z (localCovDerivB Γᵢ Xᵢ sᵢ z) :=
    fun z hz ↦ htr (hsᵢ 1) (hsⱼ 1) hsrel z hz (hXrel z hz)
  have hrelY : ∀ z ∈ U, localCovDerivB Γⱼ Yⱼ sⱼ (τ z) = G z (localCovDerivB Γᵢ Yᵢ sᵢ z) :=
    fun z hz ↦ htr (hsᵢ 1) (hsⱼ 1) hsrel z hz (hYrel z hz)
  have h1 := htr (hΓᵢ.contDiffMBOn_localCovDerivB hU (hXᵢ 1) (hsᵢ 2))
    (hΓⱼ.contDiffMBOn_localCovDerivB hV (hXⱼ 1) (hsⱼ 2)) hrelX y hy (hYrel y hy)
  have h2 := htr (hΓᵢ.contDiffMBOn_localCovDerivB hU (hYᵢ 1) (hsᵢ 2))
    (hΓⱼ.contDiffMBOn_localCovDerivB hV (hYⱼ 1) (hsⱼ 2)) hrelY y hy (hXrel y hy)
  have hbr : localBracket Xⱼ Yⱼ (τ y) = dMB τ (y, localBracket Xᵢ Yᵢ y) :=
    localBracket_transition hU hU hV subset_rfl (hτ 2) hτUV (hXᵢ 1) (hYᵢ 1) (hXⱼ 1) (hYⱼ 1)
      hXrel hYrel hy
  have h3 := htr (hsᵢ 1) (hsⱼ 1) hsrel y hy hbr
  have cⱼ := hΓⱼ.localCovDerivB_curv hV (hXⱼ 2) (hYⱼ 2) (hsⱼ 2) (hτUV hy)
  have cᵢ := hΓᵢ.localCovDerivB_curv hU (hXᵢ 2) (hYᵢ 2) (hsᵢ 2) hy
  rw [h1, h2, h3, ← hsub _ hy, ← hsub _ hy, cᵢ, hXrel y hy, hYrel y hy, hsrel y hy] at cⱼ
  exact cⱼ.symm

end Calculus

theorem IsLocalSymbol.mono {E F : Type u}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {Γ : E → E → F → F}
    {U U' : Set E} (hΓ : IsLocalSymbol Γ U) (h : U' ⊆ U) : IsLocalSymbol Γ U' :=
  ⟨fun k ↦ (hΓ.smooth k).mono (prod_mono h subset_rfl), hΓ.add_left, hΓ.smul_left,
    hΓ.add_right, hΓ.smul_right⟩

/-! ### Connections on vector bundles -/

section Global

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- A **connection on a vector bundle** `V`: symbols `Γᵢ` in the trivialization over each chart,
subject to the gauge transformation law
`Γⱼ(τ y)(dτ(y) a, g(y) ξ) = g(y) Γᵢ(y)(a, ξ) + (∂_a g)(y) ξ`, with `τ = j ∘ i⁻¹` and
`g(y) = g_{ij}(i⁻¹ y)`. -/
structure BundleConnection (V : MBVectorBundleCore E M F) where
  /-- The symbols in the trivialization over the chart `i`. -/
  Γ : atlas E M → E → E → F → F
  isLocalSymbol : ∀ i, IsLocalSymbol (Γ i) i.1.target
  transition : ∀ i j : atlas E M, ∀ y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source, ∀ a ξ,
    Γ j ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, a)) (V.coordChange i j (i.1.symm y) ξ) =
      V.coordChange i j (i.1.symm y) (Γ i y a ξ) +
        dMB (fun z ↦ V.coordChange i j (i.1.symm z) ξ) (y, a)

namespace BundleConnection

variable {V : MBVectorBundleCore E M F} (C : BundleConnection V)

/-- **The curvature of a connection on a vector bundle is a tensor**: with `τ = j ∘ i⁻¹` and
`g(y) = g_{ij}(i⁻¹ y)`, `Ωⱼ(τ y)(dτ u, dτ v)(g ξ) = g Ωᵢ(y)(u, v) ξ`. -/
theorem curvLoc_transition (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (u v : E) (ξ : F) :
    bundleCurv (C.Γ j) ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, u))
        (dMB (j.1 ∘ i.1.symm) (y, v)) (V.coordChange i j (i.1.symm y) ξ) =
      V.coordChange i j (i.1.symm y) (bundleCurv (C.Γ i) y u v ξ) := by
  set U := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  set W := j.1.target ∩ j.1.symm ⁻¹' i.1.source
  have hτUV : MapsTo (j.1 ∘ i.1.symm) U W := fun z hz ↦
    ⟨j.1.map_source hz.2, by simp [j.1.left_inv hz.2, i.1.map_target hz.1]⟩
  have hσVU : MapsTo (i.1 ∘ j.1.symm) W U := fun z hz ↦
    ⟨i.1.map_source hz.2, by simp [i.1.left_inv hz.2, j.1.map_target hz.1]⟩
  have hστ : ∀ z ∈ U, (i.1 ∘ j.1.symm) ((j.1 ∘ i.1.symm) z) = z := fun z hz ↦ by
    simp [j.1.left_inv hz.2, i.1.right_inv hz.1]
  have hlin : ∀ z ∈ U, i.1.symm z ∈ i.1.source ∩ j.1.source := fun z hz ↦
    ⟨i.1.map_target hz.1, hz.2⟩
  exact curvature_gauge (G := fun z ξ ↦ V.coordChange i j (i.1.symm z) ξ)
    (isOpen_transition_domain i j) (isOpen_transition_domain j i)
    (smoothMBOn_transition' i j) (smoothMBOn_transition' j i) hτUV hσVU hστ (V.smooth i j)
    (fun z hz ↦ V.map_add i j _ (hlin z hz)) (fun z hz ↦ V.map_smul i j _ (hlin z hz))
    ((C.isLocalSymbol i).mono inter_subset_left) ((C.isLocalSymbol j).mono inter_subset_left)
    (C.transition i j) hy u v ξ

omit [MBManifold E M] in
/-- **The second Bianchi identity** in every trivialization. -/
theorem dLoc_curvLoc (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (ξ : F) (u v t : E) :
    dLoc (curvLoc (C.Γ i) ξ) (y, ![u, v, t]) =
      (C.Γ i y u (bundleCurv (C.Γ i) y v t ξ) - bundleCurv (C.Γ i) y v t (C.Γ i y u ξ)) -
        (C.Γ i y v (bundleCurv (C.Γ i) y u t ξ) - bundleCurv (C.Γ i) y u t (C.Γ i y v ξ)) +
          (C.Γ i y t (bundleCurv (C.Γ i) y u v ξ) - bundleCurv (C.Γ i) y u v (C.Γ i y t ξ)) :=
  (C.isLocalSymbol i).dLoc_curvLoc i.1.open_target hy ξ u v t

end BundleConnection

namespace Connection

variable (C : Connection E M)

/-- A connection on `M` is a connection on the tangent bundle. -/
def toBundleConnection : BundleConnection (tangentMBCore E M) where
  Γ := C.Γ
  isLocalSymbol i := C.isLocalSymbol i
  transition i j y hy a b := by
    have hev : (fun z ↦ tangentCoordChange i j (i.1.symm z) b) =ᶠ[𝓝 y]
        fun z ↦ dMB (j.1 ∘ i.1.symm) (z, b) :=
      eventuallyEq_of_mem (i.1.open_target.mem_nhds hy.1) fun z hz ↦ by
        simp only [tangentCoordChange, i.1.right_inv hz]
    have hd : dMB (fun z ↦ dMB (j.1 ∘ i.1.symm) (z, b)) (y, a) =
        dMB (dMB (j.1 ∘ i.1.symm)) ((y, b), (a, 0)) := by
      simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
    change C.Γ j _ _ (tangentCoordChange i j (i.1.symm y) b) =
      tangentCoordChange i j (i.1.symm y) (C.Γ i y a b) +
        dMB (fun z ↦ tangentCoordChange i j (i.1.symm z) b) (y, a)
    rw [dMB_congr_of_eventuallyEq hev, hd]
    simp only [tangentCoordChange, i.1.right_inv hy.1]
    exact C.transition i j y hy a b

/-- **The curvature of a connection on `M` is a tensor**: with `τ = j ∘ i⁻¹`,
`Rⱼ(τ y)(dτ u, dτ v)(dτ w) = dτ Rᵢ(y)(u, v) w`. -/
theorem localCurv_transition (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (u v w : E) :
    localCurv (C.Γ j) ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, u))
        (dMB (j.1 ∘ i.1.symm) (y, v)) (dMB (j.1 ∘ i.1.symm) (y, w)) =
      dMB (j.1 ∘ i.1.symm) (y, localCurv (C.Γ i) y u v w) := by
  have h := C.toBundleConnection.curvLoc_transition i j hy u v w
  simp only [toBundleConnection, tangentMBCore, tangentCoordChange, i.1.right_inv hy.1,
    bundleCurv_eq_localCurv] at h
  exact h

end Connection

end Global

end LocallyConvex.Manifolds

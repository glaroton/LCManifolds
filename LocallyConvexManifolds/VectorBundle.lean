/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.TangentBundle

/-!
# Vector bundles

Let `M` be a manifold modeled on a locally convex space `E`, and `F` a locally convex space. A
vector bundle over `M` with fiber `F` is glued from the products `φ(U) × F` along maps
`(y, ξ) ↦ (τ y, g(y) ξ)`, where `τ` runs over the transition maps of the atlas and `g(y)` is
linear. We encode it by its coordinate changes, indexed by the charts of the atlas
(`MBVectorBundleCore`), as Mathlib's `FiberBundleCore`, and require that **the map
`(y, ξ) ↦ g(y) ξ` be smooth on `U × F`**, in the chart coordinates `y`.

**An infinite-dimensional subtlety.** In finite dimensions (and for Banach spaces, with the norm
topology on `L(F)`) one asks the transition functions `y ↦ g(y)` to be smooth maps into
`GL(F)`. If `F` is not normable, no vector topology on `L(F)` makes the evaluation
`L(F) × F → F` continuous, so this requirement is not available; joint smoothness of
`(y, ξ) ↦ g(y) ξ` is the substitute, and it is exactly what the tangent bundle satisfies
(`tangentMBCore`): its coordinate changes are `(y, w) ↦ dτ(y) w`.

The total space is a topological fiber bundle with fiber `F`
(`MBVectorBundleCore.toFiberBundleCore`), and it is a manifold modeled on `E × F`
(`MBVectorBundleCore.mbManifold`), with transition maps `(y, ξ) ↦ (τ y, g(y) ξ)`.

No completeness of `E` or `F` is assumed.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (E M F) in
/-- A **vector bundle** over `M` with fiber `F`, given by its coordinate changes
`g_{ij}(x) : F → F` between the trivializations over the charts `i`, `j` of the atlas: linear on
the overlap `Uᵢ ∩ Uⱼ`, satisfying the cocycle conditions, and such that
`(y, ξ) ↦ g_{ij}(i⁻¹ y) ξ` is smooth on `i(Uᵢ ∩ Uⱼ) × F`. -/
structure MBVectorBundleCore where
  /-- The coordinate change `g_{ij}(x)` from the trivialization over `i` to the one over `j`. -/
  coordChange : atlas E M → atlas E M → M → F → F
  map_add : ∀ i j x, x ∈ i.1.source ∩ j.1.source → ∀ ξ η,
    coordChange i j x (ξ + η) = coordChange i j x ξ + coordChange i j x η
  map_smul : ∀ i j x, x ∈ i.1.source ∩ j.1.source → ∀ (c : ℝ) ξ,
    coordChange i j x (c • ξ) = c • coordChange i j x ξ
  coordChange_self : ∀ i x, x ∈ i.1.source → ∀ ξ, coordChange i i x ξ = ξ
  coordChange_comp : ∀ i j k x, x ∈ i.1.source ∩ j.1.source ∩ k.1.source → ∀ ξ,
    coordChange j k x (coordChange i j x ξ) = coordChange i k x ξ
  smooth : ∀ i j, SmoothMBOn (fun p : E × F ↦ coordChange i j (i.1.symm p.1) p.2)
    ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ)

namespace MBVectorBundleCore

variable (V : MBVectorBundleCore E M F)

/-- The coordinate change over a point of the overlap, as a linear map. -/
def coordChangeLinear (i j : atlas E M) {x : M} (hx : x ∈ i.1.source ∩ j.1.source) :
    F →ₗ[ℝ] F where
  toFun := V.coordChange i j x
  map_add' := V.map_add i j x hx
  map_smul' := V.map_smul i j x hx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem continuousOn_coordChange (i j : atlas E M) :
    ContinuousOn (fun p : M × F ↦ V.coordChange i j p.1 p.2)
      ((i.1.source ∩ j.1.source) ×ˢ univ) := by
  have hd : ContinuousOn (fun p : E × F ↦ V.coordChange i j (i.1.symm p.1) p.2)
      ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ) :=
    (V.smooth i j 0 : ContDiffMBOn 0 _ _)
  have hfst : ContinuousOn (fun p : M × F ↦ i.1 p.1) ((i.1.source ∩ j.1.source) ×ˢ univ) :=
    i.1.continuousOn.comp continuousOn_fst fun p hp ↦ hp.1.1
  refine (hd.comp (hfst.prodMk continuousOn_snd) ?_).congr fun p hp ↦ ?_
  · rintro ⟨x, v⟩ ⟨⟨hi, hj⟩, -⟩
    exact ⟨⟨i.1.map_source hi, by simp [i.1.left_inv hi, hj]⟩, mem_univ _⟩
  · simp [i.1.left_inv hp.1.1]

/-- The underlying topological fiber bundle core. -/
def toFiberBundleCore : FiberBundleCore (atlas E M) M F where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt x := ⟨chartAt E x, chart_mem_atlas E x⟩
  mem_baseSet_at x := mem_chart_source E x
  coordChange := V.coordChange
  coordChange_self i x hx ξ := V.coordChange_self i x hx ξ
  continuousOn_coordChange := V.continuousOn_coordChange
  coordChange_comp i j k x hx ξ := V.coordChange_comp i j k x hx ξ

/-- The total space of the bundle. -/
abbrev TotalSpace : Type _ := V.toFiberBundleCore.TotalSpace

instance : ChartedSpace (E × F) V.TotalSpace :=
  FiberBundle.chartedSpace (HB := E)

/-- The chart of the total space built from the trivialization over the chart `i` and the
chart `c` of the base. -/
def bundleChart (i : atlas E M) (c : OpenPartialHomeomorph M E) :
    OpenPartialHomeomorph V.TotalSpace (E × F) :=
  (V.toFiberBundleCore.localTriv i).toOpenPartialHomeomorph ≫ₕ
    c.prod (OpenPartialHomeomorph.refl F)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem bundleChart_apply (i : atlas E M) (c : OpenPartialHomeomorph M E) (p : V.TotalSpace) :
    V.bundleChart i c p =
      (c p.1, V.coordChange ⟨chartAt E p.1, chart_mem_atlas E p.1⟩ i p.1 p.2) :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem bundleChart_symm_proj (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × F) :
    ((V.bundleChart i c).symm q).proj = c.symm q.1 :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem bundleChart_symm_snd (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × F) :
    (((V.bundleChart i c).symm q).2 : F) =
      V.coordChange i ⟨chartAt E (c.symm q.1), chart_mem_atlas E _⟩ (c.symm q.1) q.2 :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem mem_bundleChart_source (i : atlas E M) (c : OpenPartialHomeomorph M E)
    (p : V.TotalSpace) :
    p ∈ (V.bundleChart i c).source ↔ p.1 ∈ i.1.source ∧ p.1 ∈ c.source := by
  simp only [bundleChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_prod, mem_univ,
    and_true, Trivialization.coe_coe, FiberBundleCore.localTriv_apply,
    FiberBundleCore.mem_localTriv_source]
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem mem_bundleChart_target (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × F) :
    q ∈ (V.bundleChart i c).target ↔ q.1 ∈ c.target ∧ c.symm q.1 ∈ i.1.source := by
  simp only [bundleChart, OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target, mem_prod, mem_univ,
    and_true, OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_symm, FiberBundleCore.mem_localTriv_target]
  rfl

/-- The transition maps of the total space are `(y, ξ) ↦ (τ y, g(c⁻¹ y) ξ)`; they are smooth. -/
theorem smoothMBOn_bundleChart_transition (i j : atlas E M) {c c' : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    SmoothMBOn ⇑((V.bundleChart i c).symm ≫ₕ V.bundleChart j c')
      ((V.bundleChart i c).symm ≫ₕ V.bundleChart j c').source := by
  set ψ := V.bundleChart i c
  set ψ' := V.bundleChart j c'
  set D := c.target ∩ c.symm ⁻¹' (i.1.source ∩ j.1.source ∩ c'.source)
  have hD : IsOpen D := c.isOpen_inter_preimage_symm
    ((i.1.open_source.inter j.1.open_source).inter c'.open_source)
  have hDU : IsOpen (D ×ˢ (univ : Set F)) := hD.prod isOpen_univ
  have hsrc : (ψ.symm ≫ₕ ψ').source ⊆ D ×ˢ univ := by
    rintro q ⟨hq, hq'⟩
    replace hq : q ∈ ψ.target := hq
    rw [mem_bundleChart_target] at hq
    rw [mem_preimage, mem_bundleChart_source] at hq'
    simp only [OpenPartialHomeomorph.symm_symm] at hq'
    exact ⟨⟨hq.1, ⟨hq.2, hq'.1⟩, hq'.2⟩, mem_univ _⟩
  set G : E × F → E × F := fun q ↦
    (c' (c.symm q.1), V.coordChange i j (i.1.symm (i.1 (c.symm q.1))) q.2)
  have hG : ∀ q ∈ D ×ˢ (univ : Set F), (ψ.symm ≫ₕ ψ') q = G q := by
    rintro q ⟨⟨-, ⟨hi, hj⟩, -⟩, -⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, bundleChart_apply,
      bundleChart_symm_proj, bundleChart_symm_snd,
      V.coordChange_comp i _ j _ ⟨⟨hi, mem_chart_source E _⟩, hj⟩]
    simp only [G, i.1.left_inv hi]
  intro k
  refine ContDiffMBOn.congr_of_isOpen (ψ.symm ≫ₕ ψ').open_source
    (fun q hq ↦ (hG q (hsrc hq)).symm) (ContDiffMBOn.mono ?_ hsrc)
  have hfst : ContDiffMBOn k (ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
    (ContinuousLinearMap.fst ℝ E F).contDiffMBOn k _
  have hsnd : ContDiffMBOn k (ContinuousLinearMap.snd ℝ E F) (D ×ˢ univ) :=
    (ContinuousLinearMap.snd ℝ E F).contDiffMBOn k _
  have h1 : ContDiffMBOn k ((c' ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
    (smoothMBOn_transition hc hc' k).comp hDU (c.isOpen_inter_preimage_symm c'.open_source)
      hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.2⟩
  have hic : ContDiffMBOn k ((i.1 ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
    (smoothMBOn_transition hc i.2 k).comp hDU (c.isOpen_inter_preimage_symm i.1.open_source)
      hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.1.1⟩
  have hφ := hic.prodMk hDU hsnd
  have h2 := (V.smooth i j k).comp hDU ((isOpen_transition_domain i j).prod isOpen_univ) hφ
    fun q hq ↦ ⟨⟨i.1.map_source hq.1.2.1.1, by
      simp [i.1.left_inv hq.1.2.1.1, hq.1.2.1.2]⟩, mem_univ _⟩
  exact h1.prodMk hDU h2

theorem bundleChart_transition_mem (i j : atlas E M) {c c' : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    (V.bundleChart i c).symm ≫ₕ V.bundleChart j c' ∈ mbGroupoid (E × F) := by
  refine ⟨V.smoothMBOn_bundleChart_transition i j hc hc', ?_⟩
  have h := V.smoothMBOn_bundleChart_transition j i hc' hc
  rw [OpenPartialHomeomorph.trans_source] at h
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h

/-- The total space of a vector bundle with fiber `F` over a manifold modeled on `E` is a
manifold modeled on `E × F`. -/
instance mbManifold : MBManifold (E × F) V.TotalSpace where
  compatible := by
    rintro _ _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨c, hc, r, hr, rfl⟩, rfl⟩
      ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, _, ⟨c', hc', r', hr', rfl⟩, rfl⟩
    rw [chartedSpaceSelf_atlas] at hr hr'
    subst hr hr'
    exact V.bundleChart_transition_mem i j hc hc'

end MBVectorBundleCore

variable (E M) in
/-- **The tangent bundle is a vector bundle**: its coordinate changes are the derivatives of the
transition maps, `(y, w) ↦ dτ(y) w`. -/
def tangentMBCore : MBVectorBundleCore E M E where
  coordChange := tangentCoordChange
  map_add i j x hx v w :=
    (smoothMBOn_transition' i j 1).dMB_add (isOpen_transition_domain i j)
      ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ v w
  map_smul i j x hx c v :=
    (smoothMBOn_transition' i j 1).dMB_smul
      ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ c v
  coordChange_self i x hx v := tangentCoordChange_self i hx v
  coordChange_comp i j k x hx v := tangentCoordChange_comp i j k hx v
  smooth i j k := by
    refine ContDiffMBOn.congr_of_isOpen ((isOpen_transition_domain i j).prod isOpen_univ)
      (fun p hp ↦ ?_) ((smoothMBOn_transition' i j (k + 1)).2.2)
    simp only [tangentCoordChange, i.1.right_inv hp.1.1]

end LocallyConvex.Manifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.TangentBundle

/-!
# Vector bundles

Let `M` be a manifold modeled on a locally convex space `E`, and `F` a locally convex space. A
vector bundle over `M` with fiber `F` is glued from products `Uᵢ × F` over the open sets of a
cover of `M`, along maps `(x, ξ) ↦ (x, g_{ij}(x) ξ)` with `g_{ij}(x)` linear.

The open sets of the cover are indexed by an arbitrary type `ι`, and each one comes with a chart
of the atlas defined on it (`TrivializationCover`); in these coordinates the bundle is glued
from the open sets `φᵢ(Uᵢ) × F ⊆ E × F`. We encode the bundle by its coordinate changes
(`MBVectorBundleCore`), as Mathlib's `FiberBundleCore`, and require that **the map
`(y, ξ) ↦ g_{ij}(φᵢ⁻¹ y) ξ` be smooth on `φᵢ(Uᵢ ∩ Uⱼ) × F`**.

The cover is not required to be the atlas of `M`: the pullback `f*V` of a bundle along a smooth
map `f : N → M` is trivial over the sets `k.source ∩ f⁻¹(Uᵢ)`, with `k` a chart of `N`, but in
general not over the chart domains of `N` (`MBVectorBundleCore.pullback`). The tangent bundle is
trivialized over the charts of the atlas (`tangentMBCore`).

**An infinite-dimensional subtlety.** In finite dimensions (and for Banach spaces, with the norm
topology on `L(F)`) one asks the transition functions `x ↦ g_{ij}(x)` to be smooth maps into
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

universe u v w

section Cover

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

variable (E M) in
/-- A **cover of `M` by trivializing sets**, indexed by a type `ι`: open sets `Uᵢ`, each
contained in the source of a chart `φᵢ` of the atlas, and a choice of a set `U_{i(x)}`
containing each point `x`. -/
structure TrivializationCover (ι : Type w) where
  /-- The chart of the atlas attached to the index `i`. -/
  chart : ι → atlas E M
  /-- The open set `Uᵢ`. -/
  baseSet : ι → Set M
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  baseSet_subset : ∀ i, baseSet i ⊆ (chart i).1.source
  /-- A chosen index `i(x)` with `x ∈ U_{i(x)}`. -/
  indexAt : M → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)

namespace TrivializationCover

variable {ι : Type w} (𝒰 : TrivializationCover E M ι)

/-- The open set `φᵢ(Uᵢ) ⊆ E` of the local coordinates over `i`. -/
def domain (i : ι) : Set E :=
  (𝒰.chart i).1.target ∩ (𝒰.chart i).1.symm ⁻¹' 𝒰.baseSet i

/-- The open set `φᵢ(Uᵢ ∩ Uⱼ) ⊆ E`, the domain of the coordinate change from `i` to `j`. -/
def transDomain (i j : ι) : Set E :=
  (𝒰.chart i).1.target ∩ (𝒰.chart i).1.symm ⁻¹' (𝒰.baseSet i ∩ 𝒰.baseSet j)

/-- The change of coordinates `φⱼ ∘ φᵢ⁻¹`. -/
def trans (i j : ι) : E → E :=
  (𝒰.chart j).1 ∘ (𝒰.chart i).1.symm

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem isOpen_domain (i : ι) : IsOpen (𝒰.domain i) :=
  (𝒰.chart i).1.isOpen_inter_preimage_symm (𝒰.isOpen_baseSet i)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem isOpen_transDomain (i j : ι) : IsOpen (𝒰.transDomain i j) :=
  (𝒰.chart i).1.isOpen_inter_preimage_symm ((𝒰.isOpen_baseSet i).inter (𝒰.isOpen_baseSet j))

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem transDomain_subset_domain (i j : ι) : 𝒰.transDomain i j ⊆ 𝒰.domain i :=
  fun _ hy ↦ ⟨hy.1, hy.2.1⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem symm_mem_source {i : ι} {y : E} (hy : y ∈ 𝒰.domain i) :
    (𝒰.chart i).1.symm y ∈ (𝒰.chart i).1.source :=
  (𝒰.chart i).1.map_target hy.1

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
/-- A point of `Uᵢ` is sent into `φᵢ(Uᵢ)`. -/
theorem chart_mem_domain {i : ι} {x : M} (hx : x ∈ 𝒰.baseSet i) :
    (𝒰.chart i).1 x ∈ 𝒰.domain i :=
  ⟨(𝒰.chart i).1.map_source (𝒰.baseSet_subset i hx), by
    rw [mem_preimage, (𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hx)]; exact hx⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem chart_mem_transDomain {i j : ι} {x : M} (hi : x ∈ 𝒰.baseSet i)
    (hj : x ∈ 𝒰.baseSet j) : (𝒰.chart i).1 x ∈ 𝒰.transDomain i j :=
  ⟨(𝒰.chart i).1.map_source (𝒰.baseSet_subset i hi), by
    rw [mem_preimage, (𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hi)]; exact ⟨hi, hj⟩⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem symm_trans {i j : ι} {y : E} (hy : y ∈ 𝒰.transDomain i j) :
    (𝒰.chart j).1.symm (𝒰.trans i j y) = (𝒰.chart i).1.symm y :=
  (𝒰.chart j).1.left_inv (𝒰.baseSet_subset j hy.2.2)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem mapsTo_trans (i j : ι) :
    MapsTo (𝒰.trans i j) (𝒰.transDomain i j) (𝒰.transDomain j i) := fun y hy ↦
  ⟨(𝒰.chart j).1.map_source (𝒰.baseSet_subset j hy.2.2), by
    rw [mem_preimage, 𝒰.symm_trans hy]; exact ⟨hy.2.2, hy.2.1⟩⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem trans_trans {i j : ι} {y : E} (hy : y ∈ 𝒰.transDomain i j) :
    𝒰.trans j i (𝒰.trans i j y) = y := by
  change (𝒰.chart i).1 ((𝒰.chart j).1.symm (𝒰.trans i j y)) = y
  rw [𝒰.symm_trans hy, (𝒰.chart i).1.right_inv hy.1]

variable [MBManifold E M]

/-- The changes of coordinates are smooth. -/
theorem smoothMBOn_trans (i j : ι) : SmoothMBOn (𝒰.trans i j) (𝒰.transDomain i j) :=
  fun k ↦ (smoothMBOn_transition' (𝒰.chart i) (𝒰.chart j) k).mono fun _ hy ↦
    ⟨hy.1, 𝒰.baseSet_subset j hy.2.2⟩

end TrivializationCover

variable (E M) in
/-- The cover of `M` by the domains of the charts of its atlas. -/
def atlasCover : TrivializationCover E M (atlas E M) where
  chart i := i
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  baseSet_subset _ := subset_rfl
  indexAt x := ⟨chartAt E x, chart_mem_atlas E x⟩
  mem_baseSet_at x := mem_chart_source E x

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem atlasCover_domain (i : atlas E M) : (atlasCover E M).domain i = i.1.target :=
  inter_eq_left.2 fun _ hy ↦ i.1.map_target hy

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] in
theorem atlasCover_transDomain (i j : atlas E M) :
    (atlasCover E M).transDomain i j = i.1.target ∩ i.1.symm ⁻¹' j.1.source := by
  ext y
  exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, i.1.map_target h.1, h.2⟩⟩

end Cover

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M] {ι : Type w}

/-- A **vector bundle** over `M` with fiber `F`, trivialized over a cover `𝒰`, given by its
coordinate changes `g_{ij}(x) : F → F` from the trivialization over `Uᵢ` to the one over `Uⱼ`:
linear on the overlap `Uᵢ ∩ Uⱼ`, satisfying the cocycle conditions, and such that
`(y, ξ) ↦ g_{ij}(φᵢ⁻¹ y) ξ` is smooth on `φᵢ(Uᵢ ∩ Uⱼ) × F`. -/
structure MBVectorBundleCore (𝒰 : TrivializationCover E M ι) (F : Type u) [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F] where
  /-- The coordinate change `g_{ij}(x)` from the trivialization over `i` to the one over `j`. -/
  coordChange : ι → ι → M → F → F
  map_add : ∀ i j x, x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j → ∀ ξ η,
    coordChange i j x (ξ + η) = coordChange i j x ξ + coordChange i j x η
  map_smul : ∀ i j x, x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j → ∀ (c : ℝ) ξ,
    coordChange i j x (c • ξ) = c • coordChange i j x ξ
  coordChange_self : ∀ i x, x ∈ 𝒰.baseSet i → ∀ ξ, coordChange i i x ξ = ξ
  coordChange_comp : ∀ i j k x, x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j ∩ 𝒰.baseSet k → ∀ ξ,
    coordChange j k x (coordChange i j x ξ) = coordChange i k x ξ
  smooth : ∀ i j, SmoothMBOn (fun p : E × F ↦ coordChange i j ((𝒰.chart i).1.symm p.1) p.2)
    (𝒰.transDomain i j ×ˢ univ)

variable {𝒰 : TrivializationCover E M ι}
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace MBVectorBundleCore

variable (V : MBVectorBundleCore 𝒰 F)

/-- The coordinate change over a point of the overlap, as a linear map. -/
def coordChangeLinear (i j : ι) {x : M} (hx : x ∈ 𝒰.baseSet i ∩ 𝒰.baseSet j) :
    F →ₗ[ℝ] F where
  toFun := V.coordChange i j x
  map_add' := V.map_add i j x hx
  map_smul' := V.map_smul i j x hx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem continuousOn_coordChange (i j : ι) :
    ContinuousOn (fun p : M × F ↦ V.coordChange i j p.1 p.2)
      ((𝒰.baseSet i ∩ 𝒰.baseSet j) ×ˢ univ) := by
  have hd : ContinuousOn (fun p : E × F ↦ V.coordChange i j ((𝒰.chart i).1.symm p.1) p.2)
      (𝒰.transDomain i j ×ˢ univ) :=
    (V.smooth i j 0 : ContDiffMBOn 0 _ _)
  have hfst : ContinuousOn (fun p : M × F ↦ (𝒰.chart i).1 p.1)
      ((𝒰.baseSet i ∩ 𝒰.baseSet j) ×ˢ univ) :=
    (𝒰.chart i).1.continuousOn.comp continuousOn_fst fun p hp ↦ 𝒰.baseSet_subset i hp.1.1
  refine (hd.comp (hfst.prodMk continuousOn_snd) ?_).congr fun p hp ↦ ?_
  · rintro ⟨x, v⟩ ⟨⟨hi, hj⟩, -⟩
    exact ⟨𝒰.chart_mem_transDomain hi hj, mem_univ _⟩
  · simp [(𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hp.1.1)]

/-- The underlying topological fiber bundle core. -/
def toFiberBundleCore : FiberBundleCore ι M F where
  baseSet := 𝒰.baseSet
  isOpen_baseSet := 𝒰.isOpen_baseSet
  indexAt := 𝒰.indexAt
  mem_baseSet_at := 𝒰.mem_baseSet_at
  coordChange := V.coordChange
  coordChange_self i x hx ξ := V.coordChange_self i x hx ξ
  continuousOn_coordChange := V.continuousOn_coordChange
  coordChange_comp i j k x hx ξ := V.coordChange_comp i j k x hx ξ

/-- The total space of the bundle. -/
abbrev TotalSpace : Type _ := V.toFiberBundleCore.TotalSpace

instance : ChartedSpace (E × F) V.TotalSpace :=
  FiberBundle.chartedSpace (HB := E)

/-- The chart of the total space built from the trivialization over `i` and the chart `c` of
the base. -/
def bundleChart (i : ι) (c : OpenPartialHomeomorph M E) :
    OpenPartialHomeomorph V.TotalSpace (E × F) :=
  (V.toFiberBundleCore.localTriv i).toOpenPartialHomeomorph ≫ₕ
    c.prod (OpenPartialHomeomorph.refl F)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem bundleChart_apply (i : ι) (c : OpenPartialHomeomorph M E) (p : V.TotalSpace) :
    V.bundleChart i c p = (c p.1, V.coordChange (𝒰.indexAt p.1) i p.1 p.2) :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem bundleChart_symm_proj (i : ι) (c : OpenPartialHomeomorph M E) (q : E × F) :
    ((V.bundleChart i c).symm q).proj = c.symm q.1 :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem bundleChart_symm_snd (i : ι) (c : OpenPartialHomeomorph M E) (q : E × F) :
    (((V.bundleChart i c).symm q).2 : F) =
      V.coordChange i (𝒰.indexAt (c.symm q.1)) (c.symm q.1) q.2 :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem mem_bundleChart_source (i : ι) (c : OpenPartialHomeomorph M E) (p : V.TotalSpace) :
    p ∈ (V.bundleChart i c).source ↔ p.1 ∈ 𝒰.baseSet i ∧ p.1 ∈ c.source := by
  simp only [bundleChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_prod, mem_univ,
    and_true, Trivialization.coe_coe, FiberBundleCore.localTriv_apply,
    FiberBundleCore.mem_localTriv_source]
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem mem_bundleChart_target (i : ι) (c : OpenPartialHomeomorph M E) (q : E × F) :
    q ∈ (V.bundleChart i c).target ↔ q.1 ∈ c.target ∧ c.symm q.1 ∈ 𝒰.baseSet i := by
  simp only [bundleChart, OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target, mem_prod, mem_univ,
    and_true, OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_symm, FiberBundleCore.mem_localTriv_target]
  rfl

/-- The transition maps of the total space are `(y, ξ) ↦ (τ y, g(c⁻¹ y) ξ)`; they are smooth. -/
theorem smoothMBOn_bundleChart_transition (i j : ι) {c c' : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    SmoothMBOn ⇑((V.bundleChart i c).symm ≫ₕ V.bundleChart j c')
      ((V.bundleChart i c).symm ≫ₕ V.bundleChart j c').source := by
  set ψ := V.bundleChart i c
  set ψ' := V.bundleChart j c'
  set φ := (𝒰.chart i).1
  set D := c.target ∩ c.symm ⁻¹' (𝒰.baseSet i ∩ 𝒰.baseSet j ∩ c'.source)
  have hD : IsOpen D := c.isOpen_inter_preimage_symm
    (((𝒰.isOpen_baseSet i).inter (𝒰.isOpen_baseSet j)).inter c'.open_source)
  have hDU : IsOpen (D ×ˢ (univ : Set F)) := hD.prod isOpen_univ
  have hsrc : (ψ.symm ≫ₕ ψ').source ⊆ D ×ˢ univ := by
    rintro q ⟨hq, hq'⟩
    replace hq : q ∈ ψ.target := hq
    rw [mem_bundleChart_target] at hq
    rw [mem_preimage, mem_bundleChart_source] at hq'
    simp only [OpenPartialHomeomorph.symm_symm] at hq'
    exact ⟨⟨hq.1, ⟨hq.2, hq'.1⟩, hq'.2⟩, mem_univ _⟩
  set G : E × F → E × F := fun q ↦
    (c' (c.symm q.1), V.coordChange i j (φ.symm (φ (c.symm q.1))) q.2)
  have hG : ∀ q ∈ D ×ˢ (univ : Set F), (ψ.symm ≫ₕ ψ') q = G q := by
    rintro q ⟨⟨-, ⟨hi, hj⟩, -⟩, -⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, bundleChart_apply,
      bundleChart_symm_proj, bundleChart_symm_snd,
      V.coordChange_comp i _ j _ ⟨⟨hi, 𝒰.mem_baseSet_at _⟩, hj⟩]
    simp only [G, φ, (𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hi)]
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
  have hic : ContDiffMBOn k ((φ ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E F) (D ×ˢ univ) :=
    (smoothMBOn_transition hc (𝒰.chart i).2 k).comp hDU
      (c.isOpen_inter_preimage_symm (𝒰.chart i).1.open_source)
      hfst fun q hq ↦ ⟨hq.1.1, 𝒰.baseSet_subset i hq.1.2.1.1⟩
  have hφ := hic.prodMk hDU hsnd
  have h2 := (V.smooth i j k).comp hDU ((𝒰.isOpen_transDomain i j).prod isOpen_univ) hφ
    fun q hq ↦ ⟨𝒰.chart_mem_transDomain hq.1.2.1.1 hq.1.2.1.2, mem_univ _⟩
  exact h1.prodMk hDU h2

theorem bundleChart_transition_mem (i j : ι) {c c' : OpenPartialHomeomorph M E}
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
/-- **The tangent bundle is a vector bundle**, trivialized over the charts of the atlas: its
coordinate changes are the derivatives of the transition maps, `(y, w) ↦ dτ(y) w`. -/
def tangentMBCore : MBVectorBundleCore (atlasCover E M) E where
  coordChange := tangentCoordChange
  map_add i j x (hx : x ∈ i.1.source ∩ j.1.source) v w :=
    (smoothMBOn_transition' i j 1).dMB_add (isOpen_transition_domain i j)
      ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ v w
  map_smul i j x (hx : x ∈ i.1.source ∩ j.1.source) c v :=
    (smoothMBOn_transition' i j 1).dMB_smul
      ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩ c v
  coordChange_self i x hx v := tangentCoordChange_self i hx v
  coordChange_comp i j k x hx v := tangentCoordChange_comp i j k hx v
  smooth i j k := by
    rw [atlasCover_transDomain]
    refine ContDiffMBOn.congr_of_isOpen ((isOpen_transition_domain i j).prod isOpen_univ)
      (fun p hp ↦ ?_) ((smoothMBOn_transition' i j (k + 1)).2.2)
    simp only [tangentCoordChange, atlasCover, i.1.right_inv hp.1.1]

/-! ### Pullback bundles -/

section Pullback

variable {E' : Type u}
  [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] [MBManifold E' N]

variable (𝒰) in
/-- The **pullback of a cover** along a continuous map `f : N → M`: the sets
`k.source ∩ f⁻¹(Uᵢ)`, indexed by the pairs `(k, i)` of a chart `k` of `N` and an index `i`
of `𝒰`. -/
def TrivializationCover.pullback (f : N → M) (hf : Continuous f) :
    TrivializationCover E' N (atlas E' N × ι) where
  chart p := p.1
  baseSet p := p.1.1.source ∩ f ⁻¹' 𝒰.baseSet p.2
  isOpen_baseSet p := p.1.1.open_source.inter ((𝒰.isOpen_baseSet p.2).preimage hf)
  baseSet_subset _ := inter_subset_left
  indexAt x := (⟨chartAt E' x, chart_mem_atlas E' x⟩, 𝒰.indexAt (f x))
  mem_baseSet_at x := ⟨mem_chart_source E' x, 𝒰.mem_baseSet_at (f x)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E']
  [T2Space E'] [MBManifold E' N] in
theorem SmoothMBM.continuous {f : N → M} (hf : SmoothMBM E' E f) : Continuous f :=
  continuousOn_univ.1 (hf 0).continuousOn

namespace MBVectorBundleCore

variable (V : MBVectorBundleCore 𝒰 F)

/-- The **pullback** `f*V` of a vector bundle along a smooth map `f : N → M`: over
`k.source ∩ f⁻¹(Uᵢ)` it is trivialized by the trivialization of `V` over `Uᵢ`, and its coordinate
changes are `g_{ij} ∘ f`. Its fiber over `x` is the fiber of `V` over `f x`
(`MBVectorBundleCore.pullbackMap`). -/
def pullback (f : N → M) (hf : SmoothMBM E' E f) :
    MBVectorBundleCore (𝒰.pullback (E' := E') f hf.continuous) F where
  coordChange p q x := V.coordChange p.2 q.2 (f x)
  map_add p q x hx := V.map_add p.2 q.2 (f x) ⟨hx.1.2, hx.2.2⟩
  map_smul p q x hx := V.map_smul p.2 q.2 (f x) ⟨hx.1.2, hx.2.2⟩
  coordChange_self p x hx := V.coordChange_self p.2 (f x) hx.2
  coordChange_comp p q r x hx :=
    V.coordChange_comp p.2 q.2 r.2 (f x) ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩
  smooth p q n := by
    obtain ⟨k, i⟩ := p
    obtain ⟨l, j⟩ := q
    set φ := (𝒰.chart i).1
    set D := (𝒰.pullback (E' := E') f hf.continuous).transDomain (k, i) (l, j)
    have hD : IsOpen D := TrivializationCover.isOpen_transDomain _ _ _
    have hDU : IsOpen (D ×ˢ (univ : Set F)) := hD.prod isOpen_univ
    -- the local representative `φ ∘ f ∘ k⁻¹` of `f` is smooth on `D`
    have hfD : ContDiffMBOn n (φ ∘ f ∘ k.1.symm) D :=
      ((hf n).contDiffMBOn_chart isOpen_univ k.2 (𝒰.chart i).2).mono fun y hy ↦
        ⟨hy.1, mem_univ _, 𝒰.baseSet_subset i hy.2.1.2⟩
    have hfst : ContDiffMBOn n (ContinuousLinearMap.fst ℝ E' F) (D ×ˢ univ) :=
      (ContinuousLinearMap.fst ℝ E' F).contDiffMBOn n _
    have hsnd : ContDiffMBOn n (ContinuousLinearMap.snd ℝ E' F) (D ×ˢ univ) :=
      (ContinuousLinearMap.snd ℝ E' F).contDiffMBOn n _
    have h1 : ContDiffMBOn n ((φ ∘ f ∘ k.1.symm) ∘ ContinuousLinearMap.fst ℝ E' F)
        (D ×ˢ univ) :=
      hfD.comp hDU hD hfst fun q hq ↦ hq.1
    have h2 := (V.smooth i j n).comp hDU ((𝒰.isOpen_transDomain i j).prod isOpen_univ)
      (h1.prodMk hDU hsnd) fun q hq ↦
        ⟨𝒰.chart_mem_transDomain hq.1.2.1.2 hq.1.2.2.2, mem_univ _⟩
    refine ContDiffMBOn.congr_of_isOpen hDU (fun q hq ↦ ?_) h2
    have hq' : f (k.1.symm q.1) ∈ 𝒰.baseSet i := hq.1.2.1.2
    change V.coordChange i j (φ.symm (φ (f (k.1.symm q.1)))) q.2 =
      V.coordChange i j (f (k.1.symm q.1)) q.2
    rw [(𝒰.chart i).1.left_inv (𝒰.baseSet_subset i hq')]

/-- The canonical map `f*V → V` over `f`; it identifies the fiber of `f*V` over `x` with the
fiber of `V` over `f x`. -/
def pullbackMap (f : N → M) (hf : SmoothMBM E' E f) (p : (V.pullback f hf).TotalSpace) :
    V.TotalSpace :=
  ⟨f p.1, p.2⟩

theorem pullbackMap_proj (f : N → M) (hf : SmoothMBM E' E f)
    (p : (V.pullback f hf).TotalSpace) : (V.pullbackMap f hf p).proj = f p.proj :=
  rfl

end MBVectorBundleCore

end Pullback

end LocallyConvex.Manifolds

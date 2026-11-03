/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCAnalysis.Higher
import LCManifolds.ContMDiff

/-!
# The tangent bundle

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, §I.3; H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3.

Let `M` be a manifold modeled on a locally convex space `E`. The tangent bundle `TM` is glued
from the products `φ(U) × E` along the maps `(y, w) ↦ (τ y, dτ(y) w)`, where `τ` runs over the
transition maps of the atlas. We build it from a `FiberBundleCore` indexed by the charts of the
atlas, whose coordinate changes are the derivatives of the transition maps
(`tangentBundleCore`). The tangent bundle is then a topological fiber bundle with fiber `E`, and
it is a charted space modeled on `E × E`; we show that it is a manifold
(`TangentBundle.mbManifold`): its transition maps are `(y, w) ↦ (τ y, dτ(y) w)`, which are
smooth.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The coordinate change of tangent vectors from the chart `i` to the chart `j` at `x`: the
derivative of the transition map `j ∘ i⁻¹` at `i x`. -/
def tangentCoordChange (i j : atlas E M) (x : M) (v : E) : E :=
  dMB (j.1 ∘ i.1.symm) (i.1 x, v)

/-- The transition map `j ∘ i⁻¹` is smooth on its domain. -/
theorem smoothMBOn_transition' (i j : atlas E M) :
    SmoothMBOn (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
  smoothMBOn_transition i.2 j.2

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
theorem isOpen_transition_domain (i j : atlas E M) :
    IsOpen (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
  i.1.isOpen_inter_preimage_symm j.1.open_source

omit [LocallyConvexSpace ℝ E] [MBManifold E M] in
theorem tangentCoordChange_self (i : atlas E M) {x : M} (hx : x ∈ i.1.source) (v : E) :
    tangentCoordChange i i x v = v := by
  have hev : (i.1 ∘ i.1.symm) =ᶠ[𝓝 (i.1 x)] id :=
    Filter.eventuallyEq_of_mem (i.1.open_target.mem_nhds (i.1.map_source hx))
      fun y hy ↦ i.1.right_inv hy
  rw [tangentCoordChange, dMB_congr_of_eventuallyEq hev]
  exact ((ContinuousLinearMap.id ℝ E).hasDirDerivAt _ v).dMB_eq

theorem tangentCoordChange_comp (i j k : atlas E M) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source ∩ k.1.source) (v : E) :
    tangentCoordChange j k x (tangentCoordChange i j x v) = tangentCoordChange i k x v := by
  obtain ⟨⟨hi, hj⟩, hk⟩ := hx
  set U := i.1.target ∩ i.1.symm ⁻¹' (j.1.source ∩ k.1.source)
  have hU : IsOpen U := i.1.isOpen_inter_preimage_symm (j.1.open_source.inter k.1.open_source)
  have hxU : i.1 x ∈ U := ⟨i.1.map_source hi, by simp [i.1.left_inv hi, hj, hk]⟩
  have hf : ContDiffMBOn 1 (j.1 ∘ i.1.symm) U :=
    (smoothMBOn_transition' i j 1).mono fun y hy ↦ ⟨hy.1, hy.2.1⟩
  have hg : ContDiffMBOn 1 (k.1 ∘ j.1.symm) (j.1.target ∩ j.1.symm ⁻¹' k.1.source) :=
    smoothMBOn_transition' j k 1
  have hmaps : MapsTo (j.1 ∘ i.1.symm) U (j.1.target ∩ j.1.symm ⁻¹' k.1.source) := by
    rintro y ⟨-, hyj, hyk⟩
    exact ⟨j.1.map_source hyj, by simp [j.1.left_inv hyj, hyk]⟩
  have hev : (k.1 ∘ j.1.symm) ∘ (j.1 ∘ i.1.symm) =ᶠ[𝓝 (i.1 x)] k.1 ∘ i.1.symm :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun y hy ↦ by
      simp [j.1.left_inv hy.2.1]
  have := ContDiffMBOn.dMB_comp (isOpen_transition_domain j k) hg hf hmaps hxU v
  rw [dMB_congr_of_eventuallyEq hev] at this
  rw [tangentCoordChange, tangentCoordChange, tangentCoordChange, this]
  simp [i.1.left_inv hi]

theorem continuousOn_tangentCoordChange (i j : atlas E M) :
    ContinuousOn (fun p : M × E ↦ tangentCoordChange i j p.1 p.2)
      ((i.1.source ∩ j.1.source) ×ˢ univ) := by
  have hd : ContinuousOn (dMB (j.1 ∘ i.1.symm))
      ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ) :=
    ((smoothMBOn_transition' i j 1).2.2 : ContDiffMBOn 0 _ _)
  have hfst : ContinuousOn (fun p : M × E ↦ i.1 p.1) ((i.1.source ∩ j.1.source) ×ˢ univ) :=
    i.1.continuousOn.comp continuousOn_fst fun p hp ↦ hp.1.1
  refine hd.comp (hfst.prodMk continuousOn_snd) ?_
  rintro ⟨x, v⟩ ⟨⟨hi, hj⟩, -⟩
  exact ⟨⟨i.1.map_source hi, by simp [i.1.left_inv hi, hj]⟩, mem_univ _⟩

variable (E M) in
/-- The tangent bundle as a fiber bundle core: indexed by the charts of the atlas, with
coordinate changes the derivatives of the transition maps. -/
def tangentBundleCore : FiberBundleCore (atlas E M) M E where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt x := ⟨chartAt E x, chart_mem_atlas E x⟩
  mem_baseSet_at x := mem_chart_source E x
  coordChange := tangentCoordChange
  coordChange_self i _ hx v := tangentCoordChange_self i hx v
  continuousOn_coordChange := continuousOn_tangentCoordChange
  coordChange_comp i j k _ hx v := tangentCoordChange_comp i j k hx v

instance (x : M) : AddCommGroup ((tangentBundleCore E M).Fiber x) :=
  inferInstanceAs (AddCommGroup E)

instance (x : M) : Module ℝ ((tangentBundleCore E M).Fiber x) :=
  inferInstanceAs (Module ℝ E)

variable (E M) in
/-- The tangent bundle of `M`, with fibers `E`. -/
abbrev TangentBundle : Type _ := (tangentBundleCore E M).TotalSpace

instance : ChartedSpace (E × E) (TangentBundle E M) :=
  FiberBundle.chartedSpace (HB := E)

/-- The chart of the tangent bundle built from the trivialization over the chart `i` and the
chart `c` of the base. -/
def tangentChart (i : atlas E M) (c : OpenPartialHomeomorph M E) :
    OpenPartialHomeomorph (TangentBundle E M) (E × E) :=
  ((tangentBundleCore E M).localTriv i).toOpenPartialHomeomorph ≫ₕ
    c.prod (OpenPartialHomeomorph.refl E)

theorem tangentChart_apply (i : atlas E M) (c : OpenPartialHomeomorph M E)
    (p : TangentBundle E M) :
    tangentChart i c p =
      (c p.1, tangentCoordChange ⟨chartAt E p.1, chart_mem_atlas E p.1⟩ i p.1 p.2) :=
  rfl

theorem tangentChart_symm_proj (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × E) :
    ((tangentChart i c).symm q).proj = c.symm q.1 :=
  rfl

theorem tangentChart_symm_snd (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × E) :
    (((tangentChart i c).symm q).2 : E) =
      tangentCoordChange i ⟨chartAt E (c.symm q.1), chart_mem_atlas E _⟩ (c.symm q.1) q.2 :=
  rfl

theorem mem_tangentChart_source (i : atlas E M) (c : OpenPartialHomeomorph M E)
    (p : TangentBundle E M) :
    p ∈ (tangentChart i c).source ↔ p.1 ∈ i.1.source ∧ p.1 ∈ c.source := by
  simp only [tangentChart, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_source, OpenPartialHomeomorph.refl_source, mem_prod, mem_univ,
    and_true, Trivialization.coe_coe, FiberBundleCore.localTriv_apply,
    FiberBundleCore.mem_localTriv_source]
  rfl

theorem mem_tangentChart_target (i : atlas E M) (c : OpenPartialHomeomorph M E) (q : E × E) :
    q ∈ (tangentChart i c).target ↔ q.1 ∈ c.target ∧ c.symm q.1 ∈ i.1.source := by
  simp only [tangentChart, OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target, mem_prod, mem_univ,
    and_true, OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_apply,
    OpenPartialHomeomorph.refl_symm, FiberBundleCore.mem_localTriv_target]
  rfl

/-- The transition maps of the tangent bundle are `(y, w) ↦ (τ y, dσ(i (c⁻¹ y)) w)`, where `τ` and
`σ` are transition maps of the base; in particular they are smooth. -/
theorem smoothMBOn_tangentChart_transition (i j : atlas E M) {c c' : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    SmoothMBOn ⇑((tangentChart i c).symm ≫ₕ tangentChart j c')
      ((tangentChart i c).symm ≫ₕ tangentChart j c').source := by
  set ψ := tangentChart i c
  set ψ' := tangentChart j c'
  set D := c.target ∩ c.symm ⁻¹' (i.1.source ∩ j.1.source ∩ c'.source)
  have hD : IsOpen D := c.isOpen_inter_preimage_symm
    ((i.1.open_source.inter j.1.open_source).inter c'.open_source)
  have hDU : IsOpen (D ×ˢ (univ : Set E)) := hD.prod isOpen_univ
  -- the source of the transition lies over `D`, where we have an explicit formula
  have hsrc : (ψ.symm ≫ₕ ψ').source ⊆ D ×ˢ univ := by
    rintro q ⟨hq, hq'⟩
    replace hq : q ∈ ψ.target := hq
    rw [mem_tangentChart_target] at hq
    rw [mem_preimage, mem_tangentChart_source] at hq'
    simp only [OpenPartialHomeomorph.symm_symm] at hq'
    exact ⟨⟨hq.1, ⟨hq.2, hq'.1⟩, hq'.2⟩, mem_univ _⟩
  set G : E × E → E × E := fun q ↦
    (c' (c.symm q.1), dMB (j.1 ∘ i.1.symm) (i.1 (c.symm q.1), q.2))
  have hG : ∀ q ∈ D ×ˢ (univ : Set E), (ψ.symm ≫ₕ ψ') q = G q := by
    rintro q ⟨⟨-, ⟨hi, hj⟩, -⟩, -⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, tangentChart_apply,
      tangentChart_symm_proj, tangentChart_symm_snd,
      tangentCoordChange_comp i _ j ⟨⟨hi, mem_chart_source E _⟩, hj⟩]
    rfl
  intro k
  refine ContDiffMBOn.congr_of_isOpen (ψ.symm ≫ₕ ψ').open_source
    (fun q hq ↦ (hG q (hsrc hq)).symm) (ContDiffMBOn.mono ?_ hsrc)
  -- smoothness of the explicit formula
  have hfst : ContDiffMBOn k (ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (ContinuousLinearMap.fst ℝ E E).contDiffMBOn k _
  have hsnd : ContDiffMBOn k (ContinuousLinearMap.snd ℝ E E) (D ×ˢ univ) :=
    (ContinuousLinearMap.snd ℝ E E).contDiffMBOn k _
  have h1 : ContDiffMBOn k ((c' ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (smoothMBOn_transition hc hc' k).comp hDU (c.isOpen_inter_preimage_symm c'.open_source)
      hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.2⟩
  have hic : ContDiffMBOn k ((i.1 ∘ c.symm) ∘ ContinuousLinearMap.fst ℝ E E) (D ×ˢ univ) :=
    (smoothMBOn_transition hc i.2 k).comp hDU (c.isOpen_inter_preimage_symm i.1.open_source)
      hfst fun q hq ↦ ⟨hq.1.1, hq.1.2.1.1⟩
  have hφ := hic.prodMk hDU hsnd
  have hd : ContDiffMBOn k (dMB (j.1 ∘ i.1.symm))
      ((i.1.target ∩ i.1.symm ⁻¹' j.1.source) ×ˢ univ) :=
    (smoothMBOn_transition' i j (k + 1)).2.2
  have h2 := hd.comp hDU ((isOpen_transition_domain i j).prod isOpen_univ) hφ
    fun q hq ↦ ⟨⟨i.1.map_source hq.1.2.1.1, by
      simp [i.1.left_inv hq.1.2.1.1, hq.1.2.1.2]⟩, mem_univ _⟩
  exact h1.prodMk hDU h2

theorem tangentChart_transition_mem (i j : atlas E M) {c c' : OpenPartialHomeomorph M E}
    (hc : c ∈ atlas E M) (hc' : c' ∈ atlas E M) :
    (tangentChart i c).symm ≫ₕ tangentChart j c' ∈ mbGroupoid (E × E) := by
  refine ⟨smoothMBOn_tangentChart_transition i j hc hc', ?_⟩
  have h := smoothMBOn_tangentChart_transition j i hc' hc
  rw [OpenPartialHomeomorph.trans_source] at h
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_target, ← OpenPartialHomeomorph.symm_source,
    OpenPartialHomeomorph.symm_target]
  exact h

/-- The tangent bundle of a manifold modeled on `E` is a manifold modeled on `E × E`. -/
instance TangentBundle.mbManifold : MBManifold (E × E) (TangentBundle E M) where
  compatible := by
    rintro _ _ ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨c, hc, r, hr, rfl⟩, rfl⟩
      ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, _, ⟨c', hc', r', hr', rfl⟩, rfl⟩
    rw [chartedSpaceSelf_atlas] at hr hr'
    subst hr hr'
    exact tangentChart_transition_mem i j hc hc'

end LCManifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.VectorField

/-!
# The double tangent bundle

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 5;
S. Lang, *Fundamentals of Differential Geometry*, §IV.3.

The double tangent bundle `TTM` is the tangent bundle of `TM`. A chart `i` of `M` gives a chart
`ψᵢ` of `TM` and a chart `Ψᵢ` of `TTM`, in which points are written `((x, v), (u, w))`: `(x, v)`
is the base point in `TM` and `(u, w)` the tangent vector at it. We show:

* `tangentChart_transition_apply`: the transition maps of `TM` are `(x, v) ↦ (τ x, dτₓ v)`,
  `τ = j ∘ i⁻¹`;
* `ddChart_transition_apply`: the transition maps of `TTM` are
  `((x, v), (u, w)) ↦ ((τ x, dτₓ v), (dτₓ u, d²τₓ(u, v) + dτₓ w))`.

Since `d²τₓ(u, v)` is symmetric in `(u, v)` (Schwarz), the canonical flip
`((x, v), (u, w)) ↦ ((x, u), (v, w))` commutes with these transition maps
(`ddChart_transition_swap`), so it is a well defined map of `TTM`.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- **The transition maps of the tangent bundle** in the charts over charts `i`, `j` of `M`:
`(x, v) ↦ (τ x, dτₓ v)`, `τ = j ∘ i⁻¹`. -/
theorem tangentChart_transition_apply (i j : atlas E M) {x : E} (hx : x ∈ i.1.target)
    (hxj : i.1.symm x ∈ j.1.source) (v : E) :
    tangentChart j j.1 ((tangentChart i i.1).symm (x, v)) =
      ((j.1 ∘ i.1.symm) x, dMB (j.1 ∘ i.1.symm) (x, v)) := by
  have hq : i.1.symm x ∈ i.1.source := i.1.map_target hx
  rw [tangentChart_apply, tangentChart_symm_proj, tangentChart_symm_snd,
    tangentCoordChange_comp i _ j ⟨⟨hq, mem_chart_source E _⟩, hxj⟩]
  simp only [tangentCoordChange, i.1.right_inv hx]
  rfl

/-- The chart of `TM` over a chart `i` of `M`, as an element of the atlas of `TM`. -/
def tangentAtlas (i : atlas E M) : atlas (E × E) (TangentBundle E M) :=
  ⟨tangentChart i i.1, tangentChart_mem_atlas i⟩

/-- The derivative of the transition map of `TM`:
`dσ_{(x,v)}(u, w) = (dτₓ u, d²τₓ(u, v) + dτₓ w)`. -/
theorem dMB_tangentChart_transition (i j : atlas E M) {x : E}
    (hx : x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v u w : E) :
    dMB ((tangentAtlas j).1 ∘ (tangentAtlas i).1.symm) ((x, v), (u, w)) =
      (dMB (j.1 ∘ i.1.symm) (x, u),
        dMB (dMB (j.1 ∘ i.1.symm)) ((x, v), (u, 0)) + dMB (j.1 ∘ i.1.symm) (x, w)) := by
  set τ := j.1 ∘ i.1.symm
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hTU : IsOpen (T ×ˢ (univ : Set E)) := hT.prod isOpen_univ
  have hτ : ContDiffMBOn 2 τ T := smoothMBOn_transition' i j 2
  have hdτ : ContDiffMBOn 1 (dMB τ) (T ×ˢ univ) := hτ.2.2
  have hp : (x, v) ∈ T ×ˢ (univ : Set E) := ⟨hx, mem_univ v⟩
  -- near `(x, v)`, the transition map of `TM` is `(y, z) ↦ (τ y, dτ_y z)`
  have hev : (tangentAtlas j).1 ∘ (tangentAtlas i).1.symm =ᶠ[𝓝 (x, v)]
      fun q : E × E ↦ (τ q.1, dMB τ q) :=
    Filter.eventuallyEq_of_mem (hTU.mem_nhds hp) fun q hq ↦
      tangentChart_transition_apply i j hq.1.1 hq.1.2 q.2
  have h1 : HasDirDerivAt (fun q : E × E ↦ τ q.1) (x, v) (u, w) (dMB τ (x, u)) :=
    (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).hasDirDerivAt hx u
  have h2 := hdτ.hasDirDerivAt (k := 0) hp (u, w)
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT hx
  have hsplit : dMB (dMB τ) ((x, v), (u, w)) =
      dMB (dMB τ) ((x, v), (u, 0)) + dMB τ (x, w) := by
    have hw : ((u, w) : E × E) = (u, 0) + (0, w) := by simp
    rw [hw, hdτ.dMB_add hTU hp, dMB_slice₂]
    have hfun : (fun z ↦ dMB τ (x, z)) = ⇑L := funext fun z ↦ (hL z).symm
    rw [hfun, (L.hasDirDerivAt _ _).dMB_eq, hL]
  rw [dMB_congr_of_eventuallyEq hev, (h1.prodMk h2).dMB_eq, hsplit]

variable (E M) in
/-- The double tangent bundle `TTM = T(TM)`. -/
abbrev DoubleTangentBundle : Type _ := TangentBundle (E × E) (TangentBundle E M)

/-- The chart of `TTM` over a chart `i` of `M`, with values `((x, v), (u, w))`. -/
def ddChart (i : atlas E M) :
    OpenPartialHomeomorph (DoubleTangentBundle E M) ((E × E) × (E × E)) :=
  tangentChart (tangentAtlas i) (tangentAtlas i).1

/-- **The transition maps of the double tangent bundle**:
`((x, v), (u, w)) ↦ ((τ x, dτₓ v), (dτₓ u, d²τₓ(u, v) + dτₓ w))`. -/
theorem ddChart_transition_apply (i j : atlas E M) {x : E}
    (hx : x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v u w : E) :
    ddChart j ((ddChart i).symm ((x, v), (u, w))) =
      (((j.1 ∘ i.1.symm) x, dMB (j.1 ∘ i.1.symm) (x, v)),
        (dMB (j.1 ∘ i.1.symm) (x, u),
          dMB (dMB (j.1 ∘ i.1.symm)) ((x, v), (u, 0)) + dMB (j.1 ∘ i.1.symm) (x, w))) := by
  have hy : (x, v) ∈ (tangentAtlas i).1.target :=
    (mem_tangentChart_target _ _ _).mpr ⟨hx.1, i.1.map_target hx.1⟩
  have hyj : (tangentAtlas i).1.symm (x, v) ∈ (tangentAtlas j).1.source :=
    (mem_tangentChart_source _ _ _).mpr ⟨hx.2, hx.2⟩
  rw [ddChart, ddChart, tangentChart_transition_apply (tangentAtlas i) (tangentAtlas j) hy hyj,
    dMB_tangentChart_transition i j hx]
  simp only [Function.comp_apply]
  congr 1
  exact tangentChart_transition_apply i j hx.1 hx.2 v

/-- The canonical swap `((x, v), (u, w)) ↦ ((x, u), (v, w))` in coordinates. -/
def swapUV (q : (E × E) × (E × E)) : (E × E) × (E × E) := ((q.1.1, q.2.1), (q.1.2, q.2.2))

/-- **The flip commutes with the transition maps of `TTM`**, by the symmetry of `d²τ`. -/
theorem ddChart_transition_swap (i j : atlas E M) {x : E}
    (hx : x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v u w : E) :
    ddChart j ((ddChart i).symm (swapUV ((x, v), (u, w)))) =
      swapUV (ddChart j ((ddChart i).symm ((x, v), (u, w)))) := by
  have hτ : ContDiffMBOn 2 (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
    smoothMBOn_transition' i j 2
  change ddChart j ((ddChart i).symm ((x, u), (v, w))) = _
  rw [ddChart_transition_apply i j hx, ddChart_transition_apply i j hx, swapUV,
    hτ.dMB_dMB_symm (isOpen_transition_domain i j) hx u v]

theorem mem_ddChart_source (i : atlas E M) (P : DoubleTangentBundle E M) :
    P ∈ (ddChart i).source ↔ P.proj.proj ∈ i.1.source := by
  rw [ddChart, mem_tangentChart_source, and_self]
  change P.proj ∈ (tangentChart i i.1).source ↔ _
  rw [mem_tangentChart_source, and_self]

theorem ddChart_symm_proj_proj (i : atlas E M) (q : (E × E) × (E × E)) :
    ((ddChart i).symm q).proj.proj = i.1.symm q.1.1 :=
  rfl

theorem mem_ddChart_target (i : atlas E M) (q : (E × E) × (E × E)) :
    q ∈ (ddChart i).target ↔ q.1.1 ∈ i.1.target := by
  rw [ddChart, mem_tangentChart_target]
  constructor
  · intro h
    exact ((mem_tangentChart_target _ _ _).mp h.1).1
  · intro h
    have h1 : q.1 ∈ (tangentAtlas i).1.target :=
      (mem_tangentChart_target _ _ _).mpr ⟨h, i.1.map_target h⟩
    exact ⟨h1, (tangentAtlas i).1.map_target h1⟩

/-- The preferred chart of `TTM` at `P`, over the preferred chart of `M` at the base point. -/
def ddChartAt (P : DoubleTangentBundle E M) : atlas E M :=
  ⟨chartAt E P.proj.proj, chart_mem_atlas E _⟩

/-- **The canonical flip** of `TTM`, `((x, v), (u, w)) ↦ ((x, u), (v, w))` in charts. -/
def flip (P : DoubleTangentBundle E M) : DoubleTangentBundle E M :=
  (ddChart (ddChartAt P)).symm (swapUV (ddChart (ddChartAt P) P))

theorem flip_proj_proj (P : DoubleTangentBundle E M) : (flip P).proj.proj = P.proj.proj := by
  have hP : P ∈ (ddChart (ddChartAt P)).source :=
    (mem_ddChart_source _ _).mpr (mem_chart_source E _)
  rw [flip, ddChart_symm_proj_proj]
  change (ddChartAt P).1.symm (ddChart (ddChartAt P) P).1.1 = _
  rw [← ddChart_symm_proj_proj, (ddChart _).left_inv hP]

/-- **The flip does not depend on the chart**: in every chart of `TTM` over a chart of `M`, it
is `((x, v), (u, w)) ↦ ((x, u), (v, w))`. -/
theorem ddChart_flip (j : atlas E M) {P : DoubleTangentBundle E M}
    (hP : P.proj.proj ∈ j.1.source) : ddChart j (flip P) = swapUV (ddChart j P) := by
  set i := ddChartAt P
  have hPi : P ∈ (ddChart i).source := (mem_ddChart_source _ _).mpr (mem_chart_source E _)
  have hq : ddChart i P ∈ (ddChart i).target := (ddChart i).map_source hPi
  have hsymm : (ddChart i).symm (ddChart i P) = P := (ddChart i).left_inv hPi
  have hx : (ddChart i P).1.1 ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source := by
    refine ⟨(mem_ddChart_target _ _).mp hq, ?_⟩
    rw [mem_preimage, ← ddChart_symm_proj_proj, hsymm]
    exact hP
  have key := ddChart_transition_swap i j hx (ddChart i P).1.2 (ddChart i P).2.1
    (ddChart i P).2.2
  simp only [Prod.mk.eta] at key
  rw [hsymm] at key
  exact key

/-- The flip is an involution. -/
theorem flip_flip (P : DoubleTangentBundle E M) : flip (flip P) = P := by
  set i := ddChartAt P
  have hPi : P.proj.proj ∈ i.1.source := mem_chart_source E _
  have hfP : (flip P).proj.proj ∈ i.1.source := by rw [flip_proj_proj]; exact hPi
  have hffP : (flip (flip P)).proj.proj ∈ i.1.source := by rw [flip_proj_proj]; exact hfP
  refine (ddChart i).injOn ((mem_ddChart_source _ _).mpr hffP) ((mem_ddChart_source _ _).mpr hPi)
    ?_
  rw [ddChart_flip i hfP, ddChart_flip i hPi]
  rfl

end LCManifolds

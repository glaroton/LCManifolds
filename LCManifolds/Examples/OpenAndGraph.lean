/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.SubmanifoldNotions

/-!
# Examples: open subsets and graphs

* An open subset of a manifold is an embedded submanifold modeled on the whole model space
  (`isEmbeddedSubmanifold_open`). This uses that smooth charts can be restricted to open sets
  (`mbGroupoid` is closed under restriction).
* The graph of a map `g`, smooth on an open set `U ⊆ E`, is a split submanifold of `E × G`
  modeled on `E × 0` (`isSplitSubmanifold_graph`). The slice chart is explicit,
  `(x, y) ↦ (x, y - g x)`, with inverse `(x, z) ↦ (x, z + g x)`: no inverse function theorem is
  needed.
-/

open Set Filter
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- Smooth charts can be restricted to open sets. -/
instance : ClosedUnderRestriction (mbGroupoid E) where
  closedUnderRestriction {e} he s hs := by
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · rw [OpenPartialHomeomorph.restr_source, hs.interior_eq]
      exact (he.1 k).mono inter_subset_left
    · rw [OpenPartialHomeomorph.restr_target, hs.interior_eq]
      exact (he.2 k).mono inter_subset_left

section Open

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- **An open subset is an embedded submanifold**, modeled on the whole model space. -/
theorem isEmbeddedSubmanifold_open {U : Set M} (hU : IsOpen U) :
    IsEmbeddedSubmanifold U (⊤ : Submodule ℝ E) := by
  refine ⟨by simp, fun p hp ↦ ⟨(chartAt E p).restr U, ⟨?_, fun q hq ↦ ?_⟩, ?_⟩⟩
  · exact restr_mem_maximalAtlas (mbGroupoid E)
      ((mbGroupoid E).chart_mem_maximalAtlas p) hU
  · rw [OpenPartialHomeomorph.restr_source, hU.interior_eq] at hq
    simpa using hq.2
  · rw [OpenPartialHomeomorph.restr_source, hU.interior_eq]
    exact ⟨mem_chart_source E p, hp⟩

end Open

section Graph

variable {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {g : E → G} {U : Set E}

variable (g U) in
/-- The graph of `g` over `U`. -/
def graph : Set (E × G) := {q | q.1 ∈ U ∧ q.2 = g q.1}

variable (E G) in
/-- The model of graphs: the horizontal subspace `E × 0`. -/
def horizontal : Submodule ℝ (E × G) := LinearMap.ker (LinearMap.snd ℝ E G)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
theorem isClosed_horizontal : IsClosed (horizontal E G : Set (E × G)) :=
  isClosed_eq continuous_snd continuous_const

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] in
theorem closedComplemented_horizontal : (horizontal E G).ClosedComplemented := by
  refine ⟨((ContinuousLinearMap.inl ℝ E G).comp (ContinuousLinearMap.fst ℝ E G)).codRestrict _
    fun q ↦ by simp [horizontal, LinearMap.mem_ker], fun q ↦ Subtype.ext ?_⟩
  have h2 : (q : E × G).2 = 0 := q.2
  ext
  · rfl
  · change (0 : G) = (q : E × G).2
    exact h2.symm

/-- The slice chart of a graph, `(x, y) ↦ (x, y - g x)`. -/
def graphChart (hU : IsOpen U) (hg : ContinuousOn g U) : OpenPartialHomeomorph (E × G) (E × G)
    where
  toFun q := (q.1, q.2 - g q.1)
  invFun q := (q.1, q.2 + g q.1)
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' q hq := ⟨hq.1, mem_univ _⟩
  map_target' q hq := ⟨hq.1, mem_univ _⟩
  left_inv' q _ := by simp
  right_inv' q _ := by simp
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := continuous_fst.continuousOn.prodMk
    (continuous_snd.continuousOn.sub (hg.comp continuous_fst.continuousOn fun q hq ↦ hq.1))
  continuousOn_invFun := continuous_fst.continuousOn.prodMk
    (continuous_snd.continuousOn.add (hg.comp continuous_fst.continuousOn fun q hq ↦ hq.1))

/-- The graph chart is smooth, with smooth inverse. -/
theorem graphChart_mem (hU : IsOpen U) (hg : SmoothMBOn g U) :
    graphChart hU (hg 0) ∈ mbGroupoid (E × G) := by
  have hUU : IsOpen (U ×ˢ (univ : Set G)) := hU.prod isOpen_univ
  have hgfst : ∀ k, ContDiffMBOn k (fun q : E × G ↦ g q.1) (U ×ˢ univ) := fun k ↦
    ContDiffMBOn.comp (g := g) (f := fun q : E × G ↦ q.1) hUU hU (hg k)
      ((ContinuousLinearMap.fst ℝ E G).contDiffMBOn k _) fun q hq ↦ hq.1
  have hfst : ∀ k, ContDiffMBOn k (fun q : E × G ↦ q.1) (U ×ˢ univ) := fun k ↦
    (ContinuousLinearMap.fst ℝ E G).contDiffMBOn k _
  have hsnd : ∀ k, ContDiffMBOn k (fun q : E × G ↦ q.2) (U ×ˢ univ) := fun k ↦
    (ContinuousLinearMap.snd ℝ E G).contDiffMBOn k _
  have hneg : ∀ k, ContDiffMBOn k (fun q : E × G ↦ -g q.1) (U ×ˢ univ) := fun k ↦
    ((-ContinuousLinearMap.id ℝ G).contDiffMBOn k univ).comp hUU isOpen_univ (hgfst k)
      (mapsTo_univ _ _)
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · have h := ContDiffMBOn.prodMk hUU (hfst k) (ContDiffMBOn.add hUU (hsnd k) (hneg k))
    refine ContDiffMBOn.congr_of_isOpen hUU (fun q _ ↦ ?_) h
    simp [graphChart, sub_eq_add_neg]
  · have h := ContDiffMBOn.prodMk hUU (hfst k) (ContDiffMBOn.add hUU (hsnd k) (hgfst k))
    refine ContDiffMBOn.congr_of_isOpen hUU (fun q _ ↦ ?_) h
    rfl

/-- **The graph of a smooth map is a split submanifold.** -/
theorem isSplitSubmanifold_graph (hU : IsOpen U) (hg : SmoothMBOn g U) :
    IsSplitSubmanifold (graph g U) (horizontal E G) := by
  refine ⟨⟨isClosed_horizontal, fun p hp ↦ ⟨graphChart hU (hg 0), ⟨?_, fun q hq ↦ ?_⟩, ?_⟩⟩,
    closedComplemented_horizontal⟩
  · exact StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ (graphChart_mem hU hg)
  · have hq1 : q.1 ∈ U := hq.1
    change (q.1 ∈ U ∧ q.2 = g q.1) ↔ (q.2 - g q.1 = 0)
    rw [sub_eq_zero]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hq1, h⟩⟩
  · exact ⟨hp.1, mem_univ _⟩

end Graph

end LCManifolds

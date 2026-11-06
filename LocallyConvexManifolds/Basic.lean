/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.MichalBastiani

/-!
# Manifolds modeled on locally convex spaces

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, Jpn. J. Math. 1 (2006),
291–468 (arXiv:1501.06269), §I.3; H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*
(arXiv:2602.12362), Ch. 3.

Mathlib's `ChartedSpace` and `StructureGroupoid` accept an arbitrary topological model space, so
a manifold modeled on `E` is a `ChartedSpace E M` with `HasGroupoid M (mbGroupoid E)`, where
`mbGroupoid E` consists of the Michal–Bastiani smooth diffeomorphisms between open subsets of `E`.

**Convention: the model space need not be complete.** The model space `E` is a Hausdorff locally
convex space, and *no completeness is assumed*. This is the convention of Glöckner–Neeb
(§5.7: "as for manifolds, we do not assume that the model space of a Lie group is complete",
following Glöckner 2002); Milnor (1984) assumed sequentially complete model spaces instead.

* The formal theory (charts, smooth maps, tangent bundle, vector fields, connections,
  submanifolds) does not use completeness: the calculus of `LocallyConvex.Analysis` replaces integrals in the
  model space by Hahn–Banach arguments.
* Every result that needs completeness says so in its hypotheses, and names the kind it needs
  (complete, sequentially complete, Mackey complete). Typically: integrals with values in the
  model space, ordinary differential equations and exponential maps, regularity of Lie groups,
  inverse function theorems.
* In particular, a manifold modeled on a normed space is **not** a Banach manifold unless the
  normed space is complete, and a manifold modeled on an inner product space is **not** a Hilbert
  manifold unless the space is complete. Statements about Banach or Hilbert manifolds in this
  library always carry the completeness hypothesis (`CompleteSpace`).
* Without completeness things do go wrong: Glöckner–Neeb, Example 5.6.8, give a Lie group
  modeled on an incomplete normed algebra (rational functions on `[0, 1]` with the sup norm)
  that has no exponential function.
-/

open Set
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

section Manifolds

variable (E)
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- The groupoid of Michal–Bastiani smooth diffeomorphisms between open subsets of `E`. -/
def mbGroupoid : StructureGroupoid E where
  members := {e | SmoothMBOn e e.source ∧ SmoothMBOn e.symm e.target}
  trans' e e' he he' := by
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · rw [OpenPartialHomeomorph.coe_trans]
      refine ContDiffMBOn.comp (e.trans e').open_source e'.open_source (he'.1 k)
        ((he.1 k).mono ?_) fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_source]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_source] at hx; exact hx.2
    · rw [OpenPartialHomeomorph.coe_trans_symm]
      refine ContDiffMBOn.comp (e.trans e').open_target e.open_target (he.2 k)
        ((he'.2 k).mono ?_) fun x hx ↦ ?_
      · rw [OpenPartialHomeomorph.trans_target]; exact inter_subset_left
      · rw [OpenPartialHomeomorph.trans_target] at hx; exact hx.2
  symm' := fun _ he ↦ ⟨he.2, he.1⟩
  id_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using smoothMBOn_id (univ : Set E)
  locality' e h := by
    refine ⟨fun k ↦ ContDiffMBOn.of_local e.open_source fun x hx ↦ ?_,
      fun k ↦ ContDiffMBOn.of_local e.open_target fun y hy ↦ ?_⟩
    · obtain ⟨s, hs, hxs, hes⟩ := h x hx
      refine ⟨s, hs, hxs, ?_⟩
      have := hes.1 k
      rwa [e.restr_source' s hs] at this
    · obtain ⟨s, hs, hxs, hes⟩ := h (e.symm y) (e.map_target hy)
      refine ⟨e.target ∩ e.symm ⁻¹' s, e.isOpen_inter_preimage_symm hs, ⟨hy, hxs⟩, ?_⟩
      have := hes.2 k
      have ht : (e.restr s).target = e.target ∩ e.symm ⁻¹' s := by
        rw [e.restr_toPartialEquiv' s hs]
        rfl
      rw [ht] at this
      rwa [← inter_assoc, inter_self]
  mem_of_eqOnSource' e e' he heq := by
    refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
    · rw [heq.source_eq]
      exact ContDiffMBOn.congr_of_isOpen e.open_source
        (fun x hx ↦ (heq.eqOn (heq.source_eq ▸ hx)).symm) (he.1 k)
    · have hs := heq.symm'
      change ContDiffMBOn k e'.symm e'.symm.source
      rw [hs.source_eq]
      exact ContDiffMBOn.congr_of_isOpen e.symm.open_source
        (fun x hx ↦ (hs.eqOn (hs.source_eq ▸ hx)).symm) (he.2 k)

/-- A smooth manifold modeled on the locally convex space `E` (Definition I.3.1). -/
abbrev MBManifold (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  HasGroupoid M (mbGroupoid E)

end Manifolds

section BanachHilbert

/-- A **Banach manifold**: a smooth manifold modeled on a Banach space `E`, i.e. a normed space
(`NormedAddCommGroup E`, `NormedSpace ℝ E`) which is complete (`CompleteSpace E`). On normed
spaces Michal–Bastiani smoothness agrees with Fréchet smoothness
(`LocallyConvex.Analysis.smoothMBOn_iff_contDiffOn`), so this is the classical notion (Lang). A manifold
modeled on an incomplete normed space is an `MBManifold`, but not a Banach manifold. -/
abbrev BanachManifold (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  MBManifold E M

/-- A **Hilbert manifold**: a smooth manifold modeled on a Hilbert space, i.e. a real inner
product space which is complete. -/
abbrev HilbertManifold (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  MBManifold E M

end BanachHilbert

end LocallyConvex.Manifolds

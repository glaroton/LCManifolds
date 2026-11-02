/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCAnalysis.MichalBastiani

/-!
# Manifolds modeled on locally convex spaces

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, Jpn. J. Math. 1 (2006),
291–468 (arXiv:1501.06269), §I.3; H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*
(arXiv:2602.12362), Ch. 3.

Mathlib's `ChartedSpace` and `StructureGroupoid` accept an arbitrary topological model space, so
a manifold modeled on `E` is a `ChartedSpace E M` with `HasGroupoid M (mbGroupoid E)`, where
`mbGroupoid E` consists of the Michal–Bastiani smooth diffeomorphisms between open subsets of `E`.
-/

open Set
open LCAnalysis

noncomputable section

namespace LCManifolds

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

end LCManifolds

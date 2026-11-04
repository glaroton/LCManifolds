/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Projector

/-!
# Example: a closed subspace

A closed subspace `S` of a locally convex space `F` is an embedded submanifold of `F`, with the
identity as slice chart (`isEmbeddedSubmanifold_subspace`); it is split when `S` is complemented.
Its tangent space at every point is `S` itself (`tangentSpace_subspace`). A continuous projection
`Pr` of `F` onto `S` is a constant field of projectors (`projectorField_subspace`). The connection
it defines is flat: its symbols vanish in the linear chart (`symb_subspace_refl`), and its
geodesics are the curves with zero acceleration, i.e. the affine lines
(`isGeodesic_subspace_iff`).
-/

open Set Filter
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {S : Submodule ℝ F}

/-- The identity is a slice chart for a subspace. -/
theorem isSliceChart_refl : IsSliceChart (S : Set F) S (OpenPartialHomeomorph.refl F) :=
  ⟨StructureGroupoid.id_mem_maximalAtlas (mbGroupoid F), fun _ _ ↦ Iff.rfl⟩

/-- **A closed subspace is an embedded submanifold.** -/
theorem isEmbeddedSubmanifold_subspace (hS : IsClosed (S : Set F)) :
    IsEmbeddedSubmanifold (S : Set F) S :=
  ⟨hS, fun _ _ ↦ ⟨_, isSliceChart_refl, mem_univ _⟩⟩

/-- A complemented subspace is a split submanifold. -/
theorem isSplitSubmanifold_subspace (hS : S.ClosedComplemented) :
    IsSplitSubmanifold (S : Set F) S :=
  ⟨isEmbeddedSubmanifold_subspace (hS.isClosed), hS⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- In the (identity) charts of the model spaces, the differential of the linear inclusion
`S → F` is the inclusion. -/
theorem dMB_chart_subtypeL (x : S) :
    (fun v : S ↦ dMB (chartAt F (S.subtypeL x) ∘ S.subtypeL ∘ (chartAt S x).symm)
      (chartAt S x x, v)) = ⇑S.subtypeL := by
  funext v
  change dMB (⇑S.subtypeL) (x, v) = S.subtypeL v
  exact (S.subtypeL.hasDirDerivAt x v).dMB_eq

/-- **The linear inclusion of a closed subspace is an immersion**: its differential is a
topological isomorphism onto the closed subspace `S`. -/
theorem isImmersion_subtypeL (hS : IsClosed (S : Set F)) : IsImmersion S F S.subtypeL := by
  refine ⟨fun k ↦ (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).mpr
    (S.subtypeL.contDiffMBOn k univ), fun x ↦ ?_⟩
  rw [dMB_chart_subtypeL]
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  have : range (⇑S.subtypeL) = (S : Set F) := by
    ext y
    simp
  rwa [this]

/-- **The linear inclusion of a subspace is a split immersion if and only if the subspace is
complemented.** -/
theorem isSplitImmersion_subtypeL_iff : IsSplitImmersion S F S.subtypeL ↔ S.ClosedComplemented := by
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨r, hr⟩ := h 0
    refine ⟨r, fun v ↦ ?_⟩
    have hd := congrFun (dMB_chart_subtypeL (S := S) 0) v
    have := hr v
    rwa [hd] at this
  · rintro ⟨r, hr⟩
    refine ⟨fun k ↦ (contMDiffMBOn_iff_contDiffMBOn isOpen_univ).mpr
      (S.subtypeL.contDiffMBOn k univ), fun x ↦ ⟨r, fun v ↦ ?_⟩⟩
    have hd := congrFun (dMB_chart_subtypeL (S := S) x) v
    rw [hd]
    exact hr v

/-- The tangent space of a closed subspace is the subspace itself. -/
theorem tangentSpace_subspace (hS : IsClosed (S : Set F)) (p : (S : Set F)) :
    (isEmbeddedSubmanifold_subspace hS).tangentSpace p = S := by
  ext w
  rw [(isEmbeddedSubmanifold_subspace hS).mem_tangentSpace_iff p isSliceChart_refl (mem_univ _)]
  have : dMB (OpenPartialHomeomorph.refl F) ((p : F), w) = w :=
    ((ContinuousLinearMap.id ℝ F).hasDirDerivAt _ _).dMB_eq
  rw [this]
  rfl

/-- **A continuous projection onto `S` is a constant field of projectors.** -/
def projectorField_subspace (hS : IsClosed (S : Set F)) (Pr : F →L[ℝ] F)
    (hidem : ∀ w, Pr (Pr w) = Pr w) (hrange : Set.range Pr = S) :
    ProjectorField (isEmbeddedSubmanifold_subspace hS) where
  E _ w := Pr w
  map_add _ := Pr.map_add
  map_smul _ c w := Pr.map_smul c w
  idem _ := hidem
  range_eq p := by rw [tangentSpace_subspace hS p, hrange]
  smooth _ _ := (Pr.comp (ContinuousLinearMap.snd ℝ S F)).smoothMBOn _

variable (hS : IsClosed (S : Set F)) (Pr : F →L[ℝ] F) (hidem : ∀ w, Pr (Pr w) = Pr w)
  (hrange : Set.range Pr = S)

/-- In the linear chart, the symbols of the connection vanish: the connection is flat. -/
theorem symb_subspace_refl (p₀ : (S : Set F)) (y a b : S) :
    (projectorField_subspace hS Pr hidem hrange).symb isSliceChart_refl p₀ y a b = 0 := by
  have hψ : ProjectorField.param (S := S) (OpenPartialHomeomorph.refl F) = ⇑S.subtypeL := rfl
  refine Subtype.ext ?_
  rw [ProjectorField.coe_symb _ _ _ (mem_univ (y : F)), hψ]
  have hd : dMB (⇑S.subtypeL) = fun p : S × S ↦ (p.2 : F) :=
    funext fun p ↦ (S.subtypeL.hasDirDerivAt _ _).dMB_eq
  have hd2 : dMB (dMB (⇑S.subtypeL)) ((y, b), (a, 0)) = 0 := by
    rw [hd]
    have := ((S.subtypeL.comp (ContinuousLinearMap.snd ℝ S S)).hasDirDerivAt (y, b) (a, 0)).dMB_eq
    exact this.trans (by simp)
  change -dMB (OpenPartialHomeomorph.refl F) (_, Pr (dMB (dMB (⇑S.subtypeL)) ((y, b), (a, 0)))) = _
  rw [hd2, map_zero]
  have h0 : dMB (OpenPartialHomeomorph.refl F) (((OpenPartialHomeomorph.refl F).symm y : F), 0) =
      0 := by
    have := ((ContinuousLinearMap.id ℝ F).hasDirDerivAt
      (((OpenPartialHomeomorph.refl F).symm y : F)) 0).dMB_eq
    simpa using this
  rw [h0, neg_zero]
  rfl

/-- **The geodesics of a closed subspace with a constant projector are the curves with zero
acceleration.** -/
theorem isGeodesic_subspace_iff {α : ℝ → (S : Set F)}
    (hα : letI := (isEmbeddedSubmanifold_subspace hS).chartedSpace; IsCkCurve S 2 α) :
    letI := (isEmbeddedSubmanifold_subspace hS).chartedSpace
    haveI := (isEmbeddedSubmanifold_subspace hS).mbManifold
    (projectorField_subspace hS Pr hidem hrange).connection.IsGeodesic α ↔
      ∀ t, dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1) = 0 := by
  let := (isEmbeddedSubmanifold_subspace hS).chartedSpace
  have := (isEmbeddedSubmanifold_subspace hS).mbManifold
  rw [ProjectorField.connection_isGeodesic_iff _ hα]
  -- in the linear chart `i`, `val ∘ α = S.subtypeL ∘ c` with `c = i ∘ α` of class `C²`
  set i : atlas S (S : Set F) :=
    ⟨sliceChart isSliceChart_refl (α 0), ⟨_, isSliceChart_refl, α 0, rfl⟩⟩
  have hsrc : α ⁻¹' (i : OpenPartialHomeomorph (S : Set F) S).source = univ :=
    eq_univ_of_forall fun _ ↦ mem_univ _
  have hc : ContDiffMBOn 2 ((i : OpenPartialHomeomorph (S : Set F) S) ∘ α) univ := by
    have := hα.2 i
    rwa [hsrc] at this
  set c := (i : OpenPartialHomeomorph (S : Set F) S) ∘ α
  have hval : Subtype.val ∘ α = ⇑S.subtypeL ∘ c :=
    funext fun s ↦ (sliceChart_apply_coe isSliceChart_refl (α 0) (q := α s) (mem_univ _)).symm
  have hc1 : ContDiffMBOn 1 c univ := hc.of_le (by norm_num)
  have hvel : (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) = ⇑S.subtypeL ∘ fun s ↦ dMB c (s, 1) := by
    funext s
    rw [hval, ContDiffMBOn.dMB_comp isOpen_univ (S.subtypeL.contDiffMBOn 1 univ) hc1
      (mapsTo_univ _ _) (mem_univ s) 1, (S.subtypeL.hasDirDerivAt _ _).dMB_eq]
    rfl
  have hdc : ContDiffMBOn 1 (fun s ↦ dMB c (s, 1)) univ := by
    have h2 : ContDiffMBOn 1 (dMB c) (univ ×ˢ univ) := hc.2.2
    have hpair : ContDiffMBOn 1 (fun s : ℝ ↦ (s, (1 : ℝ))) univ :=
      ((ContinuousLinearMap.id ℝ ℝ).contDiffMBOn 1 _).prodMk isOpen_univ (contDiffMBOn_const 1 1 _)
    exact ContDiffMBOn.comp (g := dMB c) (f := fun s : ℝ ↦ (s, (1 : ℝ))) isOpen_univ
      (isOpen_univ.prod isOpen_univ) h2 hpair fun s _ ↦ ⟨mem_univ _, mem_univ _⟩
  have hacc : ∀ t, dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1) =
      ((dMB (fun s ↦ dMB c (s, 1)) (t, 1) : S) : F) := by
    intro t
    rw [hvel, ContDiffMBOn.dMB_comp isOpen_univ (S.subtypeL.contDiffMBOn 1 univ) hdc
      (mapsTo_univ _ _) (mem_univ t) 1, (S.subtypeL.hasDirDerivAt _ _).dMB_eq]
    rfl
  -- `Pr` is the identity on `S`
  have hfix : ∀ x : S, Pr x = x := by
    intro x
    obtain ⟨w, hw⟩ : (x : F) ∈ Set.range Pr := by rw [hrange]; exact x.2
    rw [← hw, hidem]
  refine forall_congr' fun t ↦ ?_
  change Pr _ = 0 ↔ _
  rw [hacc t, hfix]

end LCManifolds

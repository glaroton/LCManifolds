/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.TangentMap

/-!
# Vector fields and the Lie bracket

Reference: K.-H. Neeb, *Towards a Lie theory of locally convex groups*, §I.3; H. Glöckner,
K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Ch. 3; S. Lang, *Fundamentals of Differential
Geometry*, §V.1.

A vector field on `M` is a section `X : M → TM` of the tangent bundle. In a chart `i` it has a
local representative `X̃ᵢ : i(U) → E`, and on chart overlaps `X̃ⱼ ∘ τ = dτ(·) X̃ᵢ(·)` for the
transition map `τ = j ∘ i⁻¹` (`localRep_transition`).

The Lie bracket is defined in the preferred chart at each point by the local formula
`[X, Y]~ = dỸ · X̃ − dX̃ · Ỹ`. In infinite dimensions vector fields need not have flows, so the
usual proof that this does not depend on the chart (through the Lie derivative along the flow)
is not available. We prove it directly (`localRep_lieBracket`): differentiating
`X̃ⱼ ∘ τ = dτ · X̃ᵢ` produces the second derivative `d²τ(X̃ᵢ, Ỹᵢ)`, which cancels in the bracket by
the symmetry of second derivatives.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

section Calculus

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- Derivatives in directions `(0, b)` are derivatives of the second slice. -/
theorem dMB_slice₂ {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    (g : E × E' → F) (x : E) (a b : E') :
    dMB g ((x, a), (0, b)) = dMB (fun w ↦ g (x, w)) (a, b) := by
  simp only [dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]

/-- The derivative of `y ↦ dτ(y)(a y)`: `d²τ(y)(v, a y) + dτ(y)(da(y) v)`. -/
theorem dMB_dMB_comp_apply {τ : E → F} {a : E → E} {T U : Set E} (hT : IsOpen T)
    (hU : IsOpen U) (hUT : U ⊆ T) (hτ : ContDiffMBOn 2 τ T) (ha : ContDiffMBOn 1 a U)
    {y : E} (hy : y ∈ U) (v : E) :
    dMB (fun y' ↦ dMB τ (y', a y')) (y, v) =
      dMB (dMB τ) ((y, a y), (v, 0)) + dMB τ (y, dMB a (y, v)) := by
  have hTU : IsOpen (T ×ˢ (univ : Set E)) := hT.prod isOpen_univ
  have hg : ContDiffMBOn 1 (dMB τ) (T ×ˢ univ) := hτ.2.2
  have hpair : ContDiffMBOn 1 (fun y' ↦ (y', a y')) U :=
    ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU ha
  have hcomp := ContDiffMBOn.dMB_comp hTU hg hpair (fun y' hy' ↦ ⟨hUT hy', mem_univ _⟩) hy v
  have hdpair : dMB (fun y' ↦ (y', a y')) (y, v) = (v, dMB a (y, v)) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt y v).prodMk (ha.hasDirDerivAt hy v)).dMB_eq
  have hsplit : (v, dMB a (y, v)) = (v, (0 : E)) + (0, dMB a (y, v)) := by simp
  change dMB (dMB τ ∘ fun y' ↦ (y', a y')) (y, v) = _
  rw [hcomp, hdpair, hsplit, hg.dMB_add hTU ⟨hUT hy, mem_univ _⟩, dMB_slice₂]
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT (hUT hy)
  have hfun : (fun w ↦ dMB τ (y, w)) = ⇑L := funext fun w ↦ (hL w).symm
  rw [hfun, (L.hasDirDerivAt _ _).dMB_eq, hL]

/-- The local Lie bracket of two vector fields on an open subset of `E`:
`[X, Y](y) = dY(y) X(y) − dX(y) Y(y)`. -/
def localBracket (X Y : E → E) (y : E) : E := dMB Y (y, X y) - dMB X (y, Y y)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem localBracket_swap (X Y : E → E) (y : E) :
    localBracket Y X y = -localBracket X Y y := by
  simp [localBracket]

/-- The local bracket transforms like a vector field under a change of coordinates `τ`: if
`Xⱼ ∘ τ = dτ · Xᵢ` and `Yⱼ ∘ τ = dτ · Yᵢ` near `y`, then
`[Xⱼ, Yⱼ](τ y) = dτ(y) [Xᵢ, Yᵢ](y)`. The second derivatives of `τ` cancel by symmetry. -/
theorem localBracket_transition {τ : E → E} {Xᵢ Yᵢ Xⱼ Yⱼ : E → E} {T U V : Set E}
    (hT : IsOpen T) (hU : IsOpen U) (hV : IsOpen V) (hUT : U ⊆ T) (hτ : ContDiffMBOn 2 τ T)
    (hUV : MapsTo τ U V) (hXᵢ : ContDiffMBOn 1 Xᵢ U) (hYᵢ : ContDiffMBOn 1 Yᵢ U)
    (hXⱼ : ContDiffMBOn 1 Xⱼ V) (hYⱼ : ContDiffMBOn 1 Yⱼ V)
    (hX : ∀ y ∈ U, Xⱼ (τ y) = dMB τ (y, Xᵢ y)) (hY : ∀ y ∈ U, Yⱼ (τ y) = dMB τ (y, Yᵢ y))
    {y : E} (hy : y ∈ U) :
    localBracket Xⱼ Yⱼ (τ y) = dMB τ (y, localBracket Xᵢ Yᵢ y) := by
  have hτ1 : ContDiffMBOn 1 τ U := (hτ.of_le (by norm_num)).mono hUT
  -- differentiating `Zⱼ ∘ τ = dτ · Zᵢ`
  have key : ∀ {Zᵢ Zⱼ : E → E}, ContDiffMBOn 1 Zᵢ U → ContDiffMBOn 1 Zⱼ V →
      (∀ y ∈ U, Zⱼ (τ y) = dMB τ (y, Zᵢ y)) → ∀ w,
      dMB Zⱼ (τ y, dMB τ (y, w)) =
        dMB (dMB τ) ((y, Zᵢ y), (w, 0)) + dMB τ (y, dMB Zᵢ (y, w)) := by
    intro Zᵢ Zⱼ hZᵢ hZⱼ hZ w
    have hev : Zⱼ ∘ τ =ᶠ[𝓝 y] fun y' ↦ dMB τ (y', Zᵢ y') :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hy) fun y' hy' ↦ hZ y' hy'
    rw [← dMB_dMB_comp_apply hT hU hUT hτ hZᵢ hy w, ← dMB_congr_of_eventuallyEq hev,
      ContDiffMBOn.dMB_comp hV hZⱼ hτ1 hUV hy w]
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT (hUT hy)
  rw [localBracket, localBracket, hX y hy, hY y hy, key hYᵢ hYⱼ hY, key hXᵢ hXⱼ hX,
    hτ.dMB_dMB_symm hT (hUT hy) (Yᵢ y) (Xᵢ y), ← hL, ← hL, ← hL, map_sub]
  abel

end Calculus

section VectorFields

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- A vector field: a section of the tangent bundle. -/
def IsVectorField (X : M → TangentBundle E M) : Prop := ∀ x, (X x).proj = x

/-- The local representative `X̃ᵢ : i(U) → E` of `X` in the chart `i`. -/
def localRep (i : atlas E M) (X : M → TangentBundle E M) (y : E) : E :=
  (tangentChart i i.1 (X (i.1.symm y))).2

/-- The charts of the tangent bundle over charts of the atlas are in its atlas. -/
theorem tangentChart_mem_atlas (i : atlas E M) :
    tangentChart i i.1 ∈ atlas (E × E) (TangentBundle E M) :=
  ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, _, ⟨i.1, i.2, OpenPartialHomeomorph.refl E,
    chartedSpaceSelf_atlas.mpr rfl, rfl⟩, rfl⟩

/-- On chart overlaps, `X̃ⱼ ∘ τ = dτ · X̃ᵢ` for the transition map `τ = j ∘ i⁻¹`. -/
theorem localRep_transition {X : M → TangentBundle E M} (hX : IsVectorField X)
    (i j : atlas E M) {y : E} (hy : y ∈ i.1.target) (hyj : i.1.symm y ∈ j.1.source) :
    localRep j X ((j.1 ∘ i.1.symm) y) = dMB (j.1 ∘ i.1.symm) (y, localRep i X y) := by
  set q := i.1.symm y
  have hq : q ∈ i.1.source := i.1.map_target hy
  have e1 : j.1.symm ((j.1 ∘ i.1.symm) y) = q := by
    simp only [Function.comp_apply, q, j.1.left_inv hyj]
  unfold localRep
  rw [e1]
  have hXq : (X q).proj = q := hX q
  generalize X q = p at hXq ⊢
  obtain ⟨xp, v⟩ := p
  change xp = q at hXq
  subst hXq
  rw [tangentChart_apply, tangentChart_apply]
  have key : ∀ w : E, tangentCoordChange ⟨chartAt E q, chart_mem_atlas E q⟩ j q w =
      dMB (j.1 ∘ i.1.symm) (y, tangentCoordChange ⟨chartAt E q, chart_mem_atlas E q⟩ i q w) := by
    intro w
    rw [← tangentCoordChange_comp ⟨chartAt E q, chart_mem_atlas E q⟩ i j
      ⟨⟨mem_chart_source E q, hq⟩, hyj⟩, tangentCoordChange, i.1.right_inv hy]
  exact key v

/-- The local representatives of a `C^k` vector field are `C^k`. -/
theorem contDiffMBOn_localRep {k : ℕ} {X : M → TangentBundle E M} (hXv : IsVectorField X)
    (hX : ContMDiffMB E (E × E) k X) (i : atlas E M) :
    ContDiffMBOn k (localRep i X) i.1.target := by
  have h := hX.contDiffMBOn_chart isOpen_univ i.2 (tangentChart_mem_atlas i)
  have hsub : i.1.target ⊆ chartDomain X univ i.1 (tangentChart i i.1) := by
    intro y hy
    refine ⟨hy, mem_univ _, ?_⟩
    rw [mem_preimage, mem_tangentChart_source, hXv]
    exact ⟨i.1.map_target hy, i.1.map_target hy⟩
  exact ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn k univ).comp i.1.open_target isOpen_univ
    (h.mono hsub) (mapsTo_univ _ _)

/-- The Lie bracket of two vector fields, computed in the preferred chart at each point by the
local formula `dỸ · X̃ − dX̃ · Ỹ`. -/
def lieBracket (X Y : M → TangentBundle E M) (x : M) : TangentBundle E M :=
  ⟨x, (localBracket (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X)
    (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y) (chartAt E x x) : E)⟩

theorem isVectorField_lieBracket (X Y : M → TangentBundle E M) :
    IsVectorField (lieBracket X Y) :=
  fun _ ↦ rfl

/-- **The Lie bracket does not depend on the chart**: in every chart `j` of the atlas, the local
representative of `[X, Y]` is the local bracket of the local representatives of `X` and `Y`. -/
theorem localRep_lieBracket {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hX : ContMDiffMB E (E × E) 1 X) (hY : ContMDiffMB E (E × E) 1 Y)
    (j : atlas E M) {y : E} (hy : y ∈ j.1.target) :
    localRep j (lieBracket X Y) y = localBracket (localRep j X) (localRep j Y) y := by
  set x := j.1.symm y
  have hxj : x ∈ j.1.source := j.1.map_target hy
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hxi : x ∈ i.1.source := mem_chart_source E x
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hτ : ContDiffMBOn 2 (j.1 ∘ i.1.symm) T := smoothMBOn_transition' i j 2
  have hmaps : MapsTo (j.1 ∘ i.1.symm) T j.1.target := fun z hz ↦ j.1.map_source hz.2
  have hix : i.1 x ∈ T := ⟨i.1.map_source hxi, by simp [i.1.left_inv hxi, hxj]⟩
  have hτx : (j.1 ∘ i.1.symm) (i.1 x) = y := by
    simp [i.1.left_inv hxi, x, j.1.right_inv hy]
  have hTi : T ⊆ i.1.target := inter_subset_left
  have htrans := localBracket_transition hT hT j.1.open_target subset_rfl hτ hmaps
    ((contDiffMBOn_localRep hXv hX i).mono hTi) ((contDiffMBOn_localRep hYv hY i).mono hTi)
    (contDiffMBOn_localRep hXv hX j) (contDiffMBOn_localRep hYv hY j)
    (fun z hz ↦ localRep_transition hXv i j hz.1 hz.2)
    (fun z hz ↦ localRep_transition hYv i j hz.1 hz.2) hix
  rw [hτx] at htrans
  rw [htrans]
  rfl

/-- Antisymmetry of the Lie bracket. -/
theorem lieBracket_swap (X Y : M → TangentBundle E M) (x : M) :
    (lieBracket Y X x).2 = -(lieBracket X Y x).2 :=
  localBracket_swap (E := E) _ _ _

end VectorFields

end LCManifolds

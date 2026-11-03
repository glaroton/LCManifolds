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
theorem localBracket_transition {τ : E → F} {Xᵢ Yᵢ : E → E} {Xⱼ Yⱼ : F → F} {T U : Set E}
    {V : Set F}
    (hT : IsOpen T) (hU : IsOpen U) (hV : IsOpen V) (hUT : U ⊆ T) (hτ : ContDiffMBOn 2 τ T)
    (hUV : MapsTo τ U V) (hXᵢ : ContDiffMBOn 1 Xᵢ U) (hYᵢ : ContDiffMBOn 1 Yᵢ U)
    (hXⱼ : ContDiffMBOn 1 Xⱼ V) (hYⱼ : ContDiffMBOn 1 Yⱼ V)
    (hX : ∀ y ∈ U, Xⱼ (τ y) = dMB τ (y, Xᵢ y)) (hY : ∀ y ∈ U, Yⱼ (τ y) = dMB τ (y, Yᵢ y))
    {y : E} (hy : y ∈ U) :
    localBracket Xⱼ Yⱼ (τ y) = dMB τ (y, localBracket Xᵢ Yᵢ y) := by
  have hτ1 : ContDiffMBOn 1 τ U := (hτ.of_le (by norm_num)).mono hUT
  -- differentiating `Zⱼ ∘ τ = dτ · Zᵢ`
  have key : ∀ {Zᵢ : E → E} {Zⱼ : F → F}, ContDiffMBOn 1 Zᵢ U → ContDiffMBOn 1 Zⱼ V →
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

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The derivative of a local bracket:
`d[Y, Z](y) v = d²Z(y)(v, Y y) + dZ(y)(dY(y) v) − d²Y(y)(v, Z y) − dY(y)(dZ(y) v)`. -/
theorem dMB_localBracket {Y Z : E → E} {U : Set E} (hU : IsOpen U) (hY : ContDiffMBOn 2 Y U)
    (hZ : ContDiffMBOn 2 Z U) {y : E} (hy : y ∈ U) (v : E) :
    dMB (localBracket Y Z) (y, v) =
      (dMB (dMB Z) ((y, Y y), (v, 0)) + dMB Z (y, dMB Y (y, v))) -
        (dMB (dMB Y) ((y, Z y), (v, 0)) + dMB Y (y, dMB Z (y, v))) := by
  have hUU : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  -- `y ↦ dZ(y)(Y y)` is `C^1`
  have hc : ∀ {A B : E → E}, ContDiffMBOn 2 A U → ContDiffMBOn 2 B U →
      ContDiffMBOn 1 (fun y' ↦ dMB A (y', B y')) U := by
    intro A B hA hB
    have hpair : ContDiffMBOn 1 (fun y' ↦ (y', B y')) U :=
      ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU (hB.of_le (by norm_num))
    have hdA : ContDiffMBOn 1 (dMB A) (U ×ˢ univ) := hA.2.2
    exact ContDiffMBOn.comp (g := dMB A) (f := fun y' ↦ (y', B y')) hU hUU hdA hpair
      fun y' hy' ↦ ⟨hy', mem_univ _⟩
  have h₁ := (hc hZ hY).hasDirDerivAt (k := 0) hy v
  have h₂ := (hc hY hZ).hasDirDerivAt (k := 0) hy v
  change dMB (fun y' ↦ dMB Z (y', Y y') - dMB Y (y', Z y')) (y, v) = _
  rw [(h₁.sub h₂).dMB_eq, ← dMB_dMB_comp_apply hU hU subset_rfl hZ (hY.of_le (by norm_num)) hy,
    ← dMB_dMB_comp_apply hU hU subset_rfl hY (hZ.of_le (by norm_num)) hy]

omit [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The Jacobi identity for local brackets of `C^2` vector fields. -/
theorem localBracket_jacobi {X Y Z : E → E} {U : Set E} (hU : IsOpen U)
    (hX : ContDiffMBOn 2 X U) (hY : ContDiffMBOn 2 Y U) (hZ : ContDiffMBOn 2 Z U) {y : E}
    (hy : y ∈ U) :
    localBracket X (localBracket Y Z) y + localBracket Y (localBracket Z X) y +
      localBracket Z (localBracket X Y) y = 0 := by
  have hb : ∀ A B : E → E, localBracket A B y = dMB B (y, A y) - dMB A (y, B y) :=
    fun _ _ ↦ rfl
  rw [hb X (localBracket Y Z), hb Y (localBracket Z X), hb Z (localBracket X Y),
    dMB_localBracket hU hY hZ hy, dMB_localBracket hU hZ hX hy,
    dMB_localBracket hU hX hY hy]
  simp only [localBracket]
  obtain ⟨LX, hLX⟩ := (hX.of_le (by norm_num) : ContDiffMBOn 1 X U).exists_clm hU hy
  obtain ⟨LY, hLY⟩ := (hY.of_le (by norm_num) : ContDiffMBOn 1 Y U).exists_clm hU hy
  obtain ⟨LZ, hLZ⟩ := (hZ.of_le (by norm_num) : ContDiffMBOn 1 Z U).exists_clm hU hy
  rw [hZ.dMB_dMB_symm hU hy (Y y) (X y), hY.dMB_dMB_symm hU hy (Z y) (X y),
    hX.dMB_dMB_symm hU hy (Z y) (Y y)]
  simp only [← hLX, ← hLY, ← hLZ, map_sub]
  abel

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The local bracket at `y` only depends on the germ of the second field at `y`. -/
theorem localBracket_congr_right {A W W' : E → E} {y : E} (h : W =ᶠ[𝓝 y] W') :
    localBracket A W y = localBracket A W' y := by
  rw [localBracket, localBracket, dMB_congr_of_eventuallyEq h, h.eq_of_nhds]

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

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem ContMDiffMB.of_le' {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    {N : Type*} [TopologicalSpace N] [ChartedSpace F N] {k l : ℕ} {f : M → N}
    (hf : ContMDiffMB E F k f) (hlk : l ≤ k) : ContMDiffMB E F l f :=
  ⟨hf.1, fun x hx ↦ (hf.2 x hx).of_le hlk⟩

/-- Near a point, the local representative of `[Y, Z]` in a chart is the local bracket of the
local representatives. -/
theorem localRep_lieBracket_eventuallyEq {Y Z : M → TangentBundle E M} (hYv : IsVectorField Y)
    (hZv : IsVectorField Z) (hY : ContMDiffMB E (E × E) 1 Y) (hZ : ContMDiffMB E (E × E) 1 Z)
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) :
    localRep i (lieBracket Y Z) =ᶠ[𝓝 y] localBracket (localRep i Y) (localRep i Z) :=
  Filter.eventuallyEq_of_mem (i.1.open_target.mem_nhds hy)
    fun _ hz ↦ localRep_lieBracket hYv hZv hY hZ i hz

/-- **The Jacobi identity** for `C^2` vector fields. -/
theorem lieBracket_jacobi {X Y Z : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hZv : IsVectorField Z) (hX : ContMDiffMB E (E × E) 2 X)
    (hY : ContMDiffMB E (E × E) 2 Y) (hZ : ContMDiffMB E (E × E) 2 Z) (x : M) :
    (show E from (lieBracket X (lieBracket Y Z) x).2) +
      (show E from (lieBracket Y (lieBracket Z X) x).2) +
      (show E from (lieBracket Z (lieBracket X Y) x).2) = 0 := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hX1 := hX.of_le' (by norm_num : 1 ≤ 2)
  have hY1 := hY.of_le' (by norm_num : 1 ≤ 2)
  have hZ1 := hZ.of_le' (by norm_num : 1 ≤ 2)
  change localBracket (localRep i X) (localRep i (lieBracket Y Z)) (i.1 x) +
      localBracket (localRep i Y) (localRep i (lieBracket Z X)) (i.1 x) +
      localBracket (localRep i Z) (localRep i (lieBracket X Y)) (i.1 x) = 0
  rw [localBracket_congr_right (localRep_lieBracket_eventuallyEq hYv hZv hY1 hZ1 i hx),
    localBracket_congr_right (localRep_lieBracket_eventuallyEq hZv hXv hZ1 hX1 i hx),
    localBracket_congr_right (localRep_lieBracket_eventuallyEq hXv hYv hX1 hY1 i hx)]
  exact localBracket_jacobi i.1.open_target (contDiffMBOn_localRep hXv hX i)
    (contDiffMBOn_localRep hYv hY i) (contDiffMBOn_localRep hZv hZ i) hx

end VectorFields

section Related

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [MBManifold F N]

/-- `X` and `X'` are `f`-related: `Tf ∘ X = X' ∘ f`. -/
def IsRelated (f : M → N) (X : M → TangentBundle E M) (X' : N → TangentBundle F N) : Prop :=
  ∀ x, tangentMap E F f (X x) = X' (f x)

/-- For `f`-related fields, the local representatives in charts `i` of `M` and `j` of `N` satisfy
`X̃'ⱼ ∘ h = dh · X̃ᵢ`, where `h = j ∘ f ∘ i⁻¹`. -/
theorem localRep_related {f : M → N} (hf : ContMDiffMB E F 1 f) {X : M → TangentBundle E M}
    {X' : N → TangentBundle F N} (hXv : IsVectorField X) (hXX' : IsRelated f X X')
    (i : atlas E M) (j : atlas F N) {y : E} (hy : y ∈ i.1.target)
    (hfy : f (i.1.symm y) ∈ j.1.source) :
    localRep j X' ((j.1 ∘ f ∘ i.1.symm) y) = dMB (j.1 ∘ f ∘ i.1.symm) (y, localRep i X y) := by
  set q := i.1.symm y
  have hq : q ∈ i.1.source := i.1.map_target hy
  have hsrc : X q ∈ (tangentChart i i.1).source := by
    rw [mem_tangentChart_source, hXv]; exact ⟨hq, hq⟩
  have hXq : tangentChart i i.1 (X q) = (y, localRep i X y) := by
    refine Prod.ext ?_ rfl
    rw [tangentChart_apply]
    change i.1 (X q).proj = y
    rw [hXv, i.1.right_inv hy]
  have hrep := tangentMap_chart hf i j hy hfy (localRep i X y)
  rw [← hXq, (tangentChart i i.1).left_inv hsrc, hXX' q] at hrep
  have e1 : j.1.symm ((j.1 ∘ f ∘ i.1.symm) y) = f q := by
    simp only [Function.comp_apply, q, j.1.left_inv hfy]
  unfold localRep
  rw [e1, hrep, hXq]

/-- **Brackets of related fields are related** (Lang, Prop. V.1.4): if `X, Y` are `f`-related
to `X', Y'`, then `[X, Y]` is `f`-related to `[X', Y']`. -/
theorem lieBracket_related {f : M → N} (hf : ContMDiffMB E F 2 f)
    {X Y : M → TangentBundle E M} {X' Y' : N → TangentBundle F N} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hX'v : IsVectorField X') (hY'v : IsVectorField Y')
    (hX : ContMDiffMB E (E × E) 1 X) (hY : ContMDiffMB E (E × E) 1 Y)
    (hX' : ContMDiffMB F (F × F) 1 X') (hY' : ContMDiffMB F (F × F) 1 Y')
    (hXX' : IsRelated f X X') (hYY' : IsRelated f Y Y') :
    IsRelated f (lieBracket X Y) (lieBracket X' Y') := by
  intro x
  have hf1 := hf.of_le' (by norm_num : 1 ≤ 2)
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  set j : atlas F N := ⟨chartAt F (f x), chart_mem_atlas F (f x)⟩
  set U := chartDomain f univ i.1 j.1
  have hU : IsOpen U := isOpen_chartDomain isOpen_univ hf.1 i.1 j.1
  have hh : ContDiffMBOn 2 (j.1 ∘ f ∘ i.1.symm) U := hf.2 x (mem_univ x)
  have hmaps : MapsTo (j.1 ∘ f ∘ i.1.symm) U j.1.target := fun z hz ↦ j.1.map_source hz.2.2
  have hUi : U ⊆ i.1.target := inter_subset_left
  have hxU : i.1 x ∈ U := ⟨i.1.map_source (mem_chart_source E x), mem_univ _, by
    simp [i, j, i.1.left_inv (mem_chart_source E x), mem_chart_source]⟩
  have htrans := localBracket_transition hU hU j.1.open_target subset_rfl hh hmaps
    ((contDiffMBOn_localRep hXv hX i).mono hUi) ((contDiffMBOn_localRep hYv hY i).mono hUi)
    (contDiffMBOn_localRep hX'v hX' j) (contDiffMBOn_localRep hY'v hY' j)
    (fun z hz ↦ localRep_related hf1 hXv hXX' i j hz.1 hz.2.2)
    (fun z hz ↦ localRep_related hf1 hYv hYY' i j hz.1 hz.2.2) hxU
  have hfx : (j.1 ∘ f ∘ i.1.symm) (i.1 x) = j.1 (f x) := by
    simp [i, i.1.left_inv (mem_chart_source E x)]
  rw [hfx] at htrans
  change (⟨f x, (dMB (j.1 ∘ f ∘ i.1.symm)
      (i.1 x, localBracket (localRep i X) (localRep i Y) (i.1 x)) : F)⟩ : TangentBundle F N) =
    ⟨f x, (localBracket (localRep j X') (localRep j Y') (j.1 (f x)) : F)⟩
  rw [htrans]

end Related

end LCManifolds

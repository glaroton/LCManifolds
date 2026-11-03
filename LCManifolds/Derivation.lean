/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.VectorField

/-!
# Vector fields acting on functions

Reference: S. Lang, *Fundamentals of Differential Geometry*, §V.1; K.-H. Neeb, *Towards a Lie
theory of locally convex groups*, §I.3.

A vector field `X` acts on `C^1` functions `φ : M → ℝ` by `X(φ)(x) = dφ(x) X(x)`, computed in a
chart: `X(φ)(x) = d(φ ∘ c⁻¹)(c x) X̃(c x)`. We show that this does not depend on the chart
(`vfDeriv_chart`) and the Leibniz rule `X(φψ) = X(φ) ψ + φ X(ψ)`.

Smooth bump functions need not exist on manifolds modeled on locally convex spaces, so vector
fields are not determined by their action on *global* functions in general; they are determined
by their action on functions defined on chart domains, such as `λ ∘ c` for continuous linear
functionals `λ` (Hahn–Banach).

Functions `φ : M → ℝ` are treated through their local representatives `φ ∘ i⁻¹` in the charts of
the atlas (`IsCkFunction`), since `ℝ` is not a model space in the universe of `E`.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

section Calculus

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The product rule for a scalar function times a vector-valued function. -/
theorem HasDirDerivAt.smul_fun {g : E → ℝ} {Y : E → F} {y v : E} {a : ℝ} {b : F}
    (hg : HasDirDerivAt g y v a) (hgc : ContinuousAt g y) (hY : HasDirDerivAt Y y v b) :
    HasDirDerivAt (fun z ↦ g z • Y z) y v (a • Y y + g y • b) := by
  have hl : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[≠] 0) (𝓝 y) := by
    have : Continuous fun t : ℝ ↦ y + t • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgl : Tendsto (fun t : ℝ ↦ g (y + t • v)) (𝓝[≠] 0) (𝓝 (g y)) := hgc.tendsto.comp hl
  have h1 := hgl.smul hY
  have h2 := hg.smul_const (Y y)
  refine (h2.add h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  simp only [smul_eq_mul]
  module

end Calculus

section Functions

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E) in
/-- `φ : M → ℝ` is `C^k`: its local representatives in the charts of the atlas are `C^k`. -/
def IsCkFunction (k : ℕ) (φ : M → ℝ) : Prop :=
  ∀ i : atlas E M, ContDiffMBOn k (φ ∘ i.1.symm) i.1.target

/-- The derivative `X(φ)(x) = dφ(x) X(x)` of a function along a vector field, computed in the
preferred chart at `x`. -/
def vfDeriv (X : M → TangentBundle E M) (φ : M → ℝ) (x : M) : ℝ :=
  dMB (φ ∘ (chartAt E x).symm)
    (chartAt E x x, localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X (chartAt E x x))

/-- `X(φ)` does not depend on the chart. -/
theorem vfDeriv_chart {X : M → TangentBundle E M} (hXv : IsVectorField X) {φ : M → ℝ}
    (hφ : IsCkFunction E 1 φ) (j : atlas E M) {x : M} (hx : x ∈ j.1.source) :
    vfDeriv X φ x = dMB (φ ∘ j.1.symm) (j.1 x, localRep j X (j.1 x)) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hxi : x ∈ i.1.source := mem_chart_source E x
  set T := i.1.target ∩ i.1.symm ⁻¹' j.1.source
  have hT : IsOpen T := isOpen_transition_domain i j
  have hix : i.1 x ∈ T := ⟨i.1.map_source hxi, by simp [i.1.left_inv hxi, hx]⟩
  have hτx : (j.1 ∘ i.1.symm) (i.1 x) = j.1 x := by simp [i.1.left_inv hxi]
  have htr := localRep_transition hXv i j hix.1 hix.2
  rw [hτx] at htr
  have hev : φ ∘ i.1.symm =ᶠ[𝓝 (i.1 x)] (φ ∘ j.1.symm) ∘ (j.1 ∘ i.1.symm) :=
    Filter.eventuallyEq_of_mem (hT.mem_nhds hix) fun z hz ↦ by
      simp [j.1.left_inv hz.2]
  have hτ : ContDiffMBOn 1 (j.1 ∘ i.1.symm) T := smoothMBOn_transition' i j 1
  have hmaps : MapsTo (j.1 ∘ i.1.symm) T j.1.target := fun z hz ↦ j.1.map_source hz.2
  change dMB (φ ∘ i.1.symm) (i.1 x, localRep i X (i.1 x)) = _
  rw [dMB_congr_of_eventuallyEq hev, ContDiffMBOn.dMB_comp j.1.open_target (hφ j) hτ hmaps hix,
    hτx, htr]

/-- The Leibniz rule `X(φψ) = X(φ) ψ + φ X(ψ)`. -/
theorem vfDeriv_mul (X : M → TangentBundle E M) {φ ψ : M → ℝ} (hφ : IsCkFunction E 1 φ)
    (hψ : IsCkFunction E 1 ψ) (x : M) :
    vfDeriv X (fun z ↦ φ z * ψ z) x = vfDeriv X φ x * ψ x + φ x * vfDeriv X ψ x := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hd := (hφ i).hasDirDerivAt (k := 0) hx (localRep i X (i.1 x))
  have hc : ContinuousAt (φ ∘ i.1.symm) (i.1 x) :=
    (hφ i).continuousOn.continuousAt (i.1.open_target.mem_nhds hx)
  have hd' := HasDirDerivAt.smul_fun hd hc
    ((hψ i).hasDirDerivAt (k := 0) hx (localRep i X (i.1 x)))
  have hxx : i.1.symm (i.1 x) = x := i.1.left_inv (mem_chart_source E x)
  change dMB (fun z ↦ (φ ∘ i.1.symm) z • (ψ ∘ i.1.symm) z)
    (i.1 x, localRep i X (i.1 x)) = _
  rw [hd'.dMB_eq]
  simp only [smul_eq_mul, Function.comp_apply, hxx]
  change _ = dMB (φ ∘ i.1.symm) (i.1 x, _) * ψ x + φ x * dMB (ψ ∘ i.1.symm) (i.1 x, _)
  ring

/-- The value of a vector field at `q`, read in the preferred chart at `q`, is its fiber
coordinate. -/
theorem localRep_chartAt {Z : M → TangentBundle E M} (hZv : IsVectorField Z) (q : M) :
    localRep ⟨chartAt E q, chart_mem_atlas E q⟩ Z (chartAt E q q) = (Z q).2 := by
  unfold localRep
  rw [(chartAt E q).left_inv (mem_chart_source E q)]
  have hp : (Z q).proj = q := hZv q
  generalize Z q = p at hp ⊢
  obtain ⟨xp, v⟩ := p
  change xp = q at hp
  subst hp
  exact tangentCoordChange_self ⟨chartAt E xp, chart_mem_atlas E xp⟩ (mem_chart_source E xp) v

/-- The product `φ Y` of a function and a vector field. -/
def smulField (φ : M → ℝ) (Y : M → TangentBundle E M) (x : M) : TangentBundle E M :=
  ⟨x, (φ x • localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y (chartAt E x x) : E)⟩

theorem isVectorField_smulField (φ : M → ℝ) (Y : M → TangentBundle E M) :
    IsVectorField (smulField φ Y) :=
  fun _ ↦ rfl

/-- In a chart, `(φ Y)~ = (φ ∘ i⁻¹) Ỹ`. -/
theorem localRep_smulField {Y : M → TangentBundle E M} (hYv : IsVectorField Y) (φ : M → ℝ)
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) :
    localRep i (smulField φ Y) y = (φ ∘ i.1.symm) y • localRep i Y y := by
  set q := i.1.symm y
  have hq : q ∈ i.1.source := i.1.map_target hy
  set iq : atlas E M := ⟨chartAt E q, chart_mem_atlas E q⟩
  have hlin : ∀ (a : ℝ) (w : E), tangentCoordChange iq i q (a • w) =
      a • tangentCoordChange iq i q w := fun a w ↦
    (smoothMBOn_transition' iq i 1).dMB_smul
      ⟨iq.1.map_source (mem_chart_source E q), by simp [iq, (chartAt E q).left_inv
        (mem_chart_source E q), hq]⟩ a w
  have hrep : localRep i Y y = tangentCoordChange iq i q (localRep iq Y (iq.1 q)) := by
    rw [localRep_chartAt hYv q]
    unfold localRep
    have hp : (Y q).proj = q := hYv q
    generalize Y q = p at hp ⊢
    obtain ⟨xp, v⟩ := p
    change xp = q at hp
    subst hp
    rfl
  rw [hrep, ← hlin]
  rfl

/-- **The Leibniz rule** `[X, φ Y] = X(φ) Y + φ [X, Y]`, in the fiber at `x`. -/
theorem lieBracket_smulField {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hX : ContMDiffMB E (E × E) 1 X) (hY : ContMDiffMB E (E × E) 1 Y)
    {φ : M → ℝ} (hφ : IsCkFunction E 1 φ) (x : M) :
    (show E from (lieBracket X (smulField φ Y) x).2) =
      vfDeriv X φ x • (show E from (Y x).2) + φ x • (show E from (lieBracket X Y x).2) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hxx : i.1.symm (i.1 x) = x := i.1.left_inv (mem_chart_source E x)
  have hev : localRep i (smulField φ Y) =ᶠ[𝓝 (i.1 x)]
      fun y ↦ (φ ∘ i.1.symm) y • localRep i Y y :=
    Filter.eventuallyEq_of_mem (i.1.open_target.mem_nhds hx)
      fun _ hy ↦ localRep_smulField hYv φ i hy
  have hXi := contDiffMBOn_localRep hXv hX i
  have hYi := contDiffMBOn_localRep hYv hY i
  have hd := HasDirDerivAt.smul_fun ((hφ i).hasDirDerivAt (k := 0) hx (localRep i X (i.1 x)))
    ((hφ i).continuousOn.continuousAt (i.1.open_target.mem_nhds hx))
    (hYi.hasDirDerivAt (k := 0) hx (localRep i X (i.1 x)))
  change localBracket (localRep i X) (localRep i (smulField φ Y)) (i.1 x) =
    vfDeriv X φ x • (show E from (Y x).2) +
      φ x • localBracket (localRep i X) (localRep i Y) (i.1 x)
  rw [localBracket_congr_right hev, ← localRep_chartAt hYv x]
  unfold localBracket
  rw [hd.dMB_eq, hXi.dMB_smul hx]
  simp only [Function.comp_apply, hxx]
  change _ = dMB (φ ∘ i.1.symm) (i.1 x, localRep i X (i.1 x)) • _ + _
  rw [smul_sub]
  abel

/-- On the domain of a chart `c`, the derivative of the local function `λ ∘ c` (for a continuous
linear functional `λ`) along `X` is `λ` applied to the local representative of `X`. -/
theorem vfDeriv_clm_comp_chart {X : M → TangentBundle E M} (hXv : IsVectorField X)
    (c : atlas E M) (l : E →L[ℝ] ℝ) {x : M} (hx : x ∈ c.1.source) :
    vfDeriv X (fun z ↦ l (c.1 z)) x = l (localRep c X (c.1 x)) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hxi : x ∈ i.1.source := mem_chart_source E x
  set T := i.1.target ∩ i.1.symm ⁻¹' c.1.source
  have hT : IsOpen T := isOpen_transition_domain i c
  have hix : i.1 x ∈ T := ⟨i.1.map_source hxi, by simp [i.1.left_inv hxi, hx]⟩
  have hτ : ContDiffMBOn 1 (c.1 ∘ i.1.symm) T := smoothMBOn_transition' i c 1
  have htr := localRep_transition hXv i c hix.1 hix.2
  have hτx : (c.1 ∘ i.1.symm) (i.1 x) = c.1 x := by simp [i.1.left_inv hxi]
  rw [hτx] at htr
  have hev : (fun z ↦ l (c.1 z)) ∘ i.1.symm =ᶠ[𝓝 (i.1 x)] l ∘ (c.1 ∘ i.1.symm) :=
    Filter.EventuallyEq.of_eq rfl
  change dMB ((fun z ↦ l (c.1 z)) ∘ i.1.symm) (i.1 x, localRep i X (i.1 x)) = _
  rw [dMB_congr_of_eventuallyEq hev,
    ContDiffMBOn.dMB_comp isOpen_univ (l.contDiffMBOn 1 univ) hτ (mapsTo_univ _ _) hix,
    (l.hasDirDerivAt _ _).dMB_eq, htr]

/-- **Vector fields are determined by their action on local functions**: if
`X(λ ∘ c) = Y(λ ∘ c)` at `x` for every continuous linear functional `λ` and one chart `c`
around `x`, then `X x = Y x`. (Global functions do not suffice in general, since smooth bump
functions need not exist.) -/
theorem eq_of_vfDeriv_clm_comp_chart {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (c : atlas E M) {x : M} (hx : x ∈ c.1.source)
    (h : ∀ l : E →L[ℝ] ℝ, vfDeriv X (fun z ↦ l (c.1 z)) x = vfDeriv Y (fun z ↦ l (c.1 z)) x) :
    X x = Y x := by
  have hrep : localRep c X (c.1 x) = localRep c Y (c.1 x) := by
    rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
    intro l
    rw [← vfDeriv_clm_comp_chart hXv c l hx, ← vfDeriv_clm_comp_chart hYv c l hx, h l]
  have hsX : X x ∈ (tangentChart c c.1).source := by
    rw [mem_tangentChart_source, hXv]; exact ⟨hx, hx⟩
  have hsY : Y x ∈ (tangentChart c c.1).source := by
    rw [mem_tangentChart_source, hYv]; exact ⟨hx, hx⟩
  refine (tangentChart c c.1).injOn hsX hsY (Prod.ext ?_ ?_)
  · simp only [tangentChart_apply]
    rw [hXv, hYv]
  · have e : c.1.symm (c.1 x) = x := c.1.left_inv hx
    unfold localRep at hrep
    rw [e] at hrep
    exact hrep

end Functions

end LCManifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Derivation

/-!
# Connections and covariant derivatives

References: S. Lang, *Fundamentals of Differential Geometry*, §§IV.3, VIII.1–2, IX.1;
G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 6.

A connection on a manifold `M` modeled on `E` is given in each chart `i` of the atlas by a
smooth family of continuous bilinear maps `Γᵢ(x) : E × E → E`, subject to the change of charts
law
`Γⱼ(τ x)(dτₓ u, dτₓ v) = dτₓ Γᵢ(x)(u, v) + d²τₓ(u, v)`,
where `τ = j ∘ i⁻¹` (`Connection`). The symbols are not tensorial: they transform affinely, with
the second derivative of the transition map. Conventions (chosen with G. Larotonda): the first
argument of `Γ` is the direction in which the base point moves, and

* the covariant derivative is `∇_X Y = dỸ · X̃ − Γ(X̃, Ỹ)` in a chart (`covDeriv`);
* the curvature follows Lang's sign, `R(X, Y) Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_[X,Y] Z`.

The covariant derivative does not depend on the chart (`localRep_covDeriv`): differentiating
`Ỹⱼ ∘ τ = dτ · Ỹᵢ` produces the term `d²τ(X̃ᵢ, Ỹᵢ)`, which cancels with the one in the change of
charts law of `Γ`.

A spray in the sense of Lang is the same as a symmetric connection, through
`f(x, v) = Γₓ(v, v)`; following the design chosen for this library, sprays are handled through
their local parts, and existence of geodesics or parallel transport (which need ODE theory, not
available in locally convex spaces) is not assumed anywhere.
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

/-- The local covariant derivative `∇_X Y = dY · X − Γ(X, Y)` on an open subset of `E`. -/
def localCovDeriv (Γ : E → E → E → E) (X Y : E → E) (y : E) : E :=
  dMB Y (y, X y) - Γ y (X y) (Y y)

/-- Differentiating `Zⱼ ∘ τ = dτ · Zᵢ`:
`dZⱼ(τ y)(dτ_y w) = d²τ_y(w, Zᵢ y) + dτ_y (dZᵢ(y) w)`. -/
theorem dMB_comp_transition {τ : E → F} {Zᵢ : E → E} {Zⱼ : F → F} {T U : Set E} {V : Set F}
    (hT : IsOpen T) (hU : IsOpen U) (hV : IsOpen V) (hUT : U ⊆ T) (hτ : ContDiffMBOn 2 τ T)
    (hUV : MapsTo τ U V) (hZᵢ : ContDiffMBOn 1 Zᵢ U) (hZⱼ : ContDiffMBOn 1 Zⱼ V)
    (hZ : ∀ y ∈ U, Zⱼ (τ y) = dMB τ (y, Zᵢ y)) {y : E} (hy : y ∈ U) (w : E) :
    dMB Zⱼ (τ y, dMB τ (y, w)) = dMB (dMB τ) ((y, Zᵢ y), (w, 0)) + dMB τ (y, dMB Zᵢ (y, w)) := by
  have hτ1 : ContDiffMBOn 1 τ U := (hτ.of_le (by norm_num)).mono hUT
  have hev : Zⱼ ∘ τ =ᶠ[𝓝 y] fun y' ↦ dMB τ (y', Zᵢ y') :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hy) fun y' hy' ↦ hZ y' hy'
  rw [← dMB_dMB_comp_apply hT hU hUT hτ hZᵢ hy w, ← dMB_congr_of_eventuallyEq hev,
    ContDiffMBOn.dMB_comp hV hZⱼ hτ1 hUV hy w]

/-- **The local covariant derivative transforms like a vector field** under a change of
coordinates `τ`, when the symbols obey the change of charts law. -/
theorem localCovDeriv_transition {τ : E → F} {Γᵢ : E → E → E → E} {Γⱼ : F → F → F → F}
    {Xᵢ Yᵢ : E → E} {Xⱼ Yⱼ : F → F} {T U : Set E} {V : Set F} (hT : IsOpen T) (hU : IsOpen U)
    (hV : IsOpen V) (hUT : U ⊆ T) (hτ : ContDiffMBOn 2 τ T) (hUV : MapsTo τ U V)
    (hYᵢ : ContDiffMBOn 1 Yᵢ U) (hYⱼ : ContDiffMBOn 1 Yⱼ V)
    (hΓ : ∀ y ∈ U, ∀ a b, Γⱼ (τ y) (dMB τ (y, a)) (dMB τ (y, b)) =
      dMB τ (y, Γᵢ y a b) + dMB (dMB τ) ((y, b), (a, 0)))
    (hX : ∀ y ∈ U, Xⱼ (τ y) = dMB τ (y, Xᵢ y)) (hY : ∀ y ∈ U, Yⱼ (τ y) = dMB τ (y, Yᵢ y))
    {y : E} (hy : y ∈ U) :
    localCovDeriv Γⱼ Xⱼ Yⱼ (τ y) = dMB τ (y, localCovDeriv Γᵢ Xᵢ Yᵢ y) := by
  obtain ⟨L, hL⟩ := (hτ.of_le (by norm_num) : ContDiffMBOn 1 τ T).exists_clm hT (hUT hy)
  rw [localCovDeriv, localCovDeriv, hX y hy, hY y hy,
    dMB_comp_transition hT hU hV hUT hτ hUV hYᵢ hYⱼ hY hy, hΓ y hy, ← hL, ← hL, ← hL, map_sub]
  abel

end Calculus

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

variable (E M) in
/-- A connection on `M`: in each chart `i` of the atlas, a smooth family of bilinear maps
`Γᵢ(x) : E × E → E` (`x ∈ i(U)`), subject to the change of charts law
`Γⱼ(τ x)(dτₓ a, dτₓ b) = dτₓ Γᵢ(x)(a, b) + d²τₓ(a, b)`, `τ = j ∘ i⁻¹`. -/
structure Connection where
  /-- The Christoffel symbols in the chart `i`: `Γ i x a b`. -/
  Γ : atlas E M → E → E → E → E
  smooth : ∀ i, SmoothMBOn (fun p : E × (E × E) ↦ Γ i p.1 p.2.1 p.2.2) (i.1.target ×ˢ univ)
  add_left : ∀ i x a a' b, Γ i x (a + a') b = Γ i x a b + Γ i x a' b
  smul_left : ∀ i x (c : ℝ) a b, Γ i x (c • a) b = c • Γ i x a b
  add_right : ∀ i x a b b', Γ i x a (b + b') = Γ i x a b + Γ i x a b'
  smul_right : ∀ i x (c : ℝ) a b, Γ i x a (c • b) = c • Γ i x a b
  transition : ∀ i j : atlas E M, ∀ y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source, ∀ a b,
    Γ j ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, a)) (dMB (j.1 ∘ i.1.symm) (y, b)) =
      dMB (j.1 ∘ i.1.symm) (y, Γ i y a b) + dMB (dMB (j.1 ∘ i.1.symm)) ((y, b), (a, 0))

namespace Connection

variable (C : Connection E M)

/-- The covariant derivative `∇_X Y`, computed in the preferred chart at each point. -/
def covDeriv (X Y : M → TangentBundle E M) (x : M) : TangentBundle E M :=
  ⟨x, (localCovDeriv (C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩)
    (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X)
    (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y) (chartAt E x x) : E)⟩

theorem isVectorField_covDeriv (X Y : M → TangentBundle E M) :
    IsVectorField (C.covDeriv X Y) :=
  fun _ ↦ rfl

/-- **The covariant derivative does not depend on the chart**: in every chart `j` of the atlas,
the local representative of `∇_X Y` is `dỸⱼ · X̃ⱼ − Γⱼ(X̃ⱼ, Ỹⱼ)`. -/
theorem localRep_covDeriv {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hY : ContMDiffMB E (E × E) 1 Y) (j : atlas E M) {y : E}
    (hy : y ∈ j.1.target) :
    localRep j (C.covDeriv X Y) y = localCovDeriv (C.Γ j) (localRep j X) (localRep j Y) y := by
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
  have htrans := localCovDeriv_transition hT hT j.1.open_target subset_rfl hτ hmaps
    ((contDiffMBOn_localRep hYv hY i).mono inter_subset_left) (contDiffMBOn_localRep hYv hY j)
    (fun z hz a b ↦ C.transition i j z hz a b)
    (fun z hz ↦ localRep_transition hXv i j hz.1 hz.2)
    (fun z hz ↦ localRep_transition hYv i j hz.1 hz.2) hix
  rw [hτx] at htrans
  rw [htrans]
  rfl

/-- `∇_X Y` at `x` only depends on the local representatives at `x`: in the preferred chart. -/
theorem covDeriv_snd (X Y : M → TangentBundle E M) (x : M) :
    (show E from (C.covDeriv X Y x).2) =
      localCovDeriv (C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩)
        (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X)
        (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y) (chartAt E x x) :=
  rfl

/-- **Torsion**: `∇_X Y − ∇_Y X − [X, Y]` is, in the preferred chart,
`Γ(Ỹ, X̃) − Γ(X̃, Ỹ)`; it only depends on the values of `X` and `Y` at the point. -/
theorem covDeriv_sub_covDeriv_sub_lieBracket (X Y : M → TangentBundle E M) (x : M) :
    (show E from (C.covDeriv X Y x).2) - (show E from (C.covDeriv Y X x).2) -
        (show E from (lieBracket X Y x).2) =
      C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩ (chartAt E x x)
          (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y (chartAt E x x))
          (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X (chartAt E x x)) -
        C.Γ ⟨chartAt E x, chart_mem_atlas E x⟩ (chartAt E x x)
          (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ X (chartAt E x x))
          (localRep ⟨chartAt E x, chart_mem_atlas E x⟩ Y (chartAt E x x)) := by
  rw [covDeriv_snd, covDeriv_snd]
  change _ - _ - localBracket _ _ _ = _
  simp only [localCovDeriv, localBracket]
  abel

/-- A connection is symmetric (torsion free) if its symbols are symmetric in every chart. -/
def IsSymmetric : Prop := ∀ i x a b, C.Γ i x a b = C.Γ i x b a

/-- For a symmetric connection, `∇_X Y − ∇_Y X = [X, Y]`. -/
theorem covDeriv_sub_covDeriv (hC : C.IsSymmetric) (X Y : M → TangentBundle E M) (x : M) :
    (show E from (C.covDeriv X Y x).2) - (show E from (C.covDeriv Y X x).2) =
      (show E from (lieBracket X Y x).2) := by
  have h := C.covDeriv_sub_covDeriv_sub_lieBracket X Y x
  rw [hC _ _ (localRep _ Y _), sub_self, sub_eq_zero] at h
  exact h

/-- `∇_{φX} Y = φ ∇_X Y`. -/
theorem covDeriv_smulField_left {X Y : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hY : ContMDiffMB E (E × E) 1 Y) (φ : M → ℝ) (x : M) :
    (show E from (C.covDeriv (smulField φ X) Y x).2) =
      φ x • (show E from (C.covDeriv X Y x).2) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hxx : i.1.symm (i.1 x) = x := i.1.left_inv (mem_chart_source E x)
  rw [covDeriv_snd, covDeriv_snd]
  change localCovDeriv (C.Γ i) (localRep i (smulField φ X)) (localRep i Y) (i.1 x) =
    φ x • localCovDeriv (C.Γ i) (localRep i X) (localRep i Y) (i.1 x)
  simp only [localCovDeriv]
  rw [localRep_smulField hXv φ i hx, Function.comp_apply, hxx,
    (contDiffMBOn_localRep hYv hY i).dMB_smul hx, C.smul_left, smul_sub]

/-- **Leibniz rule** `∇_X (φ Y) = X(φ) Y + φ ∇_X Y`. -/
theorem covDeriv_smulField_right {X Y : M → TangentBundle E M} (hYv : IsVectorField Y) (hY : ContMDiffMB E (E × E) 1 Y) {φ : M → ℝ}
    (hφ : IsCkFunction E 1 φ) (x : M) :
    (show E from (C.covDeriv X (smulField φ Y) x).2) =
      vfDeriv X φ x • (show E from (Y x).2) + φ x • (show E from (C.covDeriv X Y x).2) := by
  set i : atlas E M := ⟨chartAt E x, chart_mem_atlas E x⟩
  have hx : i.1 x ∈ i.1.target := i.1.map_source (mem_chart_source E x)
  have hxx : i.1.symm (i.1 x) = x := i.1.left_inv (mem_chart_source E x)
  have hev : localRep i (smulField φ Y) =ᶠ[𝓝 (i.1 x)]
      fun y ↦ (φ ∘ i.1.symm) y • localRep i Y y :=
    Filter.eventuallyEq_of_mem (i.1.open_target.mem_nhds hx)
      fun _ hy ↦ localRep_smulField hYv φ i hy
  have hYi := contDiffMBOn_localRep hYv hY i
  have hd := HasDirDerivAt.smul_fun ((hφ i).hasDirDerivAt (k := 0) hx (localRep i X (i.1 x)))
    ((hφ i).continuousOn.continuousAt (i.1.open_target.mem_nhds hx))
    (hYi.hasDirDerivAt (k := 0) hx (localRep i X (i.1 x)))
  rw [covDeriv_snd, covDeriv_snd]
  change localCovDeriv (C.Γ i) (localRep i X) (localRep i (smulField φ Y)) (i.1 x) =
    vfDeriv X φ x • (show E from (Y x).2) +
      φ x • localCovDeriv (C.Γ i) (localRep i X) (localRep i Y) (i.1 x)
  rw [← localRep_chartAt hYv x]
  simp only [localCovDeriv]
  rw [dMB_congr_of_eventuallyEq hev, hev.eq_of_nhds, hd.dMB_eq]
  simp only [Function.comp_apply, hxx]
  rw [C.smul_right, smul_sub,
    show vfDeriv X φ x = dMB (φ ∘ i.1.symm) (i.1 x, localRep i X (i.1 x)) from rfl]
  abel

end Connection

end Manifold

end LCManifolds

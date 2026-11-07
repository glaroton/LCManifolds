/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Connection
import LocallyConvexManifolds.DifferentialForm

/-!
# Connection forms and Cartan's structure equations

A connection on a vector bundle with fiber `F` over a manifold modeled on `E` is given, in a
local trivialization over an open set `U ⊆ E`, by symbols `Γ(y)(v, ξ) ∈ F`, bilinear in
`v ∈ E` and `ξ ∈ F`; for the tangent bundle (`F = E`) these are the Christoffel symbols of
`LocallyConvexManifolds.Connection`. Classically, the **connection form** is the
`End(F)`-valued `1`-form `A(y)(v) = Γ(y)(v, ·)`, the covariant derivative is `∇ = d − A`, and the
curvature is the `End(F)`-valued `2`-form `Ω = −dA + A ∧ A` (Cartan's structure equation, with
Lang's sign for the curvature). The local theory below is written for an arbitrary fiber `F`.

**An infinite-dimensional subtlety.** If `F` is not normable, no vector topology on the space
`L(F)` of continuous linear endomorphisms makes the evaluation `L(F) × F → F` continuous
(Maissen, Math. Ann. 151 (1963), Satz 1), so `A` cannot be an honest differential form with
values in a locally convex space of operators. We therefore encode an `End(F)`-valued form as a family of `F`-valued forms depending
linearly on an extra argument: for `ξ ∈ F`, `connForm Γ ξ` is the `F`-valued local `1`-form
`(y, v) ↦ Γ(y)(v, ξ)`, and `curvLoc Γ ξ` is the `F`-valued local `2`-form
`(y, u, v) ↦ R(y)(u, v) ξ`. All the identities below are identities between `F`-valued local forms,
and never use a topology on `L(F)`. (On a Banach space `F` these families are `L(F)`-valued forms
in the usual sense.) For the same reason, the transition functions of a vector bundle cannot be
required to be smooth maps into `GL(F)`; only `(y, ξ) ↦ g(y) ξ` can be required to be smooth.

## Main results

* `IsLocalSymbol`: the hypotheses on a family of symbols on an open set (smooth, bilinear);
* `IsLocalSymbol.isLocalForm_connForm`: `A^ξ` is a local `1`-form;
* `curvLoc_eq` (**Cartan's structure equation**): `Ω^ξ = −dA^ξ + (A ∧ A)^ξ`, where
  `(A ∧ A)(u, v) ξ = A(u) A(v) ξ − A(v) A(u) ξ`;
* `IsLocalSymbol.dLoc_curvLoc` (**the second Bianchi identity**): `dΩ = [A ∧ Ω]`, i.e. the
  covariant exterior derivative `DΩ = dΩ − [A ∧ Ω]` of the curvature vanishes;
* `Connection.connForm_transition`: the gauge transformation law of the connection forms under a
  change of charts, `A_j(τ y)(dτ v)(dτ w) = dτ(A_i(y)(v) w) + d²τ(v, w)`; the inhomogeneous term
  is why `A` is not a tensor;
* `Connection.torsionLoc_transition`: the torsion `T(u, v) = Γ(u, v) − Γ(v, u)` is a tensor,
  because the second derivatives of the transition maps are symmetric;
* `Connection.curvature_eq_structure`: the curvature of a connection, evaluated on vector fields,
  is given in the preferred chart by Cartan's structure equation.

No completeness of `E` is assumed.
-/

open Set Function Filter
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

section Local

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- The hypotheses on the symbols of a connection in a local trivialization over an open set
`U ⊆ E`: the map `(y, a, ξ) ↦ Γ(y)(a, ξ)` is smooth on `U × E × F`, and `Γ(y)` is bilinear. -/
structure IsLocalSymbol (Γ : E → E → F → F) (U : Set E) : Prop where
  smooth : SmoothMBOn (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ)
  add_left : ∀ x a a' ξ, Γ x (a + a') ξ = Γ x a ξ + Γ x a' ξ
  smul_left : ∀ x (c : ℝ) a ξ, Γ x (c • a) ξ = c • Γ x a ξ
  add_right : ∀ x a ξ ξ', Γ x a (ξ + ξ') = Γ x a ξ + Γ x a ξ'
  smul_right : ∀ x (c : ℝ) a ξ, Γ x a (c • ξ) = c • Γ x a ξ

/-- The derivative of the symbols in the base point: `∂_c Γ(y)(a, ξ)`. -/
def symbD (Γ : E → E → F → F) (y c a : E) (ξ : F) : F :=
  dMB (fun z ↦ Γ z a ξ) (y, c)

/-- The curvature, with Lang's sign:
`R(y)(u, v) ξ = ∂_v Γ(u, ξ) − ∂_u Γ(v, ξ) + Γ(u, Γ(v, ξ)) − Γ(v, Γ(u, ξ))`. -/
def bundleCurv (Γ : E → E → F → F) (y u v : E) (ξ : F) : F :=
  symbD Γ y v u ξ - symbD Γ y u v ξ + Γ y u (Γ y v ξ) - Γ y v (Γ y u ξ)

/-- The connection form `A^ξ`: the `F`-valued local `1`-form `(y, v) ↦ Γ(y)(v, ξ)`, i.e.
`A(y)(v)` applied to `ξ`. -/
def connForm (Γ : E → E → F → F) (ξ : F) (p : E × (Fin 1 → E)) : F :=
  Γ p.1 (p.2 0) ξ

/-- `(A ∧ A)^ξ`: `(y, u, v) ↦ A(u) A(v) ξ − A(v) A(u) ξ`. -/
def connWedge (Γ : E → E → F → F) (ξ : F) (p : E × (Fin 2 → E)) : F :=
  Γ p.1 (p.2 0) (Γ p.1 (p.2 1) ξ) - Γ p.1 (p.2 1) (Γ p.1 (p.2 0) ξ)

/-- The curvature form `Ω^ξ`: the `F`-valued local `2`-form `(y, u, v) ↦ R(y)(u, v) ξ`. -/
def curvLoc (Γ : E → E → F → F) (ξ : F) (p : E × (Fin 2 → E)) : F :=
  bundleCurv Γ p.1 (p.2 0) (p.2 1) ξ

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `dA^ξ(y)(u, v) = ∂_u Γ(y)(v, ξ) − ∂_v Γ(y)(u, ξ)`. -/
theorem dLoc_connForm (Γ : E → E → F → F) (ξ : F) (y : E) (v : Fin 2 → E) :
    dLoc (connForm Γ ξ) (y, v) = symbD Γ y (v 0) (v 1) ξ - symbD Γ y (v 1) (v 0) ξ := by
  rw [IsLocalForm.dLoc_apply, Fin.sum_univ_two]
  simp only [connForm, symbD, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    ← sub_eq_add_neg]
  rfl

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- **Cartan's structure equation**: `Ω = −dA + A ∧ A`. -/
theorem curvLoc_eq (Γ : E → E → F → F) (ξ : F) (p : E × (Fin 2 → E)) :
    curvLoc Γ ξ p = -dLoc (connForm Γ ξ) p + connWedge Γ ξ p := by
  obtain ⟨y, v⟩ := p
  rw [dLoc_connForm, curvLoc, connWedge, bundleCurv]
  abel

namespace IsLocalSymbol

variable {Γ : E → E → F → F} {U : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem sub_right (hΓ : IsLocalSymbol Γ U) (x a : E) (ξ ξ' : F) :
    Γ x a (ξ - ξ') = Γ x a ξ - Γ x a ξ' := by
  rw [sub_eq_add_neg, hΓ.add_right, ← neg_one_smul ℝ ξ', hΓ.smul_right, neg_one_smul,
    ← sub_eq_add_neg]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem zero_left (hΓ : IsLocalSymbol Γ U) (x : E) (ξ : F) : Γ x 0 ξ = 0 := by
  have := hΓ.smul_left x 0 0 ξ
  rwa [zero_smul, zero_smul] at this

/-- Composition of the symbols with smooth maps. -/
theorem contDiffMBOn_comp (hΓ : IsLocalSymbol Γ U) {V : Type u} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]
    [T2Space V] {W : Set V} (hW : IsOpen W) {f₀ f₁ : V → E} {f₂ : V → F} {k : ℕ}
    (h₀ : ContDiffMBOn k f₀ W) (h₁ : ContDiffMBOn k f₁ W) (h₂ : ContDiffMBOn k f₂ W)
    (hU : IsOpen U) (hmaps : MapsTo f₀ W U) :
    ContDiffMBOn k (fun q ↦ Γ (f₀ q) (f₁ q) (f₂ q)) W :=
  ContDiffMBOn.comp (g := fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2)
    (f := fun q ↦ (f₀ q, (f₁ q, f₂ q))) hW (hU.prod isOpen_univ) (hΓ.smooth k)
    (h₀.prodMk hW (h₁.prodMk hW h₂)) fun _ hq ↦ ⟨hmaps hq, mem_univ _⟩

/-- The connection form `A^ξ` is a local `1`-form. -/
theorem isLocalForm_connForm (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) (ξ : F) :
    IsLocalForm 1 (connForm Γ ξ) U := by
  refine ⟨fun k ↦ ?_, fun y _ ↦ ?_⟩
  · have hW : IsOpen (U ×ˢ (univ : Set (Fin 1 → E))) := hU.prod isOpen_univ
    exact hΓ.contDiffMBOn_comp hW
      ((ContinuousLinearMap.fst ℝ E (Fin 1 → E)).contDiffMBOn k _)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ E) 0).comp
        (ContinuousLinearMap.snd ℝ E (Fin 1 → E))).contDiffMBOn k _)
      (contDiffMBOn_const k ξ _) hU fun _ hq ↦ hq.1
  · exact ⟨AlternatingMap.ofSubsingleton ℝ E F 0
      { toFun := fun a ↦ Γ y a ξ
        map_add' := fun a a' ↦ hΓ.add_left y a a' ξ
        map_smul' := fun c a ↦ hΓ.smul_left y c a ξ }, fun _ ↦ rfl⟩

/-- `z ↦ Γ(z)(a, ξ)` is smooth. -/
theorem contDiffMBOn_slice (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) (a : E) (ξ : F) (k : ℕ) :
    ContDiffMBOn k (fun z ↦ Γ z a ξ) U :=
  hΓ.contDiffMBOn_comp hU ((ContinuousLinearMap.id ℝ E).contDiffMBOn k U)
    (contDiffMBOn_const k a U) (contDiffMBOn_const k ξ U) hU fun _ h ↦ h

/-- **Product rule**: the derivative of `z ↦ Γ(z)(a, Γ(z)(b, ξ))` in the direction `c` is
`∂_c Γ(a, Γ(b, ξ)) + Γ(a, ∂_c Γ(b, ξ))`. -/
theorem hasDirDerivAt_comp (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) {y : E} (hy : y ∈ U)
    (a b c : E) (ξ : F) :
    HasDirDerivAt (fun z ↦ Γ z a (Γ z b ξ)) y c
      (symbD Γ y c a (Γ y b ξ) + Γ y a (symbD Γ y c b ξ)) := by
  have hUU : IsOpen (U ×ˢ (univ : Set (E × F))) := hU.prod isOpen_univ
  have hΓ1 : ContDiffMBOn 1 (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ) := hΓ.smooth 1
  have hB := hΓ.contDiffMBOn_slice hU b ξ 1
  have hf : ContDiffMBOn 1 (fun z ↦ (z, (a, Γ z b ξ))) U :=
    ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U).prodMk hU
      ((contDiffMBOn_const 1 a U).prodMk hU hB)
  have hcomp := ContDiffMBOn.dMB_comp (g := fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2)
    (f := fun z ↦ (z, (a, Γ z b ξ))) hUU hΓ1 hf (fun z hz ↦ ⟨hz, mem_univ _⟩) hy c
  have h0 : HasDirDerivAt (fun _ : E ↦ a) y c 0 :=
    tendsto_nhds_of_eventually_eq (Eventually.of_forall fun t ↦ by simp)
  have hdf : dMB (fun z ↦ (z, (a, Γ z b ξ))) (y, c) = (c, (0, symbD Γ y c b ξ)) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt y c).prodMk
      (h0.prodMk (hB.hasDirDerivAt (k := 0) hy c))).dMB_eq
  have hp : (y, (a, Γ y b ξ)) ∈ U ×ˢ (univ : Set (E × F)) := ⟨hy, mem_univ _⟩
  have hsplit : (c, ((0 : E), symbD Γ y c b ξ)) =
      (c, ((0 : E), (0 : F))) + ((0 : E), ((0 : E), symbD Γ y c b ξ)) := by simp
  have hbase : dMB (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) ((y, (a, Γ y b ξ)), (c, (0, 0))) =
      symbD Γ y c a (Γ y b ξ) := by
    simp only [symbD, dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  have hfib : HasDirDerivAt (fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) (y, (a, Γ y b ξ))
      (0, (0, symbD Γ y c b ξ)) (Γ y a (symbD Γ y c b ξ)) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hΓ.add_right, hΓ.smul_right,
      add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have h := (hΓ.contDiffMBOn_comp hU ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 U)
    (contDiffMBOn_const 1 a U) hB hU fun _ h ↦ h).hasDirDerivAt (k := 0) hy c
  have hval : dMB (fun z ↦ Γ z a (Γ z b ξ)) (y, c) =
      symbD Γ y c a (Γ y b ξ) + Γ y a (symbD Γ y c b ξ) := by
    change dMB ((fun p : E × (E × F) ↦ Γ p.1 p.2.1 p.2.2) ∘ fun z ↦ (z, (a, Γ z b ξ))) (y, c) = _
    rw [hcomp, hdf, hsplit, hΓ1.dMB_add hUU hp, hbase, hfib.dMB_eq]
  rw [← hval]
  exact h

/-- **The second Bianchi identity**: `dΩ = [A ∧ Ω]`, i.e. the covariant exterior derivative
`DΩ = dΩ − [A ∧ Ω]` of the curvature vanishes. Explicitly, with `[A(a), Ω(b, c)] ξ =
A(a) Ω(b, c) ξ − Ω(b, c) A(a) ξ`:
`dΩ(u, v, t) ξ = [A(u), Ω(v, t)] ξ − [A(v), Ω(u, t)] ξ + [A(t), Ω(u, v)] ξ`.
The proof combines `Ω = −dA + A ∧ A`, `d ∘ d = 0` and the Jacobi identity for commutators. -/
theorem dLoc_curvLoc (hΓ : IsLocalSymbol Γ U) (hU : IsOpen U) {y : E} (hy : y ∈ U)
    (ξ : F) (u v t : E) :
    dLoc (curvLoc Γ ξ) (y, ![u, v, t]) =
      (Γ y u (bundleCurv Γ y v t ξ) - bundleCurv Γ y v t (Γ y u ξ)) -
        (Γ y v (bundleCurv Γ y u t ξ) - bundleCurv Γ y u t (Γ y v ξ)) +
          (Γ y t (bundleCurv Γ y u v ξ) - bundleCurv Γ y u v (Γ y t ξ)) := by
  have hA := hΓ.isLocalForm_connForm hU ξ
  have hdA := hA.dLoc hU
  set D : E → E → E → F := fun c a b ↦
    symbD Γ y c a (Γ y b ξ) + Γ y a (symbD Γ y c b ξ) -
      (symbD Γ y c b (Γ y a ξ) + Γ y b (symbD Γ y c a ξ)) with hD
  have hterm : ∀ (w : Fin 2 → E) (c : E),
      dMB (fun z ↦ curvLoc Γ ξ (z, w)) (y, c) =
        D c (w 0) (w 1) - dMB (fun z ↦ dLoc (connForm Γ ξ) (z, w)) (y, c) := by
    intro w c
    have hfun : (fun z ↦ curvLoc Γ ξ (z, w)) =
        fun z ↦ connWedge Γ ξ (z, w) - dLoc (connForm Γ ξ) (z, w) :=
      funext fun z ↦ by rw [curvLoc_eq]; abel
    have h1 := (hdA.smooth_slice hU w 1).hasDirDerivAt (k := 0) hy c
    have h2 := (hΓ.hasDirDerivAt_comp hU hy (w 0) (w 1) c ξ).sub
      (hΓ.hasDirDerivAt_comp hU hy (w 1) (w 0) c ξ)
    rw [hfun]
    exact (h2.sub h1).dMB_eq
  have hsum : dLoc (curvLoc Γ ξ) (y, ![u, v, t]) =
      (∑ i : Fin 3, (-1 : ℝ) ^ (i : ℕ) • D (![u, v, t] i) (i.removeNth ![u, v, t] 0)
          (i.removeNth ![u, v, t] 1)) - dLoc (dLoc (connForm Γ ξ)) (y, ![u, v, t]) := by
    rw [IsLocalForm.dLoc_apply, IsLocalForm.dLoc_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hterm, smul_sub]
  rw [hsum, hA.dLoc_dLoc hU hy, sub_zero, Fin.sum_univ_three]
  have r0 : (0 : Fin 3).removeNth ![u, v, t] = ![v, t] := by
    funext k; fin_cases k <;> rfl
  have r1 : (1 : Fin 3).removeNth ![u, v, t] = ![u, t] := by
    funext k; fin_cases k <;> rfl
  have r2 : (2 : Fin 3).removeNth ![u, v, t] = ![u, v] := by
    funext k; fin_cases k <;> rfl
  simp only [r0, r1, r2, hD, bundleCurv, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, neg_one_sq, hΓ.add_right, hΓ.sub_right]
  abel

end IsLocalSymbol

end Local

/-! ### The tangent bundle -/

section Tangent

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- For the tangent bundle, the curvature form is the local curvature of
`LocallyConvexManifolds.Connection`. -/
theorem bundleCurv_eq_localCurv (Γ : E → E → E → E) (y u v w : E) :
    bundleCurv Γ y u v w = localCurv Γ y u v w := by
  have h : ∀ c a b, symbD Γ y c a b = dSymb Γ y c a b := fun c a b ↦ by
    simp only [symbD, dSymb, dMB, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  simp only [bundleCurv, localCurv, h]

/-- The torsion `T(y)(u, v) = Γ(y)(u, v) − Γ(y)(v, u)`: `T = A ∧ θ`, where `θ` is the identity
(solder) form. -/
def torsionLoc (Γ : E → E → E → E) (y u v : E) : E := Γ y u v - Γ y v u

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace Connection

variable (C : Connection E M)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The Christoffel symbols of a connection in a chart satisfy the hypotheses of the local
theory. -/
theorem isLocalSymbol (i : atlas E M) : IsLocalSymbol (C.Γ i) i.1.target :=
  ⟨C.smooth i, C.add_left i, C.smul_left i, C.add_right i, C.smul_right i⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- **Gauge transformation of the connection form.** With `τ = j ∘ i⁻¹` and `g(y) = dτ(y)`,
`A_j(τ y)(g v)(g w) = g(A_i(y)(v) w) + (∂_v g)(y) w`. The inhomogeneous term
`(∂_v g) w = d²τ(v, w)` is why the connection form is not a tensor. -/
theorem connForm_transition (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (v w : E) :
    connForm (C.Γ j) (dMB (j.1 ∘ i.1.symm) (y, w)) ((j.1 ∘ i.1.symm) y,
        ![dMB (j.1 ∘ i.1.symm) (y, v)]) =
      dMB (j.1 ∘ i.1.symm) (y, connForm (C.Γ i) w (y, ![v])) +
        dMB (dMB (j.1 ∘ i.1.symm)) ((y, w), (v, 0)) :=
  C.transition i j y hy v w

/-- **The torsion is a tensor**: `T_j(τ y)(dτ a, dτ b) = dτ(T_i(y)(a, b))`, because the second
derivatives of the transition map are symmetric. -/
theorem torsionLoc_transition (i j : atlas E M) {y : E}
    (hy : y ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source) (a b : E) :
    torsionLoc (C.Γ j) ((j.1 ∘ i.1.symm) y) (dMB (j.1 ∘ i.1.symm) (y, a))
        (dMB (j.1 ∘ i.1.symm) (y, b)) =
      dMB (j.1 ∘ i.1.symm) (y, torsionLoc (C.Γ i) y a b) := by
  have hT := isOpen_transition_domain i j
  have hτ : ContDiffMBOn 2 (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
    smoothMBOn_transition' i j 2
  have hτ1 : ContDiffMBOn 1 (j.1 ∘ i.1.symm) (i.1.target ∩ i.1.symm ⁻¹' j.1.source) :=
    hτ.of_le (by norm_num)
  rw [torsionLoc, torsionLoc, C.transition i j y hy a b, C.transition i j y hy b a,
    hτ.dMB_dMB_symm hT hy b a]
  have hsub := hτ1.dMB_add hT hy (C.Γ i y a b - C.Γ i y b a) (C.Γ i y b a)
  rw [sub_add_cancel] at hsub
  rw [hsub]
  abel

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- The torsion vanishes iff the connection is symmetric. -/
theorem isSymmetric_iff_torsionLoc :
    C.IsSymmetric ↔ ∀ i y a b, torsionLoc (C.Γ i) y a b = 0 := by
  simp only [IsSymmetric, torsionLoc, sub_eq_zero]

/-- **Cartan's structure equation for the curvature of a connection**: for `C^2` vector fields,
`R(X, Y) Z` is computed in the preferred chart by `Ω = −dA + A ∧ A`, evaluated at the local
representatives of `X`, `Y` (form arguments) and `Z` (endomorphism argument). -/
theorem curvature_eq_structure {X Y Z : M → TangentBundle E M} (hXv : IsVectorField X)
    (hYv : IsVectorField Y) (hZv : IsVectorField Z) (hX : ContMDiffMB E (E × E) 2 X)
    (hY : ContMDiffMB E (E × E) 2 Y) (hZ : ContMDiffMB E (E × E) 2 Z) (x : M) :
    C.curvature X Y Z x =
      -dLoc (connForm (C.Γ (prefChart x)) (localRep (prefChart x) Z (chartAt E x x)))
          (chartAt E x x, ![localRep (prefChart x) X (chartAt E x x),
            localRep (prefChart x) Y (chartAt E x x)]) +
        connWedge (C.Γ (prefChart x)) (localRep (prefChart x) Z (chartAt E x x))
          (chartAt E x x, ![localRep (prefChart x) X (chartAt E x x),
            localRep (prefChart x) Y (chartAt E x x)]) := by
  rw [← curvLoc_eq, curvLoc, C.curvature_eq hXv hYv hZv hX hY hZ, bundleCurv_eq_localCurv]
  rfl

omit [MBManifold E M] in
/-- **The second Bianchi identity** for a connection, in every chart. -/
theorem dLoc_curvLoc (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (w u v t : E) :
    dLoc (curvLoc (C.Γ i) w) (y, ![u, v, t]) =
      (C.Γ i y u (bundleCurv (C.Γ i) y v t w) - bundleCurv (C.Γ i) y v t (C.Γ i y u w)) -
        (C.Γ i y v (bundleCurv (C.Γ i) y u t w) - bundleCurv (C.Γ i) y u t (C.Γ i y v w)) +
          (C.Γ i y t (bundleCurv (C.Γ i) y u v w) - bundleCurv (C.Γ i) y u v (C.Γ i y t w)) :=
  (C.isLocalSymbol i).dLoc_curvLoc i.1.open_target hy w u v t

end Connection

end Tangent

end LocallyConvex.Manifolds

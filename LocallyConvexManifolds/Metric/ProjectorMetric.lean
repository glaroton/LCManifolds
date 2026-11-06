/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Projector
import LocallyConvexManifolds.Metric.LeviCivita

/-!
# Orthogonal projectors and the Levi-Civita connection of a submanifold, any signature

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, §6.6
(Teorema 6.6.1, "derivar y proyectar") and §10.1.1 (the Levi-Civita derivative of a
submanifold); J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974), Theorem V.3.4 and
Example V.3.3 (ortho-complemented subspaces of Krein spaces).

Let `β` be a continuous symmetric bilinear form on the ambient space `F`, of **any signature**
(an inner product, or the indefinite form of a Krein or Pontryagin space), and let `X ⊆ F` be an
embedded submanifold with a field of projectors `P` onto its tangent spaces
(`LocallyConvex.Manifolds.ProjectorField`). The **induced form** in a slice chart `φ`, with
`ψ = φ⁻¹|_S`, is

`G(y)(a, b) = β(dψ_y a, dψ_y b)`  (`inducedForm`).

`P` is **`β`-orthogonal** if `β(P_p w, t) = β(w, t)` for every `w ∈ F` and every tangent vector
`t ∈ T_p X`; that is, `ker P_p` is `β`-orthogonal to `T_p X`.

## Main results

* `isMetric_symb` (**Gauss**): if `P` is `β`-orthogonal, the connection of `P` is metric for the
  induced form, in every slice chart:
  `∂G(y)(u)(a, b) = − G(y)(Γ(u, a), b) − G(y)(a, Γ(u, b))`.
  The computation is that of the Riemannian case: `∂G` produces `β(d²ψ(u, a), dψ b)`, and
  `dψ Γ(u, a) = −P(d²ψ(u, a))` differs from `−d²ψ(u, a)` by a vector `β`-orthogonal to `T_p X`.
* `nondegenerate_of_orthogonal`: **orthogonal projectors only exist onto nondegenerate
  subspaces.** If `β` is weakly nondegenerate and `Q` is a `β`-orthogonal projector, no nonzero
  vector of the range of `Q` is `β`-orthogonal to the whole range.
* `symb_eq_of_isMetric`: hence, if `β` is weakly nondegenerate and `P` is `β`-orthogonal, the
  symbols of `P` are **the Levi-Civita symbols** of the induced metric: any symmetric symbols
  compatible with `G` coincide with them (Koszul, `LocallyConvex.Manifolds.eq_of_koszul`).

## The induced metric on `X`

The induced forms of the slice charts glue: by the chain rule `dψ'_{τ y}(dτ_y v) = dψ_y v` for
the change of slice charts `τ` (`dMB_param_transition`), the local representative of the field
`x ↦ β(dψ ·, dψ ·)` (computed in the preferred chart at `x`) in any chart is the induced form of
that chart (`bilinLocalRep_inducedFun`). This gives:

* `inducedMetric`: the induced metric, a smooth field of symmetric bilinear forms on `X`;
  `inducedRiemannian`: a weak Riemannian metric when `β` is positive definite;
* `connection_isMetric`: the connection of a `β`-orthogonal `P` is metric for it
  (`Connection.IsMetric`, in every chart of the atlas of `X`);
* `inducedMetric_isWeaklyNondegenerate` and `covDeriv_eq_connection`: if `β` is weakly
  nondegenerate, **every symmetric metric connection of the induced metric has the covariant
  derivative of `P`**: the Levi-Civita connection of `X` is "derive and project".

## The indefinite case

For an inner product every closed subspace of a Hilbert space has an orthogonal projector, and
the theory above is that of *Estructuras*, §10.1.1. For an indefinite `β` this is no longer so,
and `nondegenerate_of_orthogonal` shows the first obstruction: a **degenerate** tangent space
`T_p X` (one containing a nonzero vector orthogonal to all of `T_p X`, as for the lightlike
hypersurfaces of a Lorentzian space) admits no `β`-orthogonal projector, and the
"derive and project" description of the Levi-Civita connection is lost. In a Krein space a
closed subspace has a `β`-orthogonal projector exactly when it is itself a Krein space with the
induced form (Bognár, Theorem V.3.4); being closed, nondegenerate and decomposable does not
suffice (Bognár, Example V.3.3). That characterization uses completeness and is not formalized.
-/

open Set Filter
open scoped Topology Manifold
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u

/-! ### Orthogonal projectors only exist onto nondegenerate subspaces -/

/-- If `β` is weakly nondegenerate and `Q` is `β`-orthogonal (`β(Q w, t) = β(w, t)` for `t` in
the range of `Q`), then the range of `Q` is nondegenerate for `β`. In particular a degenerate
subspace has no `β`-orthogonal projector. -/
theorem nondegenerate_of_orthogonal {F : Type*} [AddCommGroup F] [Module ℝ F]
    {β : LinearMap.BilinForm ℝ F} (hnd : ∀ t, (∀ w, β w t = 0) → t = 0) {Q : F → F}
    (horth : ∀ w t, t ∈ range Q → β (Q w) t = β w t) {t : F} (ht : t ∈ range Q)
    (hperp : ∀ s ∈ range Q, β s t = 0) : t = 0 :=
  hnd t fun w ↦ by rw [← horth w t ht]; exact hperp _ ⟨w, rfl⟩

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {X : Set F} {S : Submodule ℝ F} {h : IsEmbeddedSubmanifold X S}

namespace ProjectorField

variable (P : ProjectorField h) (β : LinearMap.BilinForm ℝ F)

/-- `P` is **`β`-orthogonal**: `β(P_p w, t) = β(w, t)` for every tangent vector `t ∈ T_p X`. -/
def IsOrthogonal : Prop := ∀ p w t, t ∈ h.tangentSpace p → β (P.E p w) t = β w t

/-- The **induced form** in the slice chart `φ`: `G(y)(a, b) = β(dψ_y a, dψ_y b)`. -/
def inducedForm (φ : OpenPartialHomeomorph F F) (y a b : S) : ℝ :=
  β (dMB (param φ) (y, a)) (dMB (param φ) (y, b))

/-- The derivative of the induced form in the base point:
`∂G(y)(u)(a, b) = d/dt G(y + t u)(a, b)|_{t = 0}`. -/
def inducedDeriv (φ : OpenPartialHomeomorph F F) (y u a b : S) : ℝ :=
  dMB (fun z : S ↦ inducedForm β φ z a b) (y, u)

variable {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (p₀ : X)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem hasDirDerivAt_pair (y u a : S) : HasDirDerivAt (fun z : S ↦ (z, a)) y u (u, 0) := by
  unfold HasDirDerivAt
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  ext <;> simp [smul_smul, inv_mul_cancel₀ ht]

theorem contDiffMBOn_pair (a : S) {U : Set S} (hU : IsOpen U) :
    ContDiffMBOn 1 (fun z : S ↦ (z, a)) U :=
  ((ContinuousLinearMap.id ℝ S).contDiffMBOn 1 U).prodMk hU (contDiffMBOn_const 1 a U)

include hφ in
/-- `y ↦ dψ_y a` is `C¹`. -/
theorem contDiffMBOn_dMB_param (a : S) :
    ContDiffMBOn 1 (fun y : S ↦ dMB (param φ) (y, a)) (Subtype.val ⁻¹' φ.target : Set S) := by
  have h2 : ContDiffMBOn 1 (dMB (param φ)) ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) :=
    ((smoothMBOn_param hφ) 2).2.2
  have := ContDiffMBOn.comp (g := dMB (param φ)) (f := fun y : S ↦ (y, a)) (isOpen_dom φ)
    ((isOpen_dom φ).prod isOpen_univ) h2 (contDiffMBOn_pair a (isOpen_dom φ))
    fun y hy ↦ ⟨hy, mem_univ _⟩
  exact this

include hφ in
/-- The derivative of `y ↦ dψ_y a` in the direction `u` is `d²ψ_y(u, a)`. -/
theorem dMB_dMB_param_line {y : S} (hy : (y : F) ∈ φ.target) (u a : S) :
    dMB (fun z : S ↦ dMB (param φ) (z, a)) (y, u) = dMB (dMB (param φ)) ((y, a), (u, 0)) := by
  have h2 : ContDiffMBOn 1 (dMB (param φ)) ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) :=
    ((smoothMBOn_param hφ) 2).2.2
  have hc := ContDiffMBOn.dMB_comp (g := dMB (param φ)) (f := fun y : S ↦ (y, a))
    ((isOpen_dom φ).prod isOpen_univ) h2 (contDiffMBOn_pair a (isOpen_dom φ))
    (fun z hz ↦ ⟨hz, mem_univ _⟩) (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy) u
  rw [(hasDirDerivAt_pair y u a).dMB_eq] at hc
  exact hc

variable {β}

include hφ in
/-- **The derivative of the induced form**:
`∂G(y)(u)(a, b) = β(dψ a, d²ψ(u, b)) + β(d²ψ(u, a), dψ b)`. -/
theorem inducedDeriv_eq (hβ : Continuous fun q : F × F ↦ β q.1 q.2) {y : S}
    (hy : (y : F) ∈ φ.target) (u a b : S) :
    inducedDeriv β φ y u a b =
      β (dMB (param φ) (y, a)) (dMB (dMB (param φ)) ((y, b), (u, 0))) +
        β (dMB (dMB (param φ)) ((y, a), (u, 0))) (dMB (param φ) (y, b)) := by
  have h := ContDiffMBOn.dMB_bilin β hβ (isOpen_dom φ) (contDiffMBOn_dMB_param hφ a)
    (contDiffMBOn_dMB_param hφ b) (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy) u
  rw [dMB_dMB_param_line hφ hy, dMB_dMB_param_line hφ hy] at h
  exact h

include hφ in
/-- The vectors `dψ_y s` are tangent. -/
theorem dMB_param_mem_tangentSpace {y : S} (hy : (y : F) ∈ φ.target) (s : S) :
    dMB (param φ) (y, s) ∈ h.tangentSpace ((sliceChart hφ p₀).symm y) := by
  rw [dMB_param hφ hy]
  exact h.dMB_symm_mem_tangentSpace hφ _ hy (sliceChart_symm_apply_coe hφ p₀ hy) s.2

/-- **Gauss: the connection of a `β`-orthogonal field of projectors is metric** for the induced
form, in every slice chart:
`∂G(y)(u)(a, b) = − G(y)(Γ(u, a), b) − G(y)(a, Γ(u, b))`. No sign condition on `β` is used. -/
theorem isMetric_symb (hβ : Continuous fun q : F × F ↦ β q.1 q.2)
    (hsymm : ∀ v w, β v w = β w v) (horth : P.IsOrthogonal β) {y : S}
    (hy : (y : F) ∈ φ.target) (u a b : S) :
    inducedDeriv β φ y u a b =
      -inducedForm β φ y (P.symb hφ p₀ y u a) b - inducedForm β φ y a (P.symb hφ p₀ y u b) := by
  set x := (sliceChart hφ p₀).symm y
  set d1 := dMB (dMB (param φ)) ((y, a), (u, 0))
  set d2 := dMB (dMB (param φ)) ((y, b), (u, 0))
  have e1 : β (P.E x d1) (dMB (param φ) (y, b)) = β d1 (dMB (param φ) (y, b)) :=
    horth x d1 _ (dMB_param_mem_tangentSpace hφ p₀ hy b)
  have e2 : β (dMB (param φ) (y, a)) (P.E x d2) = β (dMB (param φ) (y, a)) d2 := by
    rw [hsymm, horth x d2 _ (dMB_param_mem_tangentSpace hφ p₀ hy a), hsymm]
  rw [inducedDeriv_eq hφ hβ hy, inducedForm, inducedForm, P.dMB_param_symb hφ p₀ hy,
    P.dMB_param_symb hφ p₀ hy]
  simp only [map_neg, LinearMap.neg_apply]
  rw [e1, e2]
  ring

include hφ in
/-- The induced form is additive in its first argument. -/
theorem inducedForm_sub {y : S} (hy : (y : F) ∈ φ.target) (c c' b : S) :
    inducedForm β φ y (c - c') b = inducedForm β φ y c b - inducedForm β φ y c' b := by
  have hd : ContDiffMBOn 1 (param φ) (Subtype.val ⁻¹' φ.target : Set S) :=
    (smoothMBOn_param hφ) 1
  have hy' : y ∈ (Subtype.val ⁻¹' φ.target : Set S) := hy
  have hsub : dMB (param φ) (y, c - c') = dMB (param φ) (y, c) - dMB (param φ) (y, c') := by
    rw [sub_eq_add_neg, hd.dMB_add (isOpen_dom φ) hy', ← neg_one_smul ℝ c',
      hd.dMB_smul hy', neg_one_smul, ← sub_eq_add_neg]
  simp only [inducedForm, hsub, LinearMap.map_sub₂]

include hφ p₀ in
/-- **The induced form is weakly nondegenerate** when `β` is and `P` is `β`-orthogonal: the
tangent spaces of `X` are nondegenerate (`nondegenerate_of_orthogonal`) and `dψ_y` is an
injection of `S` onto `T_p X`. -/
theorem inducedForm_nondegenerate (hnd : ∀ t, (∀ w, β w t = 0) → t = 0)
    (hsymm : ∀ v w, β v w = β w v) (horth : P.IsOrthogonal β) {y : S} (hy : (y : F) ∈ φ.target)
    (c : S) (hc : ∀ b, inducedForm β φ y c b = 0) : c = 0 := by
  set x := (sliceChart hφ p₀).symm y
  have hx : ((x : X) : F) = φ.symm y := sliceChart_symm_apply_coe hφ p₀ hy
  -- every tangent vector is `dψ_y s` for some `s ∈ S`
  have hsurj : ∀ t ∈ h.tangentSpace x, ∃ s : S, dMB (param φ) (y, s) = t := by
    intro t ht
    have hxsrc : (x : F) ∈ φ.source := by rw [hx]; exact φ.map_target hy
    have hS := (h.mem_tangentSpace_iff x hφ hxsrc t).mp ht
    refine ⟨⟨_, hS⟩, ?_⟩
    rw [dMB_param hφ hy]
    change dMB φ.symm ((y : F), dMB φ ((x : F), t)) = t
    have := dMB_symm_dMB_chart hφ.1 hxsrc t
    rw [hx] at this ⊢
    rwa [φ.right_inv hy] at this
  have hrange : ∀ t, t ∈ h.tangentSpace x ↔ t ∈ range (P.E x) := fun t ↦ by rw [P.range_eq]
  have hzero : dMB (param φ) (y, c) = 0 := by
    refine nondegenerate_of_orthogonal hnd (Q := P.E x)
      (fun w t ht ↦ horth x w t ((hrange t).mpr ht))
      ((hrange _).mp (dMB_param_mem_tangentSpace hφ p₀ hy c)) fun s hs ↦ ?_
    obtain ⟨b, rfl⟩ := hsurj s ((hrange s).mpr hs)
    rw [hsymm]
    exact hc b
  apply dMB_param_injective hφ hy
  change dMB (param φ) (y, c) = dMB (param φ) (y, 0)
  rw [hzero, dMB_param_zero hφ hy]

/-- **The projector connection is the Levi-Civita connection** of the induced metric, in every
slice chart, for `β` of any signature: if `β` is weakly nondegenerate and `P` is
`β`-orthogonal, every symmetric family of symbols compatible with the induced form coincides
with the symbols of `P`. -/
theorem symb_eq_of_isMetric (hβ : Continuous fun q : F × F ↦ β q.1 q.2)
    (hnd : ∀ t, (∀ w, β w t = 0) → t = 0) (hsymm : ∀ v w, β v w = β w v)
    (horth : P.IsOrthogonal β) {y : S} (hy : (y : F) ∈ φ.target) {Γ : S → S → S}
    (hΓ : ∀ u a, Γ u a = Γ a u)
    (hm : ∀ u a b, inducedDeriv β φ y u a b =
      -inducedForm β φ y (Γ u a) b - inducedForm β φ y a (Γ u b)) (u a : S) :
    Γ u a = P.symb hφ p₀ y u a :=
  eq_of_koszul (fun _ _ ↦ hsymm _ _) (inducedForm_sub hφ hy)
    (P.inducedForm_nondegenerate hφ p₀ hnd hsymm horth hy) hΓ hm
    (fun u a ↦ P.symb_symm hφ p₀ y u a) (P.isMetric_symb hφ p₀ hβ hsymm horth hy) u a

/-! ### The induced metric on `X` -/

section Global

variable (β)

include hφ in
theorem inducedForm_add_left {y : S} (hy : (y : F) ∈ φ.target) (a a' b : S) :
    inducedForm β φ y (a + a') b = inducedForm β φ y a b + inducedForm β φ y a' b := by
  simp only [inducedForm, ((smoothMBOn_param hφ) 1).dMB_add (isOpen_dom φ)
    (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy), LinearMap.map_add₂]

include hφ in
theorem inducedForm_smul_left {y : S} (hy : (y : F) ∈ φ.target) (c : ℝ) (a b : S) :
    inducedForm β φ y (c • a) b = c * inducedForm β φ y a b := by
  simp only [inducedForm, ((smoothMBOn_param hφ) 1).dMB_smul
    (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy), LinearMap.map_smul₂, smul_eq_mul]

include hφ in
theorem inducedForm_add_right {y : S} (hy : (y : F) ∈ φ.target) (a b b' : S) :
    inducedForm β φ y a (b + b') = inducedForm β φ y a b + inducedForm β φ y a b' := by
  simp only [inducedForm, ((smoothMBOn_param hφ) 1).dMB_add (isOpen_dom φ)
    (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy)]
  exact (β _).map_add _ _

include hφ in
theorem inducedForm_smul_right {y : S} (hy : (y : F) ∈ φ.target) (c : ℝ) (a b : S) :
    inducedForm β φ y a (c • b) = c * inducedForm β φ y a b := by
  simp only [inducedForm, ((smoothMBOn_param hφ) 1).dMB_smul
    (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy)]
  rw [(β _).map_smul, smul_eq_mul]

/-- The induced form at a point of a slice chart, as a bilinear form on `S`. -/
def bilinAt {y : S} (hy : (y : F) ∈ φ.target) : LinearMap.BilinForm ℝ S :=
  LinearMap.mk₂ ℝ (inducedForm β φ y) (inducedForm_add_left β hφ hy)
    (inducedForm_smul_left β hφ hy) (inducedForm_add_right β hφ hy)
    (inducedForm_smul_right β hφ hy)

theorem bilinAt_apply {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    bilinAt β hφ hy a b = inducedForm β φ y a b := rfl

variable {β}

include hφ in
/-- The induced form is smooth in `(y, a, b)`. -/
theorem smoothMBOn_inducedForm (hβ : Continuous fun q : F × F ↦ β q.1 q.2) :
    SmoothMBOn (fun q : S × S × S ↦ inducedForm β φ q.1 q.2.1 q.2.2)
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) := fun k ↦ by
  have hd : ContDiffMBOn k (dMB (param φ)) ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) :=
    ((smoothMBOn_param hφ) (k + 1)).2.2
  have hopen : IsOpen ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set S)) :=
    (isOpen_dom φ).prod isOpen_univ
  let L₁ : S × S × S →L[ℝ] S × S :=
    (ContinuousLinearMap.fst ℝ S (S × S)).prod
      ((ContinuousLinearMap.fst ℝ S S).comp (ContinuousLinearMap.snd ℝ S (S × S)))
  let L₂ : S × S × S →L[ℝ] S × S :=
    (ContinuousLinearMap.fst ℝ S (S × S)).prod
      ((ContinuousLinearMap.snd ℝ S S).comp (ContinuousLinearMap.snd ℝ S (S × S)))
  have hsub₁ : (Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set (S × S)) ⊆
      L₁ ⁻¹' ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) := fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hsub₂ : (Subtype.val ⁻¹' φ.target : Set S) ×ˢ (univ : Set (S × S)) ⊆
      L₂ ⁻¹' ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) := fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have h₁ := (ContDiffMBOn.comp_clm L₁ hopen hd).mono hsub₁
  have h₂ := (ContDiffMBOn.comp_clm L₂ hopen hd).mono hsub₂
  exact ContDiffMBOn.bilin β hβ ((isOpen_dom φ).prod isOpen_univ) h₁ h₂

/-- **The chain rule for parametrizations**: if `τ` is the change of slice charts from `φ` to
`φ'`, then `dψ'_{τ y}(dτ_y v) = dψ_y v`, since `ψ' ∘ τ = ψ` near `y`. -/
theorem dMB_param_transition (hS : IsClosed (S : Set F)) {φ' : OpenPartialHomeomorph F F}
    (hφ' : IsSliceChart X S φ')
    (p₁ : X) {y : S} (hy : y ∈ (sliceChart hφ p₀).target ∩
      (sliceChart hφ p₀).symm ⁻¹' (sliceChart hφ' p₁).source) (v : S) :
    dMB (param φ') ((sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) y,
        dMB (sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) (y, v)) = dMB (param φ) (y, v) := by
  set e := sliceChart hφ p₀
  set e' := sliceChart hφ' p₁
  set τ : S → S := e' ∘ e.symm
  set W := e.target ∩ e.symm ⁻¹' e'.source
  have hW : IsOpen W := e.isOpen_inter_preimage_symm e'.open_source
  have hτ : SmoothMBOn τ W := by
    have := smoothMBOn_sliceChart_transition hS hφ hφ' p₀ p₁
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans] at this
  have hψψ' : ∀ z ∈ W, (param φ' ∘ τ) z = param φ z := by
    intro z hz
    change φ'.symm ((e' (e.symm z) : S) : F) = φ.symm z
    rw [sliceChart_apply_coe hφ' p₁ hz.2, φ'.left_inv hz.2, sliceChart_symm_apply_coe hφ p₀ hz.1]
  have hmapsτ : MapsTo τ W (Subtype.val ⁻¹' φ'.target) := fun z hz ↦ e'.map_source hz.2
  have hc := ContDiffMBOn.dMB_comp (isOpen_dom φ') ((smoothMBOn_param hφ') 1) (hτ 1) hmapsτ hy v
  have hev : param φ' ∘ τ =ᶠ[𝓝 y] param φ :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hy) hψψ'
  rw [← hc, dMB_congr_of_eventuallyEq hev]

end Global

variable (β) in
/-- The induced metric on `X`: at `x`, the induced form in the preferred slice chart. -/
def inducedFun (x : X) : LinearMap.BilinForm ℝ S :=
  bilinAt β (h.exists_sliceChart x x.2).choose_spec.1
    ((sliceChart (h.exists_sliceChart x x.2).choose_spec.1 x).map_source
      (h.exists_sliceChart x x.2).choose_spec.2)

theorem inducedFun_apply (x : X) (a b : S) :
    inducedFun (h := h) β x a b =
      inducedForm β (h.exists_sliceChart x x.2).choose
        (sliceChart (h.exists_sliceChart x x.2).choose_spec.1 x x) a b := rfl

/-- **The local representative of the induced metric** in a chart `i = sliceChart φ p₀` of `X`
is the induced form `β(dψ a, dψ b)` of that chart. -/
theorem bilinLocalRep_inducedFun :
    letI := h.chartedSpace; haveI := h.mbManifold
    ∀ (i : atlas S X), (i : OpenPartialHomeomorph X S) = sliceChart hφ p₀ → ∀ {y : S},
      y ∈ (i : OpenPartialHomeomorph X S).target → ∀ a b : S,
      bilinLocalRep (inducedFun (h := h) β) i (y, a, b) = inducedForm β φ y a b := by
  let := h.chartedSpace
  have := h.mbManifold
  intro i hi y hy a b
  obtain ⟨e, he⟩ := i
  change e = sliceChart hφ p₀ at hi
  subst hi
  set x : X := (sliceChart hφ p₀).symm y
  have hφx := (h.exists_sliceChart x x.2).choose_spec.1
  have hxi : sliceChart hφ p₀ x = y := (sliceChart hφ p₀).right_inv hy
  have hW : y ∈ (sliceChart hφ p₀).target ∩
      (sliceChart hφ p₀).symm ⁻¹' (sliceChart hφx x).source :=
    ⟨hy, mem_chart_source S x⟩
  have ea := dMB_param_transition hφ p₀ h.isClosed hφx x hW a
  have eb := dMB_param_transition hφ p₀ h.isClosed hφx x hW b
  simp only [bilinLocalRep, inducedFun_apply, inducedForm, tangentCoordChange]
  rw [← ea, ← eb]
  have hxi' : sliceChart hφ p₀ ((sliceChart hφ p₀).symm y) = y := hxi
  rw [hxi']
  rfl

/-- **The induced metric** of `β` on `X`, a smooth field of symmetric bilinear forms of the same
signature type as `β`. -/
def inducedMetric (hβ : Continuous fun q : F × F ↦ β q.1 q.2) (hsymm : ∀ v w, β v w = β w v) :
    letI := h.chartedSpace; haveI := h.mbManifold; SymmBilinField S X := by
  let := h.chartedSpace
  have := h.mbManifold
  exact
  { toFun := inducedFun (h := h) β
    symm' := fun x v w ↦ hsymm _ _
    smooth' := fun i ↦ by
      have hi := i.2.choose_spec.choose_spec.choose_spec
      have hsm := smoothMBOn_inducedForm i.2.choose_spec.choose hβ
      refine fun k ↦ ContDiffMBOn.congr_of_isOpen ?_ ?_ ((hsm k).mono ?_)
      · exact (i : OpenPartialHomeomorph X S).open_target.prod isOpen_univ
      · intro q hq
        exact (bilinLocalRep_inducedFun i.2.choose_spec.choose i.2.choose_spec.choose_spec.choose
          i hi hq.1 q.2.1 q.2.2).symm
      · intro q hq
        rw [hi] at hq
        exact hq }

/-- **The connection of a `β`-orthogonal field of projectors is metric** for the induced
metric, with any signature of `β`. -/
theorem connection_isMetric (hβ : Continuous fun q : F × F ↦ β q.1 q.2)
    (hsymm : ∀ v w, β v w = β w v) (horth : P.IsOrthogonal β) :
    letI := h.chartedSpace; haveI := h.mbManifold
    P.connection.IsMetric (inducedMetric (h := h) hβ hsymm) := by
  let := h.chartedSpace
  have := h.mbManifold
  intro i y hy u a b
  have hi := i.2.choose_spec.choose_spec.choose_spec
  set hφ := i.2.choose_spec.choose
  set p₀ := i.2.choose_spec.choose_spec.choose
  set φ := i.2.choose
  have hyT : (y : F) ∈ φ.target := by rw [hi] at hy; exact hy
  have hF : ∀ c d, (inducedMetric (h := h) hβ hsymm).localForm i y c d = inducedForm β φ y c d :=
    fun c d ↦ bilinLocalRep_inducedFun hφ p₀ i hi hy c d
  have hD : (inducedMetric (h := h) hβ hsymm).localDeriv i y u a b = inducedDeriv β φ y u a b := by
    have hopen : IsOpen ((i : OpenPartialHomeomorph X S).target ×ˢ (univ : Set (S × S))) :=
      (i : OpenPartialHomeomorph X S).open_target.prod isOpen_univ
    have hev : bilinLocalRep (inducedFun (h := h) β) i =ᶠ[𝓝 (y, a, b)]
        fun q : S × S × S ↦ inducedForm β φ q.1 q.2.1 q.2.2 :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds ⟨hy, mem_univ _⟩) fun q hq ↦
        bilinLocalRep_inducedFun hφ p₀ i hi hq.1 q.2.1 q.2.2
    change dMB (bilinLocalRep (inducedFun (h := h) β) i) ((y, a, b), (u, 0, 0)) = _
    rw [dMB_congr_of_eventuallyEq hev]
    simp only [inducedDeriv, dMB]
    congr 1
    funext t
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  rw [hD, hF, hF]
  exact P.isMetric_symb hφ p₀ hβ hsymm horth hyT u a b

/-- The induced metric is weakly nondegenerate when `β` is and `P` is `β`-orthogonal. -/
theorem inducedMetric_isWeaklyNondegenerate (hβ : Continuous fun q : F × F ↦ β q.1 q.2)
    (hnd : ∀ t, (∀ w, β w t = 0) → t = 0) (hsymm : ∀ v w, β v w = β w v)
    (horth : P.IsOrthogonal β) :
    letI := h.chartedSpace; haveI := h.mbManifold
    (inducedMetric (h := h) hβ hsymm).IsWeaklyNondegenerate := by
  let := h.chartedSpace
  have := h.mbManifold
  intro x v hv
  exact P.inducedForm_nondegenerate (h.exists_sliceChart x x.2).choose_spec.1 x hnd hsymm horth
    ((sliceChart (h.exists_sliceChart x x.2).choose_spec.1 x).map_source
      (h.exists_sliceChart x x.2).choose_spec.2) v hv

/-- **The projector connection is the Levi-Civita connection of the induced metric**, for `β`
of any signature: if `β` is weakly nondegenerate and `P` is `β`-orthogonal, every symmetric
connection which is metric for the induced metric has the covariant derivative of `P`. -/
theorem covDeriv_eq_connection (hβ : Continuous fun q : F × F ↦ β q.1 q.2)
    (hnd : ∀ t, (∀ w, β w t = 0) → t = 0) (hsymm : ∀ v w, β v w = β w v)
    (horth : P.IsOrthogonal β) :
    letI := h.chartedSpace; haveI := h.mbManifold
    ∀ C : Connection S X, C.IsSymmetric → C.IsMetric (inducedMetric (h := h) hβ hsymm) →
      ∀ Y Z : X → Bundle.TotalSpace S (fun x : X ↦ (tangentBundleCore S X).Fiber x),
        C.covDeriv Y Z = P.connection.covDeriv Y Z := by
  let := h.chartedSpace
  have := h.mbManifold
  intro C hC hm Y Z
  exact Connection.covDeriv_eq_of_isMetric
    (P.inducedMetric_isWeaklyNondegenerate hβ hnd hsymm horth) hC hm P.connection_isSymmetric
    (P.connection_isMetric hβ hsymm horth) Y Z

/-- When `β` is positive definite (an inner product, not necessarily complete), the induced
metric is a **weak Riemannian metric** on `X`. -/
def inducedRiemannian (hβ : Continuous fun q : F × F ↦ β q.1 q.2) (hsymm : ∀ v w, β v w = β w v)
    (hpos : ∀ w, w ≠ 0 → 0 < β w w) :
    letI := h.chartedSpace; haveI := h.mbManifold; WeakRiemannianMetric S X := by
  let := h.chartedSpace
  have := h.mbManifold
  exact
  { toSymmBilinField := inducedMetric (h := h) hβ hsymm
    pos_def' := fun x a ha ↦ by
      have hφx := (h.exists_sliceChart x x.2).choose_spec.1
      have hy := (sliceChart hφx x).map_source (h.exists_sliceChart x x.2).choose_spec.2
      refine hpos _ fun h0 ↦ ha ?_
      apply dMB_param_injective hφx hy
      change dMB (param _) (_, a) = dMB (param _) (_, 0)
      rw [dMB_param_zero hφx hy]
      exact h0 }

end ProjectorField

end LocallyConvex.Manifolds

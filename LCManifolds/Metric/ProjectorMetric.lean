/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Projector
import LCManifolds.Metric.LeviCivita

/-!
# Orthogonal projectors and the Levi-Civita connection of a submanifold, any signature

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, §6.6
(Teorema 6.6.1, "derivar y proyectar") and §10.1.1 (the Levi-Civita derivative of a
submanifold); J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974), Theorem V.3.4 and
Example V.3.3 (ortho-complemented subspaces of Krein spaces).

Let `β` be a continuous symmetric bilinear form on the ambient space `F`, of **any signature**
(an inner product, or the indefinite form of a Krein or Pontryagin space), and let `X ⊆ F` be an
embedded submanifold with a field of projectors `P` onto its tangent spaces
(`LCManifolds.ProjectorField`). The **induced form** in a slice chart `φ`, with
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
  compatible with `G` coincide with them (Koszul, `LCManifolds.eq_of_koszul`).

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
open LCAnalysis

noncomputable section

namespace LCManifolds

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

end ProjectorField

end LCManifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.DifferentialForm
import LocallyConvexManifolds.VectorField
import LocallyConvexManifolds.Derivation

/-!
# Insertion of vector fields, the Lie derivative and Cartan's formula

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, §3.6.

For a smooth vector field `X` on `M` and `ω ∈ Ωⁿ⁺¹(M, F)`, the insertion `i_X ω ∈ Ωⁿ(M, F)` is
`(i_X ω)ₓ(v₁, …, vₙ) = ωₓ(X(x), v₁, …, vₙ)` (Glöckner–Neeb, Definition 3.6.15). The Lie
derivative `L_X ω ∈ Ωⁿ(M, F)` is defined by Glöckner–Neeb through vector fields, (3.35); in
charts it reads
`(L_X ω)(y)(v₁, …, vₙ) = ∂_{X(y)} ω(y)(v₁, …, vₙ) + ∑ₖ ω(y)(v₁, …, dX(y) vₖ, …, vₙ)`.

We define `L_X ω` by **Cartan's formula**, `L_X = d ∘ i_X + i_X ∘ d` (with `i_X = 0` on
`0`-forms), which produces a smooth form without further work, and prove that in every chart it
is given by the local formula above (`localRep_lieDeriv`), which is the chart form of (3.35)
(Glöckner–Neeb, Definition 3.6.14). Then:

* `lieDeriv_interior_sub`: `[L_X, i_Y] = i_{[X, Y]}` (Glöckner–Neeb, Proposition 3.6.16 (b)),
  by a computation in charts;
* `lieDeriv_d`: `L_X ∘ d = d ∘ L_X` (Proposition 3.6.16 (d)), from `d ∘ d = 0`;
* `lieDeriv_lieDeriv_sub`: `[L_X, L_Y] = L_{[X, Y]}` (Proposition 3.6.16 (a)), algebraically from
  (b), (c) and (d);
* `IsClosed.lieDeriv_eq`: `L_X ω = d(i_X ω)` for closed `ω` (Proposition 3.6.16 (e)).

Glöckner–Neeb prove (a)–(d) by embedding forms into the Chevalley–Eilenberg complex of the Lie
algebra of vector fields with values in `C^∞(M, F)`; we compute in charts instead. In infinite
dimensions vector fields need not have flows, so `L_X` cannot be defined by differentiating
along a flow (Glöckner–Neeb, Remark 3.6.17).

No completeness of the spaces is assumed.
-/

open Set Function Filter
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

/-! ### Local insertion and the local Lie derivative -/

section Local

variable {E F : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {n : ℕ}

theorem _root_.Fin.removeNth_succ_cons {α : Type*} (j : Fin (n + 1)) (a : α)
    (v : Fin (n + 1) → α) :
    Fin.removeNth j.succ (Fin.cons a v : Fin (n + 2) → α) = Fin.cons a (Fin.removeNth j v) := by
  funext k
  cases k using Fin.cases with
  | zero => simp [Fin.removeNth_apply]
  | succ k => simp [Fin.removeNth_apply, Fin.succ_succAbove_succ]

/-- The local insertion of a vector field: `(i_X ω)(y)(v) = ω(y)(X(y), v)`. -/
def iLoc (X : E → E) (ω : E × (Fin (n + 1) → E) → F) (p : E × (Fin n → E)) : F :=
  ω (p.1, Fin.cons (X p.1) p.2)

/-- The local Lie derivative (Glöckner–Neeb, (3.35) in a chart):
`(L_X ω)(y)(v) = ∂_{X(y)} ω(y)(v) + ∑ₖ ω(y)(v₁, …, dX(y) vₖ, …, vₙ)`. -/
def lieLoc (X : E → E) (ω : E × (Fin n → E) → F) (p : E × (Fin n → E)) : F :=
  dMB (fun z ↦ ω (z, p.2)) (p.1, X p.1) + ∑ k : Fin n, ω (p.1, update p.2 k (dMB X (p.1, p.2 k)))

/-- The map `(y, v) ↦ (y, (X y, v))`. -/
theorem ContDiffMBOn.consField {k : ℕ} {X : E → E} {U : Set E} (hU : IsOpen U)
    (hX : ContDiffMBOn k X U) :
    ContDiffMBOn k (fun p : E × (Fin n → E) ↦ (p.1, (Fin.cons (X p.1) p.2 : Fin (n + 1) → E)))
      (U ×ˢ univ) := by
  have hU' : IsOpen (U ×ˢ (univ : Set (Fin n → E))) := hU.prod isOpen_univ
  have h₀ : ContDiffMBOn k (fun p : E × (Fin n → E) ↦ X p.1) (U ×ˢ univ) := by
    have := hX.comp_clm (ContinuousLinearMap.fst ℝ E (Fin n → E)) hU
    rwa [show (ContinuousLinearMap.fst ℝ E (Fin n → E)) ⁻¹' U = U ×ˢ univ by ext; simp] at this
  refine ContDiffMBOn.prodMk hU'
    ((ContinuousLinearMap.fst ℝ E (Fin n → E)).contDiffMBOn k _) (ContDiffMBOn.pi hU' ?_)
  intro j
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact h₀
  | succ j =>
    simp only [Fin.cons_succ]
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ E) j).comp
      (ContinuousLinearMap.snd ℝ E (Fin n → E))).contDiffMBOn k (U ×ˢ univ)

variable {ω : E × (Fin (n + 1) → E) → F} {U : Set E} {X : E → E}

/-- The insertion of a smooth vector field into a local form is a local form. -/
theorem IsLocalForm.iLoc (hω : IsLocalForm (n + 1) ω U) (hU : IsOpen U) (hX : SmoothMBOn X U) :
    IsLocalForm n (iLoc X ω) U := by
  refine ⟨fun k ↦ (hω.smooth k).comp (hU.prod isOpen_univ) (hU.prod isOpen_univ)
    (ContDiffMBOn.consField hU (hX k)) fun p hp ↦ ⟨hp.1, mem_univ _⟩, fun y hy ↦ ?_⟩
  obtain ⟨A, hA⟩ := hω.alternating y hy
  exact ⟨A.curryLeft (X y), fun v ↦ by simp only [LocallyConvex.Manifolds.iLoc, hA]; rfl⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] in
theorem iLoc_congr {ω₁ ω₂ : E × (Fin (n + 1) → E) → F} {X₁ X₂ : E → E} {y : E}
    (hω : ∀ w, ω₁ (y, w) = ω₂ (y, w)) (hX : X₁ y = X₂ y) (v : Fin n → E) :
    LocallyConvex.Manifolds.iLoc X₁ ω₁ (y, v) = LocallyConvex.Manifolds.iLoc X₂ ω₂ (y, v) := by
  simp only [LocallyConvex.Manifolds.iLoc, hω, hX]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The derivative of `z ↦ ω(z, W(z))`: a partial derivative in the base point and one term for
each vector. -/
theorem IsLocalForm.dMB_comp_vectors {m : ℕ} {η : E × (Fin m → E) → F} {V : Set E}
    (hη : IsLocalForm m η V) (hV : IsOpen V) {W : E → Fin m → E} {y u : E} (hy : y ∈ V)
    {D : Fin m → E} (hW : ∀ k, HasDirDerivAt (fun z ↦ W z k) y u (D k)) :
    dMB (fun z ↦ η (z, W z)) (y, u) =
      dMB (fun z ↦ η (z, W y)) (y, u) + ∑ k, η (y, update (W y) k (D k)) := by
  classical
  have hV' : IsOpen (V ×ˢ (univ : Set (Fin m → E))) := hV.prod isOpen_univ
  have hη1 : ContDiffMBOn 1 η (V ×ˢ univ) := hη.smooth 1
  have hΨ : HasDirDerivAt (fun z ↦ (z, W z)) y u (u, D) :=
    ((ContinuousLinearMap.id ℝ E).hasDirDerivAt y u).prodMk (hasDirDerivAt_pi.mpr hW)
  have hchain := (hη1.hasDirDerivAt_comp hV' hΨ ⟨hy, mem_univ _⟩).dMB_eq
  have hsplit : dMB η ((y, W y), (u, D)) =
      dMB η ((y, W y), (u, 0)) + dMB η ((y, W y), (0, D)) := by
    rw [← hη1.dMB_add hV' ⟨hy, mem_univ _⟩]; simp
  have h0 : ContinuousOn η (V ×ˢ univ) := hη.smooth 0
  have hcont : Continuous fun w' : Fin m → E ↦ η (y, w') :=
    continuousOn_univ.mp <| h0.comp (Continuous.continuousOn (by fun_prop))
      fun _ _ ↦ ⟨hy, mem_univ _⟩
  have hmult := hasDirDerivAt_of_multilinear hcont
    (fun w' k a b ↦ hη.map_update_add hy w' k a b)
    (fun w' k c a ↦ hη.map_update_smul hy w' k c a) (W y) D
  change dMB (η ∘ fun z ↦ (z, W z)) (y, u) = _
  rw [hchain, hsplit, dMB_slice, dMB_slice₂, hmult.dMB_eq]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The derivative of `z ↦ ω(z, X(z), w)`. -/
theorem IsLocalForm.dMB_iLoc (hω : IsLocalForm (n + 1) ω U) (hU : IsOpen U)
    (hX : ContDiffMBOn 1 X U) {y : E} (hy : y ∈ U) (w : Fin n → E) (u : E) :
    dMB (fun z ↦ ω (z, Fin.cons (X z) w)) (y, u) =
      dMB (fun z ↦ ω (z, Fin.cons (X y) w)) (y, u) + ω (y, Fin.cons (dMB X (y, u)) w) := by
  classical
  have hW : ∀ k, HasDirDerivAt (fun z ↦ (Fin.cons (X z) w : Fin (n + 1) → E) k) y u
      ((Fin.cons (dMB X (y, u)) 0 : Fin (n + 1) → E) k) := by
    intro k
    cases k using Fin.cases with
    | zero => simpa using hX.2.1 y hy u
    | succ k =>
      simp only [Fin.cons_succ, Pi.zero_apply]
      simp only [HasDirDerivAt, sub_self, smul_zero]
      exact tendsto_const_nhds
  rw [hω.dMB_comp_vectors hU hy hW, Fin.sum_univ_succ]
  obtain ⟨A, hA⟩ := hω.alternating y hy
  simp only [hA, Fin.cons_zero, Fin.update_cons_zero, Fin.cons_succ, Pi.zero_apply,
    A.map_update_zero, Finset.sum_const_zero, add_zero]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [TopologicalSpace F] in
theorem neg_one_pow_smul_map_cons_removeNth (A : E [⋀^Fin (n + 1)]→ₗ[ℝ] F) (v : Fin (n + 1) → E)
    (j : Fin (n + 1)) (a : E) :
    (-1 : ℝ) ^ (j : ℕ) • A (Fin.cons a (j.removeNth v)) = A (update v j a) := by
  rw [AlternatingMap.map_update_eq_neg_one_pow_smul, neg_one_pow_smul_eq_zsmul]
  rfl

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **Cartan's formula in a chart**: `d(i_X ω) + i_X(dω) = L_X ω` for local `(n+1)`-forms. -/
theorem IsLocalForm.dLoc_iLoc_add (hω : IsLocalForm (n + 1) ω U) (hU : IsOpen U)
    (hX : ContDiffMBOn 1 X U) {y : E} (hy : y ∈ U) (v : Fin (n + 1) → E) :
    LocallyConvex.Manifolds.dLoc (LocallyConvex.Manifolds.iLoc X ω) (y, v) +
        LocallyConvex.Manifolds.iLoc X (LocallyConvex.Manifolds.dLoc ω) (y, v) =
      lieLoc X ω (y, v) := by
  obtain ⟨A, hA⟩ := hω.alternating y hy
  simp only [IsLocalForm.dLoc_apply, LocallyConvex.Manifolds.iLoc, lieLoc]
  rw [Fin.sum_univ_succ (n := n + 1)]
  have hsign : ∀ j : Fin (n + 1), (-1 : ℝ) ^ ((j : ℕ) + 1) = -(-1) ^ (j : ℕ) := fun j ↦ by
    rw [pow_succ, mul_neg_one]
  have hterm : ∀ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) • ω (y, Fin.cons (dMB X (y, v j))
      (j.removeNth v)) = ω (y, update v j (dMB X (y, v j))) := fun j ↦ by
    rw [hA, hA]; exact neg_one_pow_smul_map_cons_removeNth A v j _
  simp only [hω.dMB_iLoc hU hX hy, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
    Fin.cons_succ, Fin.removeNth_succ_cons, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    hsign, neg_smul, smul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib, hterm]
  abel

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local Lie derivative of a local `0`-form is `i_X(dω)`. -/
theorem iLoc_dLoc_zero (ω : E × (Fin 0 → E) → F) (y : E) (v : Fin 0 → E) :
    LocallyConvex.Manifolds.iLoc X (dLoc ω) (y, v) = lieLoc X ω (y, v) := by
  have hv : (0 : Fin 1).removeNth (Fin.cons (X y) v : Fin 1 → E) = v := Subsingleton.elim _ _
  simp only [LocallyConvex.Manifolds.iLoc, IsLocalForm.dLoc_apply, lieLoc,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, hv]

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
theorem lieLoc_congr {m : ℕ} {ω₁ ω₂ : E × (Fin m → E) → F} {X₁ X₂ : E → E} {W : Set E}
    (hW : IsOpen W) (hω : EqOn ω₁ ω₂ (W ×ˢ univ)) (hX : EqOn X₁ X₂ W) {y : E} (hy : y ∈ W)
    (v : Fin m → E) : lieLoc X₁ ω₁ (y, v) = lieLoc X₂ ω₂ (y, v) := by
  have hXe : X₁ =ᶠ[𝓝 y] X₂ := eventuallyEq_of_mem (hW.mem_nhds hy) hX
  simp only [lieLoc, hX hy, dMB_congr_of_eventuallyEq hXe]
  rw [dMB_congr_of_eventuallyEq (eventuallyEq_of_mem (hW.mem_nhds hy)
    fun z hz ↦ hω ⟨hz, mem_univ _⟩)]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ hω ⟨hy, mem_univ _⟩)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [TopologicalSpace F] in
/-- The combinatorics behind the formula for `dω` on vector fields: the terms with first
derivatives of the vector fields regroup into brackets. Here `D a b` stands for the derivative
of the `b`-th vector field in the direction of the `a`-th one. -/
theorem sum_neg_one_pow_smul_sum_update_eq (A : E [⋀^Fin (n + 1)]→ₗ[ℝ] F)
    (V : Fin (n + 2) → E) (D : Fin (n + 2) → Fin (n + 2) → E) :
    ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) • ∑ k : Fin (n + 1),
        A (update (i.removeNth V) k (D i (i.succAbove k))) =
      ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℝ) ^ ((i : ℕ) + j) •
        A (Fin.cons (D i.castSucc j.succ - D j.succ i.castSucc)
          (j.removeNth (i.castSucc.removeNth V))) := by
  have hcons : ∀ (a b : E) (w : Fin n → E),
      A (Fin.cons (a - b) w) = A (Fin.cons a w) - A (Fin.cons b w) := fun a b w ↦ by
    have h := A.map_update_sub (Fin.cons a w : Fin (n + 1) → E) 0 a b
    simpa only [Fin.update_cons_zero] using h
  simp only [← neg_one_pow_smul_map_cons_removeNth A, Finset.smul_sum, smul_smul, ← pow_add]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Ici] at hj
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  have hw : j.removeNth (i.castSucc.removeNth V) = i.removeNth (j.succ.removeNth V) := by
    rw [Fin.removeNth_removeNth_eq_swap, H₁, H₂]
  rw [H₁, H₃, ← hw, hcons, Fin.val_castSucc, Fin.val_succ,
    show (j : ℕ) + 1 + i = (i + j) + 1 by omega, show (i : ℕ) + j = i + j from rfl, pow_succ,
    mul_neg_one, neg_smul, smul_sub, sub_eq_add_neg]

end Local

/-! ### Smooth vector fields -/

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

variable (E M) in
/-- Smooth vector fields on `M`. -/
structure SmoothVectorField where
  /-- The vector field as a section of the tangent bundle. -/
  toFun : M → TangentBundle E M
  isVectorField : IsVectorField toFun
  smooth : ∀ k, ContMDiffMB E (E × E) k toFun

namespace SmoothVectorField

instance : CoeFun (SmoothVectorField E M) fun _ ↦ M → TangentBundle E M := ⟨toFun⟩

/-- The local representative of `X` in the chart `i`. -/
abbrev rep (X : SmoothVectorField E M) (i : atlas E M) : E → E := localRep i X

/-- The value `X(x)`, in the preferred chart at `x`. -/
def vec (X : SmoothVectorField E M) (x : M) : E := ((X x).2 : E)

/-- The local representatives of a smooth vector field are smooth. -/
theorem smoothMBOn_localRep (X : SmoothVectorField E M) (i : atlas E M) :
    SmoothMBOn (localRep i X) i.1.target := fun k ↦
  contDiffMBOn_localRep X.isVectorField (X.smooth k) i

/-- The local representative in the chart `i`, transported to the preferred chart, is the value
of the vector field. -/
theorem tangentCoordChange_localRep (X : SmoothVectorField E M) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) :
    tangentCoordChange i (prefChart (i.1.symm y)) (i.1.symm y) (localRep i X y) =
      X.vec (i.1.symm y) := by
  have hx : i.1.symm y ∈ i.1.source := i.1.map_target hy
  unfold localRep vec
  have hp : (X (i.1.symm y)).proj = i.1.symm y := X.isVectorField _
  generalize X (i.1.symm y) = p at hp ⊢
  obtain ⟨xp, w⟩ := p
  change xp = i.1.symm y at hp
  subst hp
  rw [tangentChart_apply]
  have key : ∀ w' : E, tangentCoordChange i (prefChart (i.1.symm y)) (i.1.symm y)
      (tangentCoordChange (prefChart (i.1.symm y)) i (i.1.symm y) w') = w' := fun w' ↦ by
    rw [tangentCoordChange_comp (prefChart _) i (prefChart _)
      ⟨⟨mem_chart_source E _, hx⟩, mem_chart_source E _⟩]
    exact tangentCoordChange_self _ (mem_chart_source E _) w'
  exact key w

/-- The Lie bracket of smooth vector fields is a smooth vector field. -/
def bracket (X Y : SmoothVectorField E M) : SmoothVectorField E M where
  toFun := lieBracket X Y
  isVectorField := isVectorField_lieBracket _ _
  smooth k := contMDiffMB_lieBracket X.isVectorField Y.isVectorField (X.smooth (k + 1))
    (Y.smooth (k + 1))

theorem localRep_bracket (X Y : SmoothVectorField E M) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) :
    localRep i (X.bracket Y) y = localBracket (localRep i X) (localRep i Y) y :=
  localRep_lieBracket X.isVectorField Y.isVectorField (X.smooth 1) (Y.smooth 1) i hy

end SmoothVectorField

/-! ### Insertion -/

namespace DifferentialForm

open SmoothVectorField

/-- `(i_X ω)ₓ(v₁, …, vₙ) = ωₓ(X(x), v₁, …, vₙ)`. -/
def interiorFun (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) (x : M)
    (v : Fin n → E) : F :=
  ω x (Fin.cons (X.vec x) v)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem formLocalRep_interiorFun (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1))
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : Fin n → E) :
    formLocalRep n i (interiorFun X ω) (y, v) = iLoc (X.rep i) (ω.localRep i) (y, v) := by
  simp only [formLocalRep, interiorFun, iLoc, localRep]
  congr 1
  funext k
  cases k using Fin.cases with
  | zero => exact (X.tangentCoordChange_localRep i hy).symm
  | succ k => rfl

/-- The insertion `i_X ω` of a smooth vector field into a form (Glöckner–Neeb,
Definition 3.6.15). -/
def interior (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) :
    DifferentialForm E M F n where
  toFun := interiorFun X ω
  alternating' x := by
    obtain ⟨A, hA⟩ := ω.alternating' x
    exact ⟨A.curryLeft (X.vec x), fun v ↦ by simp only [interiorFun, hA]; rfl⟩
  smooth' i k :=
    ContDiffMBOn.congr_of_isOpen (i.1.open_target.prod isOpen_univ)
      (fun p hp ↦ (formLocalRep_interiorFun X ω i hp.1 p.2).symm)
      (((ω.isLocalForm_localRep i).iLoc i.1.open_target (X.smoothMBOn_localRep i)).smooth k)

theorem interior_apply (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) (x : M)
    (v : Fin n → E) : interior X ω x v = ω x (Fin.cons (X.vec x) v) :=
  rfl

theorem localRep_interior (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1))
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : Fin n → E) :
    (interior X ω).localRep i (y, v) = iLoc (X.rep i) (ω.localRep i) (y, v) :=
  formLocalRep_interiorFun X ω i hy v

theorem interior_add (X : SmoothVectorField E M) (ω η : DifferentialForm E M F (n + 1)) :
    interior X (ω + η) = interior X ω + interior X η :=
  rfl

theorem interior_smul (X : SmoothVectorField E M) (c : ℝ) (ω : DifferentialForm E M F (n + 1)) :
    interior X (c • ω) = c • interior X ω :=
  rfl

theorem interior_zero (X : SmoothVectorField E M) :
    interior X (0 : DifferentialForm E M F (n + 1)) = 0 :=
  rfl

theorem interior_neg (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) :
    interior X (-ω) = -interior X ω :=
  rfl

theorem interior_sub (X : SmoothVectorField E M) (ω η : DifferentialForm E M F (n + 1)) :
    interior X (ω - η) = interior X ω - interior X η :=
  rfl

/-- `i_X i_X = 0`. -/
theorem interior_interior (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 2)) :
    interior X (interior X ω) = 0 := by
  ext x v
  obtain ⟨A, hA⟩ := ω.alternating' x
  simp only [interior_apply, zero_apply, hA]
  exact A.map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp [Fin.cons_one]) (by simp)

/-! ### The Lie derivative -/

/-- The Lie derivative `L_X ω`, defined by Cartan's formula `L_X = d ∘ i_X + i_X ∘ d`, with
`i_X = 0` on functions. Its local representatives are given by the local formula (3.35) of
Glöckner–Neeb (`localRep_lieDeriv`). -/
def lieDeriv (X : SmoothVectorField E M) : ∀ {n : ℕ}, DifferentialForm E M F n →
    DifferentialForm E M F n
  | 0, ω => interior X ω.d
  | _ + 1, ω => (interior X ω).d + interior X ω.d

theorem lieDeriv_zero (X : SmoothVectorField E M) (ω : DifferentialForm E M F 0) :
    lieDeriv X ω = interior X ω.d :=
  rfl

/-- **Cartan's formula** (Glöckner–Neeb, Proposition 3.6.16 (c)):
`L_X = d ∘ i_X + i_X ∘ d`. -/
theorem lieDeriv_succ (X : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) :
    lieDeriv X ω = (interior X ω).d + interior X ω.d :=
  rfl

/-- **The Lie derivative in charts** (Glöckner–Neeb, (3.35)): in every chart,
`(L_X ω)(y)(v) = ∂_{X(y)} ω(y)(v) + ∑ₖ ω(y)(v₁, …, dX(y) vₖ, …, vₙ)`. -/
theorem localRep_lieDeriv (X : SmoothVectorField E M) (ω : DifferentialForm E M F n)
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : Fin n → E) :
    (lieDeriv X ω).localRep i (y, v) = lieLoc (X.rep i) (ω.localRep i) (y, v) := by
  have hT := i.1.open_target
  cases n with
  | zero =>
    rw [lieDeriv_zero, localRep_interior X _ i hy,
      iLoc_congr (fun w ↦ ω.localRep_d i hy w) rfl v]
    exact iLoc_dLoc_zero _ _ _
  | succ n =>
    rw [lieDeriv_succ]
    change (interior X ω).d.localRep i (y, v) + (interior X ω.d).localRep i (y, v) = _
    rw [localRep_d _ i hy, localRep_interior X _ i hy,
      dLoc_congr hT (fun p hp ↦ localRep_interior X ω i hp.1 p.2) hy,
      iLoc_congr (fun w ↦ ω.localRep_d i hy w) rfl v]
    exact (ω.isLocalForm_localRep i).dLoc_iLoc_add hT (X.smoothMBOn_localRep i 1) hy v

theorem lieDeriv_add (X : SmoothVectorField E M) (ω η : DifferentialForm E M F n) :
    lieDeriv X (ω + η) = lieDeriv X ω + lieDeriv X η := by
  cases n with
  | zero => simp only [lieDeriv_zero, d_add, interior_add]
  | succ n =>
    simp only [lieDeriv_succ, d_add, interior_add]
    abel

theorem lieDeriv_smul (X : SmoothVectorField E M) (c : ℝ) (ω : DifferentialForm E M F n) :
    lieDeriv X (c • ω) = c • lieDeriv X ω := by
  cases n with
  | zero => simp only [lieDeriv_zero, d_smul, interior_smul]
  | succ n => simp only [lieDeriv_succ, d_smul, interior_smul, smul_add]

variable (F n) in
/-- The Lie derivative as a linear map on `Ωⁿ(M, F)`. -/
def lieDerivLinear (X : SmoothVectorField E M) :
    DifferentialForm E M F n →ₗ[ℝ] DifferentialForm E M F n where
  toFun := lieDeriv X
  map_add' := lieDeriv_add X
  map_smul' := lieDeriv_smul X

theorem lieDeriv_sub (X : SmoothVectorField E M) (ω η : DifferentialForm E M F n) :
    lieDeriv X (ω - η) = lieDeriv X ω - lieDeriv X η :=
  (lieDerivLinear F n X).map_sub ω η

/-! ### Proposition 3.6.16 -/

/-- `L_X ∘ d = d ∘ L_X` (Glöckner–Neeb, Proposition 3.6.16 (d)). -/
theorem lieDeriv_d (X : SmoothVectorField E M) (ω : DifferentialForm E M F n) :
    lieDeriv X ω.d = (lieDeriv X ω).d := by
  cases n with
  | zero =>
    rw [lieDeriv_succ, lieDeriv_zero, d_d_eq_zero, interior_zero, add_zero]
  | succ n =>
    rw [lieDeriv_succ, lieDeriv_succ, d_d_eq_zero, interior_zero, add_zero, d_add,
      d_d_eq_zero, zero_add]

/-- Closed forms: `L_X ω = d(i_X ω)` (Glöckner–Neeb, Proposition 3.6.16 (e)). -/
theorem IsClosed.lieDeriv_eq {X : SmoothVectorField E M} {ω : DifferentialForm E M F (n + 1)}
    (hω : ω.IsClosed) : lieDeriv X ω = (interior X ω).d := by
  rw [lieDeriv_succ, show ω.d = 0 from ext hω, interior_zero, add_zero]

/-- The Lie derivative of a closed form is exact (Glöckner–Neeb, Proposition 3.6.16 (e)). -/
theorem IsClosed.isExact_lieDeriv {X : SmoothVectorField E M}
    {ω : DifferentialForm E M F (n + 1)} (hω : ω.IsClosed) : (lieDeriv X ω).IsExact :=
  ⟨interior X ω, hω.lieDeriv_eq.symm⟩

/-- A closed function has vanishing Lie derivative. -/
theorem IsClosed.lieDeriv_eq_zero {X : SmoothVectorField E M} {ω : DifferentialForm E M F 0}
    (hω : ω.IsClosed) : lieDeriv X ω = 0 := by
  rw [lieDeriv_zero, show ω.d = 0 from ext hω, interior_zero]

omit [LocallyConvexSpace ℝ E] [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The value of a form at `x` is its local representative in the preferred chart at `x`. -/
theorem apply_eq_localRep (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    ω x v = ω.localRep (prefChart x) (chartAt E x x, v) :=
  (ω.localRep_prefChart x v).symm

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The local computation behind `[L_X, i_Y] = i_{[X, Y]}`. -/
theorem lieLoc_iLoc_sub {Xl Yl : E → E} {ω : E × (Fin (n + 1) → E) → F} {U : Set E}
    (hω : IsLocalForm (n + 1) ω U) (hU : IsOpen U) (hY : ContDiffMBOn 1 Yl U) {y : E}
    (hy : y ∈ U) (v : Fin n → E) :
    lieLoc Xl (iLoc Yl ω) (y, v) - iLoc Yl (lieLoc Xl ω) (y, v) =
      iLoc (localBracket Xl Yl) ω (y, v) := by
  obtain ⟨A, hA⟩ := hω.alternating y hy
  simp only [lieLoc, iLoc]
  rw [hω.dMB_iLoc hU hY hy v, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.update_cons_zero, Fin.cons_succ, ← Fin.cons_update, hA,
    localBracket]
  have h := A.map_update_sub (Fin.cons (Yl y) v) 0 (dMB Yl (y, Xl y)) (dMB Xl (y, Yl y))
  simp only [Fin.update_cons_zero] at h
  rw [h]
  abel

/-- `[L_X, i_Y] = i_{[X, Y]}` (Glöckner–Neeb, Proposition 3.6.16 (b)). -/
theorem lieDeriv_interior_sub (X Y : SmoothVectorField E M) (ω : DifferentialForm E M F (n + 1)) :
    lieDeriv X (interior Y ω) - interior Y (lieDeriv X ω) = interior (X.bracket Y) ω := by
  ext x v
  set i : atlas E M := prefChart x
  have hT := i.1.open_target
  have hy : chartAt E x x ∈ i.1.target := (chartAt E x).map_source (mem_chart_source E x)
  simp only [apply_eq_localRep _ x]
  change (lieDeriv X (interior Y ω)).localRep i (chartAt E x x, v) -
      (interior Y (lieDeriv X ω)).localRep i (chartAt E x x, v) =
      (interior (X.bracket Y) ω).localRep i (chartAt E x x, v)
  rw [localRep_lieDeriv X _ i hy, localRep_interior Y _ i hy, localRep_interior _ _ i hy,
    lieLoc_congr hT (fun p hp ↦ localRep_interior Y ω i hp.1 p.2) (fun _ _ ↦ rfl) hy,
    iLoc_congr (fun w ↦ localRep_lieDeriv X ω i hy w) rfl v,
    iLoc_congr (ω₂ := ω.localRep i) (fun _ ↦ rfl) (X.localRep_bracket Y i hy) v]
  exact lieLoc_iLoc_sub (ω.isLocalForm_localRep i) hT (Y.smoothMBOn_localRep i 1) hy v

/-- `[L_X, L_Y] = L_{[X, Y]}` (Glöckner–Neeb, Proposition 3.6.16 (a)): the Lie derivative is a
representation of the Lie algebra of smooth vector fields on `Ωⁿ(M, F)`. -/
theorem lieDeriv_lieDeriv_sub (X Y : SmoothVectorField E M) (ω : DifferentialForm E M F n) :
    lieDeriv X (lieDeriv Y ω) - lieDeriv Y (lieDeriv X ω) = lieDeriv (X.bracket Y) ω := by
  cases n with
  | zero =>
    have hb := lieDeriv_interior_sub X Y ω.d
    have e1 : lieDeriv Y (lieDeriv X ω) = interior Y (lieDeriv X ω.d) := by
      rw [lieDeriv_zero Y, ← lieDeriv_d]
    rw [e1, lieDeriv_zero Y ω, lieDeriv_zero (X.bracket Y) ω]
    exact hb
  | succ n =>
    have hb := lieDeriv_interior_sub X Y ω
    have hb' := lieDeriv_interior_sub X Y ω.d
    rw [lieDeriv_succ Y ω, lieDeriv_add, lieDeriv_d, lieDeriv_succ Y (lieDeriv X ω),
      ← lieDeriv_d X ω, lieDeriv_succ (X.bracket Y), ← hb, ← hb', d_sub]
    abel

end DifferentialForm


/-! ### Evaluation on vector fields: (3.29) and (3.35) -/

namespace SmoothVectorField

/-- The value of `X` at `x` is the value at `x` of its local representative in the preferred
chart. -/
theorem vec_eq_rep (X : SmoothVectorField E M) (x : M) :
    X.vec x = X.rep (prefChart x) (chartAt E x x) :=
  (localRep_chartAt X.isVectorField x).symm

/-- The derivative `X.g` of a vector-valued function along a vector field, computed in the
preferred chart. -/
def derivFun (X : SmoothVectorField E M) (g : M → F) (x : M) : F :=
  dMB (g ∘ (chartAt E x).symm) (chartAt E x x, X.vec x)

end SmoothVectorField

namespace DifferentialForm

open SmoothVectorField

/-- The function `ω(X₁, …, Xₙ) : M → F`. -/
def evalFields (ω : DifferentialForm E M F n) (X : Fin n → SmoothVectorField E M) (x : M) : F :=
  ω x fun k ↦ (X k).vec x

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem evalFields_eq_localRep (ω : DifferentialForm E M F n) (X : Fin n → SmoothVectorField E M)
    (i : atlas E M) {z : E} (hz : z ∈ i.1.target) :
    evalFields ω X (i.1.symm z) = ω.localRep i (z, fun k ↦ (X k).rep i z) := by
  simp only [evalFields, localRep, formLocalRep]
  congr 1
  funext k
  exact ((X k).tangentCoordChange_localRep i hz).symm

/-- The derivative of `ω(X₁, …, Xₙ)` along `Y`, in a chart: a partial derivative of the local
representative of `ω` and one term for each derivative `dXₖ · Y`. -/
theorem derivFun_evalFields (ω : DifferentialForm E M F n) (X : Fin n → SmoothVectorField E M)
    (Y : SmoothVectorField E M) (x : M) :
    Y.derivFun (evalFields ω X) x =
      dMB (fun z ↦ ω.localRep (prefChart x) (z, fun k ↦ (X k).rep (prefChart x) (chartAt E x x)))
          (chartAt E x x, Y.rep (prefChart x) (chartAt E x x)) +
        ∑ k, ω.localRep (prefChart x) (chartAt E x x,
          update (fun j ↦ (X j).rep (prefChart x) (chartAt E x x)) k
            (dMB ((X k).rep (prefChart x))
              (chartAt E x x, Y.rep (prefChart x) (chartAt E x x)))) := by
  set i : atlas E M := prefChart x
  have hT := i.1.open_target
  have hy : chartAt E x x ∈ i.1.target := (chartAt E x).map_source (mem_chart_source E x)
  have heq : evalFields ω X ∘ (chartAt E x).symm =ᶠ[𝓝 (chartAt E x x)]
      fun z ↦ ω.localRep i (z, fun k ↦ (X k).rep i z) :=
    eventuallyEq_of_mem (hT.mem_nhds hy) fun z hz ↦ evalFields_eq_localRep ω X i hz
  rw [derivFun, dMB_congr_of_eventuallyEq heq, Y.vec_eq_rep x]
  exact (ω.isLocalForm_localRep i).dMB_comp_vectors hT hy
    fun k ↦ ((X k).smoothMBOn_localRep i 1).2.1 _ hy _

/-- **The Lie derivative on vector fields** (Glöckner–Neeb, (3.35)):
`(L_Y ω)(X₁, …, Xₙ) = Y.ω(X₁, …, Xₙ) − ∑ⱼ ω(X₁, …, [Y, Xⱼ], …, Xₙ)`. -/
theorem lieDeriv_apply_fields (Y : SmoothVectorField E M) (ω : DifferentialForm E M F n)
    (X : Fin n → SmoothVectorField E M) (x : M) :
    lieDeriv Y ω x (fun k ↦ (X k).vec x) =
      Y.derivFun (evalFields ω X) x -
        ∑ k, ω x (update (fun j ↦ (X j).vec x) k ((Y.bracket (X k)).vec x)) := by
  classical
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  obtain ⟨A, hA⟩ := (ω.isLocalForm_localRep (prefChart x)).alternating _ hy
  have hvec : (fun k ↦ (X k).vec x) = fun k ↦ (X k).rep (prefChart x) (chartAt E x x) :=
    funext fun k ↦ (X k).vec_eq_rep x
  simp only [apply_eq_localRep _ x, hvec, (Y.bracket _).vec_eq_rep x]
  rw [derivFun_evalFields, localRep_lieDeriv Y ω _ hy, lieLoc]
  simp only [Y.localRep_bracket _ _ hy, localBracket, hA, A.map_update_sub,
    Finset.sum_sub_distrib]
  abel

/-- **The exterior derivative on vector fields** (Glöckner–Neeb, Proposition 3.6.7, (3.29)):
`dω(X₀, …, X_{n+1}) = ∑ᵢ (-1)ⁱ Xᵢ.ω(…, X̂ᵢ, …) − ∑_{i ≤ j} (-1)^{i+j} ω([Xᵢ, X_{j+1}], …)`,
where in the second sum `Xᵢ` and `X_{j+1}` are removed. (With the index `j + 1` in place of `j`,
the second sum is `+ ∑_{i < j} (-1)^{i+j} ω([Xᵢ, Xⱼ], …)` as in Glöckner–Neeb; we follow the
indexing of Mathlib's `extDeriv_apply_vectorField`.) -/
theorem d_apply_fields (ω : DifferentialForm E M F (n + 1))
    (X : Fin (n + 2) → SmoothVectorField E M) (x : M) :
    ω.d x (fun k ↦ (X k).vec x) =
      ∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) •
          (X i).derivFun (evalFields ω (X ∘ i.succAbove)) x -
        ∑ i : Fin (n + 1), ∑ j ∈ Finset.Ici i, (-1 : ℝ) ^ ((i : ℕ) + j) •
          ω x (Fin.cons (((X i.castSucc).bracket (X j.succ)).vec x)
            (j.removeNth (i.castSucc.removeNth fun k ↦ (X k).vec x))) := by
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  obtain ⟨A, hA⟩ := (ω.isLocalForm_localRep (prefChart x)).alternating _ hy
  have hvec : (fun k ↦ (X k).vec x) = fun k ↦ (X k).rep (prefChart x) (chartAt E x x) :=
    funext fun k ↦ (X k).vec_eq_rep x
  have key := sum_neg_one_pow_smul_sum_update_eq A
    (fun k ↦ (X k).rep (prefChart x) (chartAt E x x))
    fun a b ↦ dMB ((X b).rep (prefChart x)) (chartAt E x x, (X a).rep (prefChart x) (chartAt E x x))
  simp only [apply_eq_localRep _ x, hvec, ((X _).bracket _).vec_eq_rep x, derivFun_evalFields,
    comp_apply, (X _).localRep_bracket _ _ hy, localBracket, hA,
    smul_add, Finset.sum_add_distrib]
  rw [localRep_d _ _ hy, IsLocalForm.dLoc_apply, add_sub_assoc]
  convert (add_zero _).symm using 2
  all_goals first | rfl | (rw [sub_eq_zero]; exact key)

end DifferentialForm

/-! ### Related vector fields (Glöckner–Neeb, Exercise 3.6.6) -/

section Related

variable {E₀ : Type u} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N] {φ : N → M}

namespace DifferentialForm

open SmoothVectorField

/-- If `X` and `Y` are `φ`-related, the tangent map sends `X(x)` to `Y(φ x)`, in the preferred
charts. -/
theorem dMB_vec_of_isRelated {X : SmoothVectorField E₀ N} {Y : SmoothVectorField E M}
    (hXY : IsRelated φ X Y) (x : N) :
    dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm) (chartAt E₀ x x, X.vec x) = Y.vec (φ x) := by
  have key : ∀ p : TangentBundle E₀ N, p.proj = x →
      ((tangentMap E₀ E φ p).2 : E) =
        dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm) (chartAt E₀ x x, (p.2 : E₀)) := by
    rintro ⟨q, w⟩ rfl
    rfl
  exact (key (X x) (X.isVectorField x)).symm.trans
    (congrArg (fun p : TangentBundle E M ↦ (p.2 : E)) (hXY x))

/-- `φ*(i_Y ω) = i_X(φ*ω)` for `φ`-related vector fields (Glöckner–Neeb, Exercise 3.6.6). -/
theorem pullback_interior (hφ : SmoothMBM E₀ E φ) {X : SmoothVectorField E₀ N}
    {Y : SmoothVectorField E M} (hXY : IsRelated φ X Y) (ω : DifferentialForm E M F (n + 1)) :
    (interior Y ω).pullback hφ = interior X (ω.pullback hφ) := by
  ext x v
  change ω (φ x) (Fin.cons (Y.vec (φ x)) fun k ↦
      dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm) (chartAt E₀ x x, v k)) =
    ω (φ x) fun k ↦ dMB (chartAt E (φ x) ∘ φ ∘ (chartAt E₀ x).symm)
      (chartAt E₀ x x, (Fin.cons (X.vec x) v : Fin (n + 1) → E₀) k)
  congr 1
  funext k
  cases k using Fin.cases with
  | zero => exact (dMB_vec_of_isRelated hXY x).symm
  | succ k => rfl

/-- `φ*(L_Y ω) = L_X(φ*ω)` for `φ`-related vector fields (Glöckner–Neeb, Exercise 3.6.6). -/
theorem pullback_lieDeriv (hφ : SmoothMBM E₀ E φ) {X : SmoothVectorField E₀ N}
    {Y : SmoothVectorField E M} (hXY : IsRelated φ X Y) (ω : DifferentialForm E M F n) :
    (lieDeriv Y ω).pullback hφ = lieDeriv X (ω.pullback hφ) := by
  cases n with
  | zero => rw [lieDeriv_zero, lieDeriv_zero, pullback_interior hφ hXY, d_pullback]
  | succ n =>
    rw [lieDeriv_succ, lieDeriv_succ, pullback_add, ← d_pullback, pullback_interior hφ hXY,
      pullback_interior hφ hXY, d_pullback]

end DifferentialForm

end Related

end Manifold

end LocallyConvex.Manifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.DifferentialForm
import LocallyConvexManifolds.Derivation
import LocallyConvexAnalysis.Rules
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# The wedge product of differential forms

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, §3.6.

Let `β : E₁ × E₂ → E₃` be a continuous bilinear map between locally convex spaces. The wedge
product of `ω ∈ Ωᵖ(M, E₁)` and `η ∈ Ω^q(M, E₂)` is the form `ω ∧ η ∈ Ω^{p+q}(M, E₃)` given by
`(ω ∧ η)ₓ(v₁, …, v_{p+q}) = (p! q!)⁻¹ ∑_σ sgn(σ) β(ωₓ(v_{σ 1}, …, v_{σ p}), ηₓ(v_{σ(p+1)}, …))`
(Glöckner–Neeb, Definition 3.6.3, which follows Lang's conventions).

## Main definitions and results

* `wedgeFun`: the formula above, for arbitrary functions of the vectors;
* `wedgeAlt`: the wedge product of alternating maps, built from `MultilinearMap.alternatization`;
  its values are given by `wedgeFun` (`wedgeAlt_apply`), so `(ω ∧ η)ₓ` is alternating;
* `DifferentialForm.wedge`: the wedge product of forms; it is bilinear (`wedge_add_left`,
  `wedge_smul_left`, …), it is given for `p = q = 1` by
  `(ω ∧ η)(v₁, v₂) = β(ω v₁, η v₂) − β(ω v₂, η v₁)` (`wedge_apply_one_one`), and it commutes with
  pullbacks, `φ*(ω ∧ η) = φ*ω ∧ φ*η` (Glöckner–Neeb, (3.28); `pullback_wedge`);
* `DifferentialForm.smulFun`: the product `f ω` of a form by a smooth real function
  (Glöckner–Neeb, Remark 3.6.5), with the module identities over `C^∞(M, ℝ)`; it is the wedge
  product with the `0`-form `f` and the scalar multiplication (`wedge_ofFunction`).

Glöckner–Neeb form the product `f ∧ ω`, with `f` on the left. We put `f` on the right, so that
the degree is `p + 0`, which is definitionally `p`; for `0`-forms both orders give `f(x) ωₓ`.

No completeness of the spaces is assumed.
-/

open Set Function Equiv
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### The algebraic wedge product -/

section Algebra

variable {V E₁ E₂ E₃ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E₁] [Module ℝ E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [AddCommGroup E₃] [Module ℝ E₃]
  (β : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] E₃) {p q : ℕ}

/-- The wedge product of two functions of `p` and `q` vectors (Glöckner–Neeb,
Definition 3.6.3). -/
def wedgeFun (f : (Fin p → V) → E₁) (g : (Fin q → V) → E₂) (v : Fin (p + q) → V) : E₃ :=
  ((p.factorial : ℝ) * q.factorial)⁻¹ • ∑ σ : Perm (Fin (p + q)),
    ((Perm.sign σ : ℤ) : ℝ) •
      β (f fun i ↦ v (σ (Fin.castAdd q i))) (g fun j ↦ v (σ (Fin.natAdd p j)))

/-- The multilinear map `v ↦ β(A(v₁, …, v_p), B(v_{p+1}, …, v_{p+q}))`. -/
def wedgeMultilinear (A : MultilinearMap ℝ (fun _ : Fin p ↦ V) E₁)
    (B : MultilinearMap ℝ (fun _ : Fin q ↦ V) E₂) :
    MultilinearMap ℝ (fun _ : Fin (p + q) ↦ V) E₃ :=
  ((TensorProduct.lift β).compMultilinearMap (A.domCoprod B)).domDomCongr finSumFinEquiv

theorem wedgeMultilinear_apply (A : MultilinearMap ℝ (fun _ : Fin p ↦ V) E₁)
    (B : MultilinearMap ℝ (fun _ : Fin q ↦ V) E₂) (v : Fin (p + q) → V) :
    wedgeMultilinear β A B v =
      β (A fun i ↦ v (Fin.castAdd q i)) (B fun j ↦ v (Fin.natAdd p j)) := by
  simp [wedgeMultilinear]

/-- The wedge product of alternating maps. -/
def wedgeAlt (A : V [⋀^Fin p]→ₗ[ℝ] E₁) (B : V [⋀^Fin q]→ₗ[ℝ] E₂) :
    V [⋀^Fin (p + q)]→ₗ[ℝ] E₃ :=
  ((p.factorial : ℝ) * q.factorial)⁻¹ •
    MultilinearMap.alternatization (wedgeMultilinear β A.toMultilinearMap B.toMultilinearMap)

theorem wedgeAlt_apply (A : V [⋀^Fin p]→ₗ[ℝ] E₁) (B : V [⋀^Fin q]→ₗ[ℝ] E₂)
    (v : Fin (p + q) → V) : wedgeAlt β A B v = wedgeFun β A B v := by
  simp only [wedgeAlt, wedgeFun, smul_apply,
    MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply,
    wedgeMultilinear_apply, AlternatingMap.coe_multilinearMap, Units.smul_def,
    Int.cast_smul_eq_zsmul]

omit [AddCommGroup V] [Module ℝ V] in
theorem wedgeFun_congr {f f' : (Fin p → V) → E₁} {g g' : (Fin q → V) → E₂}
    (hf : ∀ w, f w = f' w) (hg : ∀ w, g w = g' w) (v : Fin (p + q) → V) :
    wedgeFun β f g v = wedgeFun β f' g' v := by
  simp only [wedgeFun, hf, hg]

omit [AddCommGroup V] [Module ℝ V] in
/-- For `p = q = 1`: `(f ∧ g)(v₁, v₂) = β(f v₁, g v₂) − β(f v₂, g v₁)` (Glöckner–Neeb,
Definition 3.6.3). -/
theorem wedgeFun_one_one (f : (Fin 1 → V) → E₁) (g : (Fin 1 → V) → E₂) (v : Fin 2 → V) :
    wedgeFun β f g v = β (f ![v 0]) (g ![v 1]) - β (f ![v 1]) (g ![v 0]) := by
  have huniv : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by decide
  have hne : (1 : Perm (Fin 2)) ≠ swap 0 1 := by decide
  have e0 : (fun _ : Fin 1 ↦ v 0) = ![v 0] := by ext i; fin_cases i; rfl
  have e1 : (fun _ : Fin 1 ↦ v 1) = ![v 1] := by ext i; fin_cases i; rfl
  simp only [wedgeFun, Nat.factorial_one, Nat.cast_one, mul_one, inv_one, one_smul]
  rw [huniv, Finset.sum_pair hne]
  simp only [Perm.sign_one, Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide), Units.val_one,
    Units.val_neg, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul, Perm.coe_one, id]
  have c0 : ∀ i : Fin 1, (Fin.castAdd 1 i : Fin 2) = 0 := fun i ↦ by fin_cases i; rfl
  have c1 : ∀ j : Fin 1, (Fin.natAdd 1 j : Fin 2) = 1 := fun j ↦ by fin_cases j; rfl
  simp only [c0, c1, swap_apply_left, swap_apply_right, e0, e1, sub_eq_add_neg]

end Algebra

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {E₁ E₂ E₃ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [AddCommGroup E₃] [Module ℝ E₃] [TopologicalSpace E₃] [IsTopologicalAddGroup E₃]
  [ContinuousSMul ℝ E₃] [LocallyConvexSpace ℝ E₃] [T2Space E₃]
  {β : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] E₃} {p q : ℕ}

/-! ### Smoothness in charts -/

/-- The precomposition of a function of `p` vectors with the inclusion `σ ∘ castAdd`, as a
continuous linear map on `E × E^{p+q}`. -/
def wedgeLeftCLM (σ : Perm (Fin (p + q))) : E × (Fin (p + q) → E) →L[ℝ] E × (Fin p → E) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.pi fun i ↦
    (ContinuousLinearMap.proj (σ (Fin.castAdd q i))) ∘L ContinuousLinearMap.snd ℝ _ _)

/-- The precomposition of a function of `q` vectors with `σ ∘ natAdd`. -/
def wedgeRightCLM (σ : Perm (Fin (p + q))) : E × (Fin (p + q) → E) →L[ℝ] E × (Fin q → E) :=
  (ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.pi fun j ↦
    (ContinuousLinearMap.proj (σ (Fin.natAdd p j))) ∘L ContinuousLinearMap.snd ℝ _ _)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] in
theorem ContDiffMBOn.comp_vectors {k ℓ m : ℕ} {f : E × (Fin ℓ → E) → E₁} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn k f (U ×ˢ univ))
    (L : E × (Fin m → E) →L[ℝ] E × (Fin ℓ → E)) (hL : ∀ r, (L r).1 = r.1) :
    ContDiffMBOn k (fun r ↦ f (L r)) (U ×ˢ univ) := by
  have h := hf.comp_clm L (hU.prod isOpen_univ)
  rwa [show L ⁻¹' (U ×ˢ univ) = U ×ˢ univ by ext r; simp [hL]] at h

variable (β) in
/-- The local wedge product of two families of functions of the vectors. -/
def wedgeLoc (ω : E × (Fin p → E) → E₁) (η : E × (Fin q → E) → E₂)
    (r : E × (Fin (p + q) → E)) : E₃ :=
  wedgeFun β (fun w ↦ ω (r.1, w)) (fun w ↦ η (r.1, w)) r.2

/-- The local wedge product of smooth functions is smooth. -/
theorem smoothMBOn_wedgeLoc (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2)
    {ω : E × (Fin p → E) → E₁} {η : E × (Fin q → E) → E₂} {U : Set E} (hU : IsOpen U)
    (hω : SmoothMBOn ω (U ×ˢ univ)) (hη : SmoothMBOn η (U ×ˢ univ)) :
    SmoothMBOn (wedgeLoc β ω η) (U ×ˢ univ) := by
  intro k
  have hT : IsOpen (U ×ˢ (univ : Set (Fin (p + q) → E))) := hU.prod isOpen_univ
  refine ContDiffMBOn.const_smul hT ?_ _
  refine ContDiffMBOn.sum _ hT fun σ _ ↦ ContDiffMBOn.const_smul hT ?_ _
  exact ContDiffMBOn.bilin β hβ hT
    (ContDiffMBOn.comp_vectors hU (hω k) (wedgeLeftCLM σ) fun _ ↦ rfl)
    (ContDiffMBOn.comp_vectors hU (hη k) (wedgeRightCLM σ) fun _ ↦ rfl)

/-! ### The wedge product of forms -/

namespace DifferentialForm

variable (β) in
/-- The wedge product `ω ∧ η ∈ Ω^{p+q}(M, E₃)` of `ω ∈ Ωᵖ(M, E₁)` and `η ∈ Ω^q(M, E₂)` with
respect to a continuous bilinear map `β : E₁ × E₂ → E₃` (Glöckner–Neeb, Definition 3.6.3). -/
def wedge (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2) (ω : DifferentialForm E M E₁ p)
    (η : DifferentialForm E M E₂ q) : DifferentialForm E M E₃ (p + q) where
  toFun x := wedgeFun β (ω x) (η x)
  alternating' x := by
    obtain ⟨A, hA⟩ := ω.alternating' x
    obtain ⟨B, hB⟩ := η.alternating' x
    exact ⟨wedgeAlt β A B, fun v ↦ by rw [wedgeAlt_apply]; exact wedgeFun_congr β hA hB v⟩
  smooth' i := smoothMBOn_wedgeLoc hβ i.1.open_target (ω.smooth' i) (η.smooth' i)

variable (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2)

omit [MBManifold E M] in
theorem wedge_apply (ω : DifferentialForm E M E₁ p) (η : DifferentialForm E M E₂ q) (x : M)
    (v : Fin (p + q) → E) : ω.wedge β hβ η x v = wedgeFun β (ω x) (η x) v :=
  rfl

omit [MBManifold E M] in
/-- In every chart, the local representative of `ω ∧ η` is the local wedge product of the local
representatives. -/
theorem localRep_wedge (ω : DifferentialForm E M E₁ p) (η : DifferentialForm E M E₂ q)
    (i : atlas E M) : (ω.wedge β hβ η).localRep i = wedgeLoc β (ω.localRep i) (η.localRep i) :=
  rfl

omit [MBManifold E M] in
/-- For `p = q = 1`: `(ω ∧ η)ₓ(v₁, v₂) = β(ωₓ v₁, ηₓ v₂) − β(ωₓ v₂, ηₓ v₁)` (Glöckner–Neeb,
Definition 3.6.3). -/
theorem wedge_apply_one_one (ω : DifferentialForm E M E₁ 1) (η : DifferentialForm E M E₂ 1)
    (x : M) (v : Fin 2 → E) :
    ω.wedge β hβ η x v = β (ω x ![v 0]) (η x ![v 1]) - β (ω x ![v 1]) (η x ![v 0]) :=
  wedgeFun_one_one β _ _ v

/-! #### Bilinearity -/

omit [MBManifold E M] in
theorem wedge_add_left (ω ω' : DifferentialForm E M E₁ p) (η : DifferentialForm E M E₂ q) :
    (ω + ω').wedge β hβ η = ω.wedge β hβ η + ω'.wedge β hβ η := by
  ext x v
  simp only [wedge_apply, add_apply, wedgeFun, map_add, LinearMap.add_apply, smul_add,
    Finset.sum_add_distrib]

omit [MBManifold E M] in
theorem wedge_add_right (ω : DifferentialForm E M E₁ p) (η η' : DifferentialForm E M E₂ q) :
    ω.wedge β hβ (η + η') = ω.wedge β hβ η + ω.wedge β hβ η' := by
  ext x v
  simp only [wedge_apply, add_apply, wedgeFun, map_add, smul_add, Finset.sum_add_distrib]

omit [MBManifold E M] in
theorem wedge_smul_left (c : ℝ) (ω : DifferentialForm E M E₁ p)
    (η : DifferentialForm E M E₂ q) : (c • ω).wedge β hβ η = c • ω.wedge β hβ η := by
  ext x v
  simp only [wedge_apply, smul_apply, wedgeFun, map_smul, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  module

omit [MBManifold E M] in
theorem wedge_smul_right (c : ℝ) (ω : DifferentialForm E M E₁ p)
    (η : DifferentialForm E M E₂ q) : ω.wedge β hβ (c • η) = c • ω.wedge β hβ η := by
  ext x v
  simp only [wedge_apply, smul_apply, wedgeFun, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  module

variable (M p q) in
/-- The wedge product as a bilinear map `Ωᵖ(M, E₁) × Ω^q(M, E₂) → Ω^{p+q}(M, E₃)`
(Glöckner–Neeb, Definition 3.6.3). -/
def wedgeBilinear :
    DifferentialForm E M E₁ p →ₗ[ℝ] DifferentialForm E M E₂ q →ₗ[ℝ]
      DifferentialForm E M E₃ (p + q) :=
  LinearMap.mk₂ ℝ (fun ω η ↦ ω.wedge β hβ η) (wedge_add_left hβ) (wedge_smul_left hβ)
    (wedge_add_right hβ) (wedge_smul_right hβ)

/-! #### Pullbacks -/

section Pullback

variable {E₀ : Type u} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N] {φ : N → M}

/-- `φ*(ω ∧ η) = φ*ω ∧ φ*η` (Glöckner–Neeb, (3.28)). -/
theorem pullback_wedge (hφ : SmoothMBM E₀ E φ) (ω : DifferentialForm E M E₁ p)
    (η : DifferentialForm E M E₂ q) :
    (ω.wedge β hβ η).pullback hφ = (ω.pullback hφ).wedge β hβ (η.pullback hφ) :=
  rfl

end Pullback

end DifferentialForm

/-! ### Products with smooth functions -/

namespace DifferentialForm

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

omit [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The directional derivative of the scalar multiplication `ℝ × F → F`. -/
theorem hasDirDerivAt_smul_pair (r s : ℝ × F) :
    HasDirDerivAt (fun r : ℝ × F ↦ r.1 • r.2) r s (r.1 • s.2 + s.1 • r.2) := by
  have key : ∀ t : ℝ, t ≠ 0 → t⁻¹ • ((r + t • s).1 • (r + t • s).2 - r.1 • r.2) =
      r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2) := by
    intro t ht
    have : (r + t • s).1 • (r + t • s).2 - r.1 • r.2 =
        t • (r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      module
    rw [this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hc : Continuous fun t : ℝ ↦ r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2) := by fun_prop
  have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_smul, add_zero] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  exact (key t ht).symm

/-- The scalar multiplication `ℝ × F → F` is `C^k` for every `k`. (The product rule
`ContDiffMBOn.bilin` needs both factors in the universe of the domain, which `ℝ` is not in
general.) -/
theorem contDiffMBOn_smul_pair (k : ℕ) : ContDiffMBOn k (fun r : ℝ × F ↦ r.1 • r.2) univ := by
  induction k with
  | zero => exact continuous_smul.continuousOn
  | succ k ih =>
    have heq : dMB (fun r : ℝ × F ↦ r.1 • r.2) = fun q ↦ q.1.1 • q.2.2 + q.2.1 • q.1.2 :=
      funext fun q ↦ (hasDirDerivAt_smul_pair q.1 q.2).dMB_eq
    refine ⟨continuous_smul.continuousOn, fun r _ s ↦ ?_, ?_⟩
    · rw [heq]; exact hasDirDerivAt_smul_pair r s
    · rw [heq, univ_prod_univ]
      let L₁ : (ℝ × F) × (ℝ × F) →L[ℝ] ℝ × F :=
        ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.fst ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.snd ℝ _ _))
      let L₂ : (ℝ × F) × (ℝ × F) →L[ℝ] ℝ × F :=
        ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.snd ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.fst ℝ _ _))
      have h₁ := ContDiffMBOn.comp_clm L₁ isOpen_univ ih
      have h₂ := ContDiffMBOn.comp_clm L₂ isOpen_univ ih
      rw [preimage_univ] at h₁ h₂
      exact h₁.add isOpen_univ h₂

/-- Product rule for a real function times a vector-valued function. -/
theorem ContDiffMBOn.smul_fun {k : ℕ} {E' : Type u} [AddCommGroup E'] [Module ℝ E']
    [TopologicalSpace E'] [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E']
    [LocallyConvexSpace ℝ E'] [T2Space E'] {f : E' → ℝ} {g : E' → F} {U : Set E'}
    (hU : IsOpen U) (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) :
    ContDiffMBOn k (fun x ↦ f x • g x) U :=
  ContDiffMBOn.comp (g := fun r : ℝ × F ↦ r.1 • r.2) hU isOpen_univ (contDiffMBOn_smul_pair k)
    (hf.prodMk hU hg) (mapsTo_univ _ _)

/-- The product `f ω` of a form by a smooth real function: `(f ω)ₓ = f(x) ωₓ` (Glöckner–Neeb,
Remark 3.6.5). -/
def smulFun (f : M → ℝ) (hf : ∀ k, IsCkFunction E k f) (ω : DifferentialForm E M F n) :
    DifferentialForm E M F n where
  toFun x v := f x • ω x v
  alternating' x := by
    obtain ⟨A, hA⟩ := ω.alternating' x
    exact ⟨f x • A, fun v ↦ by simp [hA]⟩
  smooth' i k := by
    have hT : IsOpen (i.1.target ×ˢ (univ : Set (Fin n → E))) :=
      i.1.open_target.prod isOpen_univ
    have h₁ := (hf k i).comp_clm (ContinuousLinearMap.fst ℝ E (Fin n → E)) i.1.open_target
    rw [show (ContinuousLinearMap.fst ℝ E (Fin n → E)) ⁻¹' i.1.target = i.1.target ×ˢ univ by
      ext; simp] at h₁
    exact ContDiffMBOn.smul_fun hT h₁ (ω.smooth' i k)

variable {f g : M → ℝ} (hf : ∀ k, IsCkFunction E k f) (hg : ∀ k, IsCkFunction E k g)

omit [MBManifold E M] in
@[simp] theorem smulFun_apply (ω : DifferentialForm E M F n) (x : M) (v : Fin n → E) :
    smulFun f hf ω x v = f x • ω x v :=
  rfl

omit [MBManifold E M] in
theorem smulFun_add (ω η : DifferentialForm E M F n) :
    smulFun f hf (ω + η) = smulFun f hf ω + smulFun f hf η := by
  ext x v; simp [smul_add]

omit [MBManifold E M] in
theorem smulFun_smul (c : ℝ) (ω : DifferentialForm E M F n) :
    smulFun f hf (c • ω) = c • smulFun f hf ω := by
  ext x v; simp [smul_comm c]

omit [MBManifold E M] in
theorem add_smulFun (hfg : ∀ k, IsCkFunction E k (f + g)) (ω : DifferentialForm E M F n) :
    smulFun (f + g) hfg ω = smulFun f hf ω + smulFun g hg ω := by
  ext x v; simp [add_smul]

omit [MBManifold E M] in
theorem mul_smulFun (hfg : ∀ k, IsCkFunction E k (f * g)) (ω : DifferentialForm E M F n) :
    smulFun (f * g) hfg ω = smulFun f hf (smulFun g hg ω) := by
  ext x v; simp [mul_smul]

omit [MBManifold E M] in
theorem one_smulFun (h1 : ∀ k, IsCkFunction E k (1 : M → ℝ)) (ω : DifferentialForm E M F n) :
    smulFun 1 h1 ω = ω := by
  ext x v; simp

end DifferentialForm

/-! ### `f ω` as a wedge product

Real-valued forms are only available when the model space lives in `Type`, since all spaces of
a differential form live in the universe of the model space. -/

namespace DifferentialForm

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

/-- The bilinear map `F × ℝ → F`, `(w, t) ↦ t w`. -/
abbrev smulRight : F →ₗ[ℝ] ℝ →ₗ[ℝ] F := (LinearMap.lsmul ℝ F).flip

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem continuous_smulRight : Continuous fun r : F × ℝ ↦ smulRight r.1 r.2 :=
  continuous_snd.smul continuous_fst

/-- The product `f ω` is the wedge product of `ω` with the `0`-form `f`, formed with the scalar
multiplication (Glöckner–Neeb, Remark 3.6.5). -/
theorem wedge_ofFunction {f : M → ℝ} (hf : SmoothMBM E ℝ f) (hf' : ∀ k, IsCkFunction E k f)
    (ω : DifferentialForm E M F n) :
    ω.wedge smulRight continuous_smulRight (ofFunction f hf) = smulFun f hf' ω := by
  ext x v
  obtain ⟨A, hA⟩ := ω.alternating' x
  have hperm : ∀ σ : Perm (Fin (n + 0)),
      ω x (fun i ↦ v (σ (Fin.castAdd 0 i))) = ((Perm.sign σ : ℤ) : ℝ) • ω x v := by
    intro σ
    rw [hA, hA, Int.cast_smul_eq_zsmul, ← Units.smul_def]
    exact A.map_perm v σ
  simp only [wedge_apply, wedgeFun, smulFun_apply, smulRight, LinearMap.flip_apply,
    LinearMap.lsmul_apply, ofFunction, hperm, smul_smul]
  have hsq : ∀ σ : Perm (Fin (n + 0)),
      ((Perm.sign σ : ℤ) : ℝ) * (f x * ((Perm.sign σ : ℤ) : ℝ)) = f x := fun σ ↦ by
    rw [mul_comm (f x), ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, Int.cast_one, one_mul]
  simp only [hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_zero, Nat.cast_one, mul_one, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hn : ((n.factorial : ℝ))⁻¹ * ((n + 0).factorial * f x) = f x :=
    inv_mul_cancel_left₀ (by positivity) _
  rw [hn]

end DifferentialForm

end LocallyConvex.Manifolds

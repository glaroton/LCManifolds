/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Wedge

/-!
# The Leibniz rule for the wedge product

For `ω ∈ Ωᵖ(M, E₁)`, `η ∈ Ω^q(M, E₂)` and a continuous bilinear map `β : E₁ × E₂ → E₃`,
`d(ω ∧ η) = dω ∧ η + (-1)ᵖ ω ∧ dη`
(`DifferentialForm.d_wedge_apply`). The degrees of `dω ∧ η` and `d(ω ∧ η)` are `(p + 1) + q` and
`(p + q) + 1`, which are not definitionally equal; the first term is evaluated at `v ∘ Fin.cast`,
and `DifferentialForm.d_wedge` states the identity of forms with the reindexing
`DifferentialForm.castDeg`.

Glöckner–Neeb do not state this rule in §3.6. The proof is local: by the product rule, the
derivative of `z ↦ ω(z) ∧ η(z)` in a direction `u` is `∂ᵤω ∧ η + ω ∧ ∂ᵤη`, and the identity
reduces to two algebraic identities between alternating maps (`alternatizeUncurryFin_wedge_left`,
`alternatizeUncurryFin_wedge_right`), the classical computation behind the Leibniz rule.

## The algebraic identities

We write `altF f v = ∑_σ sign(σ) f(v ∘ σ)` for the (unnormalized) alternation of an arbitrary
function `f` of `k` vectors. Everything follows from:

* `altF_comp_perm`: `altF f (v ∘ σ) = sign(σ) altF f v`;
* `altF_precomp`: `altF (f ∘ (· ∘ e)) = altF f ∘ (· ∘ e)` for a bijection `e`;
* `altF_alternating`: `altF A = k! A` for an alternating map `A`;
* `altF_sum_perm`: alternating a partial alternation `w ↦ ∑_τ sign(τ) g(w ∘ τ̃)` over a subgroup
  of permutations with `sign τ̃ = sign τ` gives `a! · altF g`.

The wedge product is `(p! q!)⁻¹ altF` of `w ↦ β(f(w₁, …, w_p), g(w_{p+1}, …))`, and
`alternatizeUncurryFin L = (n!)⁻¹ altF (w ↦ L(w₀)(w₁, …, wₙ))`
(`alternatizeUncurryFin_eq_altF`).
-/

open Set Function Equiv
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

/-! ### Alternation of functions -/

section AltF

variable {V N : Type*} [AddCommGroup N] [Module ℝ N]

/-- The unnormalized alternation `altF f v = ∑_σ sign(σ) f(v ∘ σ)` of a function of `k`
vectors. -/
def altF (k : ℕ) (f : (Fin k → V) → N) (v : Fin k → V) : N :=
  ∑ σ : Perm (Fin k), ((Perm.sign σ : ℤ) : ℝ) • f (v ∘ σ)

theorem sign_mul_sign_self {k : ℕ} (σ : Perm (Fin k)) :
    ((Perm.sign σ : ℤ) : ℝ) * ((Perm.sign σ : ℤ) : ℝ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- `altF f (v ∘ σ) = sign(σ) altF f v`. -/
theorem altF_comp_perm {k : ℕ} (f : (Fin k → V) → N) (v : Fin k → V) (σ : Perm (Fin k)) :
    altF k f (v ∘ σ) = ((Perm.sign σ : ℤ) : ℝ) • altF k f v := by
  simp only [altF, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ ↦ ?_
  simp only [Equiv.coe_mulLeft, Perm.sign_mul, Units.val_mul, Int.cast_mul, Perm.coe_mul]
  rw [← mul_assoc, sign_mul_sign_self, one_mul]
  rfl

/-- Alternation commutes with reindexing along a bijection `e : Fin a ≃ Fin b`. -/
theorem altF_precomp {a b : ℕ} (e : Fin a ≃ Fin b) (f : (Fin a → V) → N) (v : Fin b → V) :
    altF b (fun w ↦ f (w ∘ e)) v = altF a f (v ∘ e) := by
  simp only [altF]
  refine Fintype.sum_equiv (e.permCongr.symm) _ _ fun τ ↦ ?_
  rw [show Perm.sign (e.permCongr.symm τ) = Perm.sign τ from by
    rw [Equiv.permCongr_symm]; exact Perm.sign_permCongr _ _]
  congr 2
  funext i
  simp [Equiv.permCongr_symm, Equiv.permCongr_apply]

/-- The alternation of an alternating map `A` of `k` vectors is `k! A`. -/
theorem altF_alternating [AddCommGroup V] [Module ℝ V] {k : ℕ} (A : V [⋀^Fin k]→ₗ[ℝ] N)
    (v : Fin k → V) :
    altF k A v = (k.factorial : ℝ) • A v := by
  simp only [altF]
  have h : ∀ σ : Perm (Fin k), ((Perm.sign σ : ℤ) : ℝ) • A (v ∘ σ) = A v := fun σ ↦ by
    rw [A.map_perm v σ, Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ,
      smul_smul, sign_mul_sign_self, one_smul]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]

theorem altF_add {k : ℕ} (f g : (Fin k → V) → N) (v : Fin k → V) :
    altF k (fun w ↦ f w + g w) v = altF k f v + altF k g v := by
  simp only [altF, smul_add, Finset.sum_add_distrib]

theorem altF_smul {k : ℕ} (c : ℝ) (f : (Fin k → V) → N) (v : Fin k → V) :
    altF k (fun w ↦ c • f w) v = c • altF k f v := by
  simp only [altF, Finset.smul_sum, smul_comm c]

theorem altF_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin k → V) → N) (v : Fin k → V) :
    altF k (fun w ↦ ∑ i ∈ s, f i w) v = ∑ i ∈ s, altF k (f i) v := by
  simp only [altF, Finset.smul_sum]
  exact Finset.sum_comm

/-- **Alternating a partial alternation.** If `τ ↦ τ̃` maps the permutations of `Fin a` to
permutations of `Fin k` with `sign τ̃ = sign τ`, then alternating `w ↦ ∑_τ sign(τ) g(w ∘ τ̃)`
gives `a! altF g`. -/
theorem altF_sum_perm {a k : ℕ} (emb : Perm (Fin a) → Perm (Fin k))
    (hemb : ∀ τ, Perm.sign (emb τ) = Perm.sign τ) (g : (Fin k → V) → N) (v : Fin k → V) :
    altF k (fun w ↦ ∑ τ : Perm (Fin a), ((Perm.sign τ : ℤ) : ℝ) • g (w ∘ emb τ)) v =
      (a.factorial : ℝ) • altF k g v := by
  rw [altF_sum]
  have h : ∀ τ : Perm (Fin a),
      altF k (fun w ↦ ((Perm.sign τ : ℤ) : ℝ) • g (w ∘ emb τ)) v = altF k g v := fun τ ↦ by
    rw [altF_smul, altF_precomp (emb τ) g v, altF_comp_perm, hemb, smul_smul,
      sign_mul_sign_self, one_smul]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]

end AltF

/-! ### Uncurrying and the wedge product as alternations -/

section Uncurry

variable {V N : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup N] [Module ℝ N] {n : ℕ}

/-- The terms of `alternatizeUncurryFin` are reindexings of `w ↦ L(w₀)(w₁, …, wₙ)` by the
cycles `(0 1 … i)`. -/
theorem alternatizeUncurryFin_apply_eq_sum (L : V →ₗ[ℝ] V [⋀^Fin n]→ₗ[ℝ] N)
    (v : Fin (n + 1) → V) :
    AlternatingMap.alternatizeUncurryFin L v =
      ∑ i : Fin (n + 1), ((Perm.sign i.cycleRange.symm : ℤ) : ℝ) •
        (fun w : Fin (n + 1) → V ↦ L (w 0) (Fin.tail w)) (v ∘ i.cycleRange.symm) := by
  rw [AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 : (v ∘ i.cycleRange.symm) 0 = v i := by simp
  have h2 : Fin.tail (v ∘ i.cycleRange.symm) = i.removeNth v := by
    funext j; simp [Fin.tail, Fin.removeNth]
  simp only [h1, h2, Perm.sign_symm, Fin.sign_cycleRange, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp

/-- `alternatizeUncurryFin L = (n!)⁻¹ altF (w ↦ L(w₀)(w₁, …, wₙ))`. -/
theorem alternatizeUncurryFin_eq_altF (L : V →ₗ[ℝ] V [⋀^Fin n]→ₗ[ℝ] N) (v : Fin (n + 1) → V) :
    AlternatingMap.alternatizeUncurryFin L v =
      (n.factorial : ℝ)⁻¹ • altF (n + 1) (fun w ↦ L (w 0) (Fin.tail w)) v := by
  set A := AlternatingMap.alternatizeUncurryFin L
  have key : ((n + 1).factorial : ℝ) • A v =
      ((n + 1 : ℕ) : ℝ) • altF (n + 1) (fun w ↦ L (w 0) (Fin.tail w)) v := by
    rw [← altF_alternating A v]
    have hA : (A : (Fin (n + 1) → V) → N) = fun w ↦ ∑ i : Fin (n + 1),
        ((Perm.sign i.cycleRange.symm : ℤ) : ℝ) •
          (fun w : Fin (n + 1) → V ↦ L (w 0) (Fin.tail w)) (w ∘ i.cycleRange.symm) :=
      funext (alternatizeUncurryFin_apply_eq_sum L)
    rw [hA, altF_sum]
    have h : ∀ i : Fin (n + 1), altF (n + 1) (fun w ↦ ((Perm.sign i.cycleRange.symm : ℤ) : ℝ) •
        (fun w : Fin (n + 1) → V ↦ L (w 0) (Fin.tail w)) (w ∘ i.cycleRange.symm)) v =
        altF (n + 1) (fun w ↦ L (w 0) (Fin.tail w)) v := fun i ↦ by
      rw [altF_smul,
        altF_precomp i.cycleRange.symm (fun w : Fin (n + 1) → V ↦ L (w 0) (Fin.tail w)),
        altF_comp_perm, smul_smul, sign_mul_sign_self, one_smul]
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : ((n + 1).factorial : ℝ) = (n + 1 : ℕ) * n.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  rw [hf, mul_smul] at key
  have key' := smul_right_injective N hn key
  rw [← key', smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

omit [AddCommGroup V] [Module ℝ V] in
/-- **Alternating an alternation in the last `n` variables**: if `g u` is a function of `n`
vectors for each `u`, then alternating `w ↦ altF (g w₀) (w₁, …, wₙ)` gives
`n! altF (w ↦ g(w₀)(w₁, …, wₙ))`. -/
theorem altF_altF_tail (g : V → (Fin n → V) → N) (v : Fin (n + 1) → V) :
    altF (n + 1) (fun w ↦ altF n (g (w 0)) (Fin.tail w)) v =
      (n.factorial : ℝ) • altF (n + 1) (fun w ↦ g (w 0) (Fin.tail w)) v := by
  rw [← altF_sum_perm (fun τ ↦ Perm.decomposeFin.symm (0, τ)) (fun τ ↦ by simp)]
  rfl

end Uncurry

/-! ### The two algebraic identities -/

section WedgeAlgebra

variable {V E₁ E₂ E₃ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E₁] [Module ℝ E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [AddCommGroup E₃] [Module ℝ E₃]
  (β : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] E₃) {p q : ℕ}

omit [AddCommGroup V] [Module ℝ V] in
theorem wedgeFun_eq_altF (f : (Fin p → V) → E₁) (g : (Fin q → V) → E₂) (v : Fin (p + q) → V) :
    wedgeFun β f g v = ((p.factorial : ℝ) * q.factorial)⁻¹ •
      altF (p + q) (fun w ↦ β (f fun i ↦ w (Fin.castAdd q i)) (g fun j ↦ w (Fin.natAdd p j))) v :=
  rfl

/-- The wedge product with a fixed right factor, as a linear map. -/
def wedgeAltLeft (B : V [⋀^Fin q]→ₗ[ℝ] E₂) :
    (V [⋀^Fin p]→ₗ[ℝ] E₁) →ₗ[ℝ] V [⋀^Fin (p + q)]→ₗ[ℝ] E₃ where
  toFun A := wedgeAlt β A B
  map_add' A A' := by
    ext v
    simp only [add_apply, wedgeAlt_apply, wedgeFun, map_add, LinearMap.add_apply,
      smul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext v
    simp only [smul_apply, wedgeAlt_apply, wedgeFun, map_smul, LinearMap.smul_apply,
      RingHom.id_apply, Finset.smul_sum, smul_comm c]

/-- The wedge product with a fixed left factor, as a linear map. -/
def wedgeAltRight (A : V [⋀^Fin p]→ₗ[ℝ] E₁) :
    (V [⋀^Fin q]→ₗ[ℝ] E₂) →ₗ[ℝ] V [⋀^Fin (p + q)]→ₗ[ℝ] E₃ where
  toFun B := wedgeAlt β A B
  map_add' B B' := by
    ext v
    simp only [add_apply, wedgeAlt_apply, wedgeFun, map_add, smul_add,
      Finset.sum_add_distrib]
  map_smul' c B := by
    ext v
    simp only [smul_apply, wedgeAlt_apply, wedgeFun, map_smul, RingHom.id_apply,
      Finset.smul_sum, smul_comm c]

/-- The permutation `τ ⊕ 1` of `Fin (a + b)`. -/
def permLeft {a b : ℕ} (τ : Perm (Fin a)) : Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr (Perm.sumCongr τ 1)

/-- The permutation `1 ⊕ τ` of `Fin (a + b)`. -/
def permRight {a b : ℕ} (τ : Perm (Fin b)) : Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr (Perm.sumCongr 1 τ)

theorem sign_permLeft {a b : ℕ} (τ : Perm (Fin a)) :
    Perm.sign (permLeft (b := b) τ) = Perm.sign τ := by
  simp [permLeft, Perm.sign_permCongr, Perm.sign_sumCongr]

theorem sign_permRight {a b : ℕ} (τ : Perm (Fin b)) :
    Perm.sign (permRight (a := a) τ) = Perm.sign τ := by
  simp [permRight, Perm.sign_permCongr, Perm.sign_sumCongr]

@[simp] theorem permLeft_castAdd {a b : ℕ} (τ : Perm (Fin a)) (i : Fin a) :
    permLeft (b := b) τ (Fin.castAdd b i) = Fin.castAdd b (τ i) := by
  simp [permLeft, Equiv.permCongr_apply]

@[simp] theorem permLeft_natAdd {a b : ℕ} (τ : Perm (Fin a)) (j : Fin b) :
    permLeft (b := b) τ (Fin.natAdd a j) = Fin.natAdd a j := by
  simp [permLeft, Equiv.permCongr_apply]

@[simp] theorem permRight_castAdd {a b : ℕ} (τ : Perm (Fin b)) (i : Fin a) :
    permRight (a := a) τ (Fin.castAdd b i) = Fin.castAdd b i := by
  simp [permRight, Equiv.permCongr_apply]

@[simp] theorem permRight_natAdd {a b : ℕ} (τ : Perm (Fin b)) (j : Fin b) :
    permRight (a := a) τ (Fin.natAdd a j) = Fin.natAdd a (τ j) := by
  simp [permRight, Equiv.permCongr_apply]

/-- **The first term of the Leibniz rule**, algebraically:
`∑ᵢ (-1)ⁱ (L(vᵢ) ∧ B)(v₀, …, v̂ᵢ, …) = (alternatizeUncurryFin L ∧ B)(v)`, the right hand side
of degree `(p + 1) + q`, evaluated at `v ∘ Fin.cast`. -/
theorem alternatizeUncurryFin_wedge_left (L : V →ₗ[ℝ] V [⋀^Fin p]→ₗ[ℝ] E₁)
    (B : V [⋀^Fin q]→ₗ[ℝ] E₂) (v : Fin (p + q + 1) → V) :
    AlternatingMap.alternatizeUncurryFin (wedgeAltLeft β B ∘ₗ L) v =
      wedgeFun β (AlternatingMap.alternatizeUncurryFin L) B
        (v ∘ Fin.cast (by omega : p + 1 + q = p + q + 1)) := by
  set h : p + 1 + q = p + q + 1 := by omega
  -- the common function of `p + q + 1` vectors
  set UL : (Fin (p + 1) → V) → E₁ := fun x ↦ L (x 0) (Fin.tail x)
  set Y' : (Fin (p + 1 + q) → V) → E₃ := fun w ↦
    β (UL fun i ↦ w (Fin.castAdd q i)) (B fun j ↦ w (Fin.natAdd (p + 1) j))
  set G : V → (Fin (p + q) → V) → E₃ := fun u w' ↦
    β (L u fun i ↦ w' (Fin.castAdd q i)) (B fun j ↦ w' (Fin.natAdd p j))
  -- left hand side
  have hL : AlternatingMap.alternatizeUncurryFin (wedgeAltLeft β B ∘ₗ L) v =
      ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + q + 1) (fun w ↦ Y' (w ∘ finCongr h)) v := by
    rw [alternatizeUncurryFin_eq_altF]
    have e1 : (fun w : Fin (p + q + 1) → V ↦ (wedgeAltLeft β B ∘ₗ L) (w 0) (Fin.tail w)) =
        fun w ↦ ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + q) (G (w 0)) (Fin.tail w) := by
      funext w
      simp only [LinearMap.coe_comp, comp_apply, wedgeAltLeft, LinearMap.coe_mk, AddHom.coe_mk,
        wedgeAlt_apply, wedgeFun_eq_altF]
      rfl
    rw [e1, altF_smul, altF_altF_tail G, smul_smul, smul_smul]
    have e2 : (fun w : Fin (p + q + 1) → V ↦ G (w 0) (Fin.tail w)) =
        fun w ↦ Y' (w ∘ finCongr h) := by
      funext w
      simp only [G, Y', UL, comp_apply, finCongr_apply, Fin.tail]
      congr 3
      funext j
      exact congrArg w (Fin.ext (by simp; omega))
    rw [e2]
    congr 1
    field_simp
  -- right hand side
  have hR : wedgeFun β (AlternatingMap.alternatizeUncurryFin L) B (v ∘ Fin.cast h) =
      ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + 1 + q) Y' (v ∘ finCongr h) := by
    rw [wedgeFun_eq_altF]
    have e1 : (fun w : Fin (p + 1 + q) → V ↦ β (AlternatingMap.alternatizeUncurryFin L
        fun i ↦ w (Fin.castAdd q i)) (B fun j ↦ w (Fin.natAdd (p + 1) j))) =
        fun w ↦ (p.factorial : ℝ)⁻¹ • ∑ τ : Perm (Fin (p + 1)),
          ((Perm.sign τ : ℤ) : ℝ) • Y' (w ∘ permLeft τ) := by
      funext w
      rw [alternatizeUncurryFin_eq_altF, map_smul, LinearMap.smul_apply, altF, map_sum,
        LinearMap.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      rw [map_smul, LinearMap.smul_apply]
      simp only [Y', comp_apply, permLeft_castAdd, permLeft_natAdd]
      rfl
    rw [e1, altF_smul, altF_sum_perm permLeft sign_permLeft, smul_smul, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hL, hR, altF_precomp]

/-- **The second term of the Leibniz rule**, algebraically:
`∑ᵢ (-1)ⁱ (A ∧ L(vᵢ))(v₀, …, v̂ᵢ, …) = (-1)ᵖ (A ∧ alternatizeUncurryFin L)(v)`. -/
theorem alternatizeUncurryFin_wedge_right (A : V [⋀^Fin p]→ₗ[ℝ] E₁)
    (L : V →ₗ[ℝ] V [⋀^Fin q]→ₗ[ℝ] E₂) (v : Fin (p + q + 1) → V) :
    AlternatingMap.alternatizeUncurryFin (wedgeAltRight β A ∘ₗ L) v =
      (-1 : ℝ) ^ p • wedgeFun β A (AlternatingMap.alternatizeUncurryFin L) v := by
  set UL : (Fin (q + 1) → V) → E₂ := fun x ↦ L (x 0) (Fin.tail x)
  set Z' : (Fin (p + (q + 1)) → V) → E₃ := fun w ↦
    β (A fun i ↦ w (Fin.castAdd (q + 1) i)) (UL fun j ↦ w (Fin.natAdd p j))
  set ρ : Perm (Fin (p + q + 1)) := Fin.cycleRange ⟨p, by omega⟩
  set G : V → (Fin (p + q) → V) → E₃ := fun u w' ↦
    β (A fun i ↦ w' (Fin.castAdd q i)) (L u fun j ↦ w' (Fin.natAdd p j))
  -- left hand side
  have hL : AlternatingMap.alternatizeUncurryFin (wedgeAltRight β A ∘ₗ L) v =
      ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + q + 1) (fun w ↦ Z' (w ∘ ρ)) v := by
    rw [alternatizeUncurryFin_eq_altF]
    have e1 : (fun w : Fin (p + q + 1) → V ↦ (wedgeAltRight β A ∘ₗ L) (w 0) (Fin.tail w)) =
        fun w ↦ ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + q) (G (w 0)) (Fin.tail w) := by
      funext w
      simp only [LinearMap.coe_comp, comp_apply, wedgeAltRight, LinearMap.coe_mk, AddHom.coe_mk,
        wedgeAlt_apply, wedgeFun_eq_altF]
      rfl
    rw [e1, altF_smul, altF_altF_tail G, smul_smul, smul_smul]
    have e2 : (fun w : Fin (p + q + 1) → V ↦ G (w 0) (Fin.tail w)) = fun w ↦ Z' (w ∘ ρ) := by
      funext w
      simp only [G, Z', UL, comp_apply, Fin.tail]
      congr 3
      · funext i; congr 1; apply Fin.ext
        rw [Fin.coe_cycleRange_of_lt (by simp [Fin.lt_def])]; simp
      · congr 1
        rw [Fin.cycleRange_of_eq (Fin.ext (by simp))]
      · funext j; congr 1; apply Fin.ext
        rw [Fin.cycleRange_of_gt (by simp [Fin.lt_def])]; simp; omega
    rw [e2]
    congr 1
    field_simp
  have hR : wedgeFun β A (AlternatingMap.alternatizeUncurryFin L) v =
      ((p.factorial : ℝ) * q.factorial)⁻¹ • altF (p + (q + 1)) Z' v := by
    rw [wedgeFun_eq_altF]
    have e1 : (fun w : Fin (p + (q + 1)) → V ↦ β (A fun i ↦ w (Fin.castAdd (q + 1) i))
        (AlternatingMap.alternatizeUncurryFin L fun j ↦ w (Fin.natAdd p j))) =
        fun w ↦ (q.factorial : ℝ)⁻¹ • ∑ τ : Perm (Fin (q + 1)),
          ((Perm.sign τ : ℤ) : ℝ) • Z' (w ∘ permRight τ) := by
      funext w
      rw [alternatizeUncurryFin_eq_altF, map_smul, altF, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      rw [map_smul]
      simp only [Z', comp_apply, permRight_castAdd, permRight_natAdd]
      rfl
    rw [e1, altF_smul, altF_sum_perm permRight sign_permRight, smul_smul, smul_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hL, hR, altF_precomp ρ, altF_comp_perm, smul_smul, smul_smul]
  congr 1
  rw [Fin.sign_cycleRange]
  simp [mul_comm]

end WedgeAlgebra

/-! ### The Leibniz rule in charts -/

universe u v

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E₁ E₂ E₃ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [AddCommGroup E₃] [Module ℝ E₃] [TopologicalSpace E₃] [IsTopologicalAddGroup E₃]
  [ContinuousSMul ℝ E₃] [LocallyConvexSpace ℝ E₃] [T2Space E₃]
  {β : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] E₃} {p q : ℕ}

section Local

variable {ω : E × (Fin p → E) → E₁} {η : E × (Fin q → E) → E₂} {U : Set E}

/-- **The product rule for the local wedge product**: the derivative of
`z ↦ (ω(z) ∧ η(z))(w)` at `y` in the direction `u` is `(∂ᵤω ∧ η)(w) + (ω ∧ ∂ᵤη)(w)`. -/
theorem IsLocalForm.dMB_wedgeLoc (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2) (hU : IsOpen U)
    (hω : IsLocalForm p ω U) (hη : IsLocalForm q η U) {y : E} (hy : y ∈ U)
    {L : E →ₗ[ℝ] E [⋀^Fin p]→ₗ[ℝ] E₁} (hL : ∀ u w, dMB (fun z ↦ ω (z, w)) (y, u) = L u w)
    {L' : E →ₗ[ℝ] E [⋀^Fin q]→ₗ[ℝ] E₂} (hL' : ∀ u w, dMB (fun z ↦ η (z, w)) (y, u) = L' u w)
    (u : E) (w : Fin (p + q) → E) :
    dMB (fun z ↦ wedgeLoc β ω η (z, w)) (y, u) =
      wedgeFun β (L u) (fun w' ↦ η (y, w')) w + wedgeFun β (fun w' ↦ ω (y, w')) (L' u) w := by
  have hterm : ∀ (a : Fin p → E) (b : Fin q → E),
      HasDirDerivAt (fun z ↦ β (ω (z, a)) (η (z, b))) y u
        (β (L u a) (η (y, b)) + β (ω (y, a)) (L' u b)) := fun a b ↦ by
    have hf := hω.smooth_slice hU a 1
    have hg := hη.smooth_slice hU b 1
    have h := (ContDiffMBOn.bilin β hβ hU hf hg).2.1 y hy u
    rw [ContDiffMBOn.dMB_bilin β hβ hU hf hg hy u, hL, hL'] at h
    rwa [add_comm]
  have hd : HasDirDerivAt (fun z ↦ ((p.factorial : ℝ) * q.factorial)⁻¹ •
      ∑ σ : Perm (Fin (p + q)), ((Perm.sign σ : ℤ) : ℝ) •
        β (ω (z, fun i ↦ w (σ (Fin.castAdd q i)))) (η (z, fun j ↦ w (σ (Fin.natAdd p j))))) y u
      (((p.factorial : ℝ) * q.factorial)⁻¹ • ∑ σ : Perm (Fin (p + q)),
        ((Perm.sign σ : ℤ) : ℝ) •
          (β (L u fun i ↦ w (σ (Fin.castAdd q i))) (η (y, fun j ↦ w (σ (Fin.natAdd p j)))) +
            β (ω (y, fun i ↦ w (σ (Fin.castAdd q i)))) (L' u fun j ↦ w (σ (Fin.natAdd p j))))) :=
    (HasDirDerivAt.sum _ fun σ _ ↦ (hterm _ _).const_smul _).const_smul _
  have hfun : (fun z ↦ wedgeLoc β ω η (z, w)) = fun z ↦ ((p.factorial : ℝ) * q.factorial)⁻¹ •
      ∑ σ : Perm (Fin (p + q)), ((Perm.sign σ : ℤ) : ℝ) •
        β (ω (z, fun i ↦ w (σ (Fin.castAdd q i)))) (η (z, fun j ↦ w (σ (Fin.natAdd p j)))) :=
    rfl
  rw [hfun, hd.dMB_eq]
  simp only [wedgeFun, smul_add, Finset.sum_add_distrib]

/-- **The Leibniz rule for local forms**:
`d(ω ∧ η)(y)(v) = (dω ∧ η)(y)(v) + (-1)ᵖ (ω ∧ dη)(y)(v)`, the first term evaluated at
`v ∘ Fin.cast` since it has degree `(p + 1) + q`. -/
theorem IsLocalForm.dLoc_wedgeLoc (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2) (hU : IsOpen U)
    (hω : IsLocalForm p ω U) (hη : IsLocalForm q η U) {y : E} (hy : y ∈ U)
    (v : Fin (p + q + 1) → E) :
    LocallyConvex.Manifolds.dLoc (wedgeLoc β ω η) (y, v) =
      wedgeLoc β (LocallyConvex.Manifolds.dLoc ω) η
          (y, v ∘ Fin.cast (by omega : p + 1 + q = p + q + 1)) +
        (-1 : ℝ) ^ p • wedgeLoc β ω (LocallyConvex.Manifolds.dLoc η) (y, v) := by
  obtain ⟨L, hL⟩ := hω.exists_partial hU hy
  obtain ⟨L', hL'⟩ := hη.exists_partial hU hy
  obtain ⟨A, hA⟩ := hω.alternating y hy
  obtain ⟨B, hB⟩ := hη.alternating y hy
  have hω' : ∀ w,
      LocallyConvex.Manifolds.dLoc ω (y, w) = AlternatingMap.alternatizeUncurryFin L w :=
    IsLocalForm.dLoc_eq_alternatizeUncurryFin hL
  have hη' : ∀ w,
      LocallyConvex.Manifolds.dLoc η (y, w) = AlternatingMap.alternatizeUncurryFin L' w :=
    IsLocalForm.dLoc_eq_alternatizeUncurryFin hL'
  have hlhs : LocallyConvex.Manifolds.dLoc (wedgeLoc β ω η) (y, v) =
      AlternatingMap.alternatizeUncurryFin (wedgeAltLeft β B ∘ₗ L) v +
        AlternatingMap.alternatizeUncurryFin (wedgeAltRight β A ∘ₗ L') v := by
    rw [IsLocalForm.dLoc_apply]
    simp only [AlternatingMap.alternatizeUncurryFin_apply, ← Finset.sum_add_distrib,
      ← neg_one_pow_smul_eq_zsmul, ← smul_add]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IsLocalForm.dMB_wedgeLoc hβ hU hω hη hy hL hL']
    simp only [LinearMap.coe_comp, comp_apply, wedgeAltLeft, wedgeAltRight, LinearMap.coe_mk,
      AddHom.coe_mk, wedgeAlt_apply]
    rw [wedgeFun_congr β (fun _ ↦ rfl) hB, wedgeFun_congr β hA (fun _ ↦ rfl)]
  rw [hlhs, alternatizeUncurryFin_wedge_left, alternatizeUncurryFin_wedge_right]
  simp only [wedgeLoc]
  rw [wedgeFun_congr β hω' hB, wedgeFun_congr β hA hη']

end Local

/-! ### The Leibniz rule for forms -/

variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace DifferentialForm

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- A form of degree `m`, seen as a form of degree `n = m` (to identify, e.g., the degrees
`(p + 1) + q` and `(p + q) + 1`). -/
def castDeg {m n : ℕ} (h : m = n) (ω : DifferentialForm E M F m) : DifferentialForm E M F n :=
  h ▸ ω

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
@[simp] theorem castDeg_apply {m n : ℕ} (h : m = n) (ω : DifferentialForm E M F m) (x : M)
    (v : Fin n → E) : castDeg h ω x v = ω x (v ∘ Fin.cast h) := by
  subst h
  rfl

variable (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2)

/-- **The Leibniz rule**, pointwise:
`d(ω ∧ η)ₓ(v) = (dω ∧ η)ₓ(v) + (-1)ᵖ (ω ∧ dη)ₓ(v)`, where `dω ∧ η` has degree `(p + 1) + q`
and is evaluated at `v ∘ Fin.cast`. -/
theorem d_wedge_apply (ω : DifferentialForm E M E₁ p) (η : DifferentialForm E M E₂ q) (x : M)
    (v : Fin (p + q + 1) → E) :
    (ω.wedge β hβ η).d x v =
      ω.d.wedge β hβ η x (v ∘ Fin.cast (by omega : p + 1 + q = p + q + 1)) +
        (-1 : ℝ) ^ p • ω.wedge β hβ η.d x v := by
  set j : atlas E M := prefChart x
  have hy : chartAt E x x ∈ j.1.target := (chartAt E x).map_source (mem_chart_source E x)
  rw [d_apply, localRep_wedge, IsLocalForm.dLoc_wedgeLoc hβ j.1.open_target
    (ω.isLocalForm_localRep j) (η.isLocalForm_localRep j) hy]
  simp only [wedge_apply, wedgeLoc]
  congr 1
  · refine wedgeFun_congr β (fun w ↦ rfl) (fun w ↦ ?_) _
    exact η.localRep_prefChart x w
  · congr 1
    refine wedgeFun_congr β (fun w ↦ ?_) (fun w ↦ rfl) _
    exact ω.localRep_prefChart x w

/-- **The Leibniz rule** `d(ω ∧ η) = dω ∧ η + (-1)ᵖ ω ∧ dη`, with the degree `(p + 1) + q` of
`dω ∧ η` identified with `(p + q) + 1`. -/
theorem d_wedge (ω : DifferentialForm E M E₁ p) (η : DifferentialForm E M E₂ q) :
    (ω.wedge β hβ η).d =
      castDeg (E := E) (M := M) (by omega) (ω.d.wedge β hβ η) +
        (-1 : ℝ) ^ p • ω.wedge β hβ η.d := by
  ext x v
  rw [d_wedge_apply, add_apply, smul_apply, castDeg_apply]

end DifferentialForm

end LocallyConvex.Manifolds

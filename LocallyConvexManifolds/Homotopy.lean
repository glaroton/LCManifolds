/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.IntegralExistence
import LocallyConvexAnalysis.FundamentalTheorem
import LocallyConvexManifolds.DeRham
import LocallyConvexManifolds.LieDerivative
import LocallyConvexManifolds.Product
import LocallyConvexManifolds.Wedge
import LocallyConvexAnalysis.MBFrechet

/-!
# The homotopy formula and the Poincaré Lemma

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Lemma 3.6.25 (Homotopy
Lemma), Theorem 3.6.28 (Poincaré Lemma) and Corollary 3.6.29.

For a form `ω` of degree `k + 1` on `ℝ × M` with values in a **Mackey complete** space `F`, the
*fiber integral* `I(ω) ∈ Ωᵏ(M, F)` is
`I(ω)ₓ(v₁, …, vₖ) = ∫₀¹ ω_{(t, x)}(∂ₜ, v₁, …, vₖ) dt`,
and the *homotopy formula* (Glöckner–Neeb, (3.40)) is `d I(ω) + I(dω) = i₁*ω - i₀*ω`, where
`iₜ(x) = (t, x)`. Mackey completeness is what makes the weak integrals of the smooth curves
`t ↦ ω_{(t, x)}(…)` exist (`LocallyConvex.Analysis.ContDiffMBOn.exists_hasWeakIntegral`).

## Differences with Glöckner–Neeb

* Homotopies are smooth maps `ℝ × M → N`, instead of `[0, 1] × M → N`: we have no manifolds
  with boundary. A homotopy on `[0, 1] × M` in the sense of Glöckner–Neeb can be precomposed
  with a smooth map `ℝ → [0, 1]` which is `0` near `(-∞, 0]` and `1` near `[1, ∞)`.
* Glöckner–Neeb prove the homotopy formula through Cartan's formula on vector fields. We prove it
  in charts: differentiating under the integral sign
  (`LocallyConvex.Analysis.ContDiffMBOn.dMB_weakIntegral_of_mackey`), the terms of `d I(ω)` cancel
  those of `I(dω)` with a derivative in a direction of `M`, and what remains is
  `∫₀¹ ∂ₜ ω_{(t, x)}(v) dt = ω_{(1, x)}(v) - ω_{(0, x)}(v)`.

## Main results

* `fibLoc`, `IsLocalForm.isLocalForm_fibLoc`, `IsLocalForm.dLoc_fibLoc_add`: the local fiber
  integral and the local homotopy formula;
* `DifferentialForm.fibInt`: the fiber integral `I : Ωᵏ⁺¹(ℝ × M, F) → Ωᵏ(M, F)`, and
  `DifferentialForm.d_fibInt_add`: the homotopy formula `d I(ω) + I(dω) = i₁*ω - i₀*ω`
  (Glöckner–Neeb, (3.40)), with `fibInt_d_zero` in degree `0`;
* `deRhamMap_homotopy`: **the Homotopy Lemma** (Glöckner–Neeb, Lemma 3.6.25): smoothly homotopic
  maps induce the same maps in de Rham cohomology;
* `DifferentialForm.IsClosed.isExact_of_smoothlyContractible`,
  `deRham_subsingleton_of_smoothlyContractible`: **the Poincaré Lemma** (Glöckner–Neeb,
  Theorem 3.6.28);
* `smoothlyContractible_of_starConvex`, `DifferentialForm.IsClosed.isExact_of_starConvex`: open
  star-shaped subsets of `E` (Glöckner–Neeb, Corollary 3.6.29).

To form `ℝ × M` for `M` modeled on `E : Type u`, the product of manifolds
(`LocallyConvexManifolds.Product`) allows model spaces in different universes.
-/

open Set Function Filter
open LocallyConvex.Analysis
open scoped Topology

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

/-! ### Preliminaries -/

section Prelim

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {E' : Type*} [AddCommGroup E'] [Module ℝ E']

omit [TopologicalSpace E] in
/-- Differentials along affine maps: `d(g ∘ (L + c))(x, v) = dg(L x + c, L v)`. -/
theorem dMB_comp_affine (g : E' → F) (L : E →ₗ[ℝ] E') (c : E') (x v : E) :
    dMB (fun x ↦ g (L x + c)) (x, v) = dMB g (L x + c, L v) := by
  unfold dMB
  congr 1
  funext t
  simp [map_add, map_smul, add_right_comm]

end Prelim

section Integrals

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {a b : ℝ}

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Finite sums of weak integrals of continuous curves. -/
theorem hasWeakIntegral_finsetSum {ι : Type*} (s : Finset ι) {γ : ι → ℝ → F} {y : ι → F}
    (hc : ∀ i ∈ s, ContinuousOn (γ i) (uIcc a b)) (hy : ∀ i ∈ s, HasWeakIntegral (γ i) a b (y i)) :
    HasWeakIntegral (fun t ↦ ∑ i ∈ s, γ i t) a b (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using hasWeakIntegral_const (0 : F) a b
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact HasWeakIntegral.add (hc i (Finset.mem_insert_self i s))
      (continuousOn_finsetSum _ fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
      (hy i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hy j (Finset.mem_insert_of_mem hj)))

end Integrals

/-! ### The local fiber integral -/

section Local

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {k : ℕ}

/-- The vectors `(0, v₁), …, (0, vₖ)` of `ℝ × E`. -/
def inclVec (v : Fin k → E) : Fin k → ℝ × E := fun j ↦ (0, v j)

omit [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem inclVec_update [DecidableEq (Fin k)] (v : Fin k → E) (i : Fin k) (a : E) :
    inclVec (update v i a) = update (inclVec v) i (0, a) := by
  funext j
  by_cases h : j = i
  · subst h; simp [inclVec]
  · simp [inclVec, update_of_ne h]

/-- The point `(t, y)` and the vectors `(1, 0), (0, v₁), …, (0, vₖ)` at which the integrand of
the fiber integral is evaluated, as a function of `((y, v), t)`. -/
def fibPt (p : (E × (Fin k → E)) × ℝ) : (ℝ × E) × (Fin (k + 1) → ℝ × E) :=
  ((p.2, p.1.1), Fin.cons (1, 0) (inclVec p.1.2))

/-- The linear part of `fibPt`. -/
def fibLin : (E × (Fin k → E)) × ℝ →L[ℝ] (ℝ × E) × (Fin (k + 1) → ℝ × E) :=
  ((ContinuousLinearMap.snd ℝ _ ℝ).prod
      ((ContinuousLinearMap.fst ℝ E _).comp (ContinuousLinearMap.fst ℝ _ ℝ))).prod
    (ContinuousLinearMap.pi fun m ↦ Fin.cases 0 (fun j ↦ (ContinuousLinearMap.inr ℝ ℝ E).comp
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℝ E _).comp
        (ContinuousLinearMap.fst ℝ _ ℝ)))) m)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem fibPt_eq (p : (E × (Fin k → E)) × ℝ) :
    fibPt p = fibLin p + ((0, 0), Fin.cons (1, 0) 0) := by
  refine Prod.ext (by simp [fibPt, fibLin]) ?_
  funext m
  cases m using Fin.cases <;> simp [fibPt, fibLin, inclVec]

theorem smoothMBOn_fibPt : SmoothMBOn (fibPt (E := E) (k := k)) univ := fun n ↦ by
  have h := (fibLin (E := E) (k := k)).contDiffMBOn n univ |>.add isOpen_univ
    (contDiffMBOn_const n (((0 : ℝ), (0 : E)), (Fin.cons ((1 : ℝ), (0 : E)) 0 :
      Fin (k + 1) → ℝ × E)) univ)
  exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun p _ ↦ (fibPt_eq p).symm) h

/-- The local fiber integral `I(Ω)(y)(v) = ∫₀¹ Ω(t, y)((1, 0), (0, v₁), …, (0, vₖ)) dt`. -/
def fibLoc (Ω : (ℝ × E) × (Fin (k + 1) → ℝ × E) → F) (p : E × (Fin k → E)) : F :=
  weakIntegral (fun t ↦ Ω (fibPt (p, t))) 0 1

/-- The restriction of a local form to the slice `{t} × E`. -/
def sliceLoc (t : ℝ) (Ω : (ℝ × E) × (Fin k → ℝ × E) → F) (p : E × (Fin k → E)) : F :=
  Ω ((t, p.1), inclVec p.2)

variable {V : Set E}

/-- Curves `t ↦ G(t, y)` of a `C^n` map `G` on `ℝ × V` are `C^n`. -/
theorem contDiffMBOn_curve {n : ℕ} {G : ℝ × E → F} (hV : IsOpen V)
    (hG : ContDiffMBOn n G (univ ×ˢ V)) {y : E} (hy : y ∈ V) :
    ContDiffMBOn n (fun t : ℝ ↦ G (t, y)) univ := by
  have hA : ContDiffMBOn n (fun t : ℝ ↦ (t, y)) univ := by
    have h := ((ContinuousLinearMap.inl ℝ ℝ E).contDiffMBOn n univ).add isOpen_univ
      (contDiffMBOn_const n ((0 : ℝ), y) univ)
    exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun t _ ↦ by simp) h
  exact hG.comp isOpen_univ (isOpen_univ.prod hV) hA fun t _ ↦ ⟨mem_univ _, hy⟩

/-- The curves along which we integrate have weak integrals in Mackey complete spaces. -/
theorem hasWeakIntegral_curve [MackeyComplete F] {G : ℝ × E → F} (hV : IsOpen V)
    (hG : ContDiffMBOn 1 G (univ ×ˢ V)) {y : E} (hy : y ∈ V) :
    HasWeakIntegral (fun t ↦ G (t, y)) 0 1 (weakIntegral (fun t ↦ G (t, y)) 0 1) :=
  hasWeakIntegral_weakIntegral
    ((contDiffMBOn_curve hV hG hy).exists_hasWeakIntegral (subset_univ _))

theorem continuousOn_curve {G : ℝ × E → F} {n : ℕ} (hV : IsOpen V)
    (hG : ContDiffMBOn n G (univ ×ˢ V)) {y : E} (hy : y ∈ V) (s : Set ℝ) :
    ContinuousOn (fun t ↦ G (t, y)) s :=
  (contDiffMBOn_curve hV hG hy).continuousOn.mono (subset_univ _)

/-- Directional derivatives of a smooth map in a fixed direction are smooth. -/
theorem SmoothMBOn.dMB_dir {G : ℝ × E → F} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hG : SmoothMBOn G U) (d : ℝ × E) : SmoothMBOn (fun z ↦ dMB G (z, d)) U := fun n ↦ by
  have h := ((hG (n + 1)).2.2).comp (hU) (hU.prod isOpen_univ)
    (ContDiffMBOn.prodMk hU (smoothMBOn_id U n) (contDiffMBOn_const n d U))
    fun z hz ↦ ⟨hz, mem_univ _⟩
  exact h

variable {Ω : (ℝ × E) × (Fin (k + 1) → ℝ × E) → F}

theorem IsLocalForm.smoothMBOn_comp_fibPt (hΩ : IsLocalForm (k + 1) Ω (univ ×ˢ V))
    (hV : IsOpen V) :
    SmoothMBOn (fun q : (E × (Fin k → E)) × ℝ ↦ Ω (fibPt q)) ((V ×ˢ univ) ×ˢ univ) := fun n ↦
  (hΩ.smooth n).comp ((hV.prod isOpen_univ).prod isOpen_univ)
    ((isOpen_univ.prod hV).prod isOpen_univ) ((smoothMBOn_fibPt n).mono (subset_univ _))
    fun _ hq ↦ ⟨⟨mem_univ _, hq.1.1⟩, mem_univ _⟩

variable [MackeyComplete F]

/-- **The fiber integral of a local form is a local form.** -/
theorem IsLocalForm.isLocalForm_fibLoc (hΩ : IsLocalForm (k + 1) Ω (univ ×ˢ V)) (hV : IsOpen V) :
    IsLocalForm k (LocallyConvex.Manifolds.fibLoc Ω) V := by
  classical
  have hW : IsOpen (univ ×ˢ V : Set (ℝ × E)) := isOpen_univ.prod hV
  refine ⟨?_, fun y hy ↦ ?_⟩
  · have h := SmoothMBOn.smoothMBOn_weakIntegral isOpen_univ zero_le_one (subset_univ _)
      (hV.prod isOpen_univ) (hΩ.smoothMBOn_comp_fibPt hV)
    exact h
  -- the curves `t ↦ Ω((t, y), W)`
  have hS : ∀ W, ContDiffMBOn 1 (fun z ↦ Ω (z, W)) (univ ×ˢ V) := fun W ↦
    hΩ.smooth_slice hW W 1
  have hI : ∀ W, HasWeakIntegral (fun t ↦ Ω ((t, y), W)) 0 1
      (weakIntegral (fun t ↦ Ω ((t, y), W)) 0 1) := fun W ↦
    hasWeakIntegral_curve (G := fun z ↦ Ω (z, W)) hV (hS W) hy
  have hc : ∀ W, ContinuousOn (fun t ↦ Ω ((t, y), W)) (uIcc 0 1) := fun W ↦
    continuousOn_curve (G := fun z ↦ Ω (z, W)) hV (hS W) hy _
  have hmem : ∀ t : ℝ, (t, y) ∈ (univ ×ˢ V : Set (ℝ × E)) := fun t ↦ ⟨mem_univ _, hy⟩
  have hupd : ∀ (v : Fin k → E) (i : Fin k) (a : E),
      (Fin.cons (1, 0) (inclVec (update v i a)) : Fin (k + 1) → ℝ × E) =
        update (Fin.cons (1, 0) (inclVec v)) i.succ (0, a) := fun v i a ↦ by
    rw [inclVec_update, Fin.cons_update]
  refine ⟨{ toFun := fun v ↦ LocallyConvex.Manifolds.fibLoc Ω (y, v)
            map_update_add' := fun v i a b ↦ ?_
            map_update_smul' := fun v i c a ↦ ?_
            map_eq_zero_of_eq' := fun v i j hv hij ↦ ?_ }, fun v ↦ rfl⟩
  · rename_i inst
    obtain rfl : inst = instDecidableEqFin k := Subsingleton.elim _ _
    show weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec (update v i (a + b))))) 0 1 =
      weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec (update v i a)))) 0 1 +
        weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec (update v i b)))) 0 1
    rw [hupd v i (a + b), hupd v i a, hupd v i b]
    have e : ∀ t : ℝ, Ω ((t, y), update (Fin.cons (1, 0) (inclVec v)) i.succ (0, a + b)) =
        Ω ((t, y), update (Fin.cons (1, 0) (inclVec v)) i.succ (0, a)) +
          Ω ((t, y), update (Fin.cons (1, 0) (inclVec v)) i.succ (0, b)) := fun t ↦ by
      rw [show ((0 : ℝ), a + b) = ((0 : ℝ), a) + (0, b) by simp]
      exact hΩ.map_update_add (hmem t) _ _ _ _
    simp only [e]
    exact ((hI _).add (hc _) (hc _) (hI _)).weakIntegral_eq
  · rename_i inst
    obtain rfl : inst = instDecidableEqFin k := Subsingleton.elim _ _
    show weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec (update v i (c • a))))) 0 1 =
      c • weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec (update v i a)))) 0 1
    rw [hupd v i (c • a), hupd v i a]
    have e : ∀ t : ℝ, Ω ((t, y), update (Fin.cons (1, 0) (inclVec v)) i.succ (0, c • a)) =
        c • Ω ((t, y), update (Fin.cons (1, 0) (inclVec v)) i.succ (0, a)) := fun t ↦ by
      rw [show ((0 : ℝ), c • a) = c • ((0 : ℝ), a) by simp]
      exact hΩ.map_update_smul (hmem t) _ _ _ _
    simp only [e]
    exact ((hI _).const_smul c).weakIntegral_eq
  · have e : ∀ t : ℝ, Ω ((t, y), Fin.cons (1, 0) (inclVec v)) = 0 := fun t ↦
      hΩ.map_eq_zero_of_eq (hmem t) (i := i.succ) (j := j.succ)
        (by simp [inclVec, hv]) (Fin.succ_injective _ |>.ne hij)
    show weakIntegral (fun t ↦ Ω ((t, y), Fin.cons (1, 0) (inclVec v))) 0 1 = 0
    simp only [e]
    simpa using (hasWeakIntegral_const (0 : F) 0 1).weakIntegral_eq

end Local

/-! ### The local homotopy formula -/

section LocalHomotopy

variable {E F : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {k : ℕ} {V : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem fibLin_dir (u : E) :
    fibLin (E := E) (k := k) ((u, 0), 0) = ((0, u), 0) := by
  refine Prod.ext (by simp [fibLin]) ?_
  funext m
  cases m using Fin.cases <;> simp [fibLin]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- The integrand of `I(dΩ)`: the term with the derivative in the `t`-direction, minus the terms
with derivatives in directions of `E`. -/
theorem dLoc_fibPt (Ω : (ℝ × E) × (Fin (k + 1) → ℝ × E) → F) (t : ℝ) (y : E)
    (v : Fin (k + 1) → E) :
    dLoc Ω ((t, y), Fin.cons (1, 0) (inclVec v)) =
      dMB (fun z ↦ Ω (z, inclVec v)) ((t, y), (1, 0)) -
        ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) •
          dMB (fun z ↦ Ω (z, Fin.cons (1, 0) (inclVec (j.removeNth v)))) ((t, y), (0, v j)) := by
  rw [IsLocalForm.dLoc_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
    Fin.val_succ, Fin.removeNth_succ_cons, Fin.cons_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- The integrand of `I(dΩ)` in degree `0`. -/
theorem dLoc_fibPt_zero (Ω : (ℝ × E) × (Fin 0 → ℝ × E) → F) (t : ℝ) (y : E)
    (v : Fin 0 → E) :
    dLoc Ω ((t, y), Fin.cons (1, 0) (inclVec v)) =
      dMB (fun z ↦ Ω (z, inclVec v)) ((t, y), (1, 0)) := by
  rw [IsLocalForm.dLoc_apply, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
  congr 2

variable [MackeyComplete F]

/-- **Differentiation of the fiber integral**: `∂ᵤ I(Ω)(y)(w) = ∫₀¹ ∂_{(0, u)} Ω(t, y)(…) dt`. -/
theorem IsLocalForm.dMB_fibLoc {Ω : (ℝ × E) × (Fin (k + 1) → ℝ × E) → F}
    (hΩ : IsLocalForm (k + 1) Ω (univ ×ˢ V)) (hV : IsOpen V) {y : E} (hy : y ∈ V)
    (w : Fin k → E) (u : E) :
    dMB (fun z ↦ fibLoc Ω (z, w)) (y, u) =
      weakIntegral (fun t ↦ dMB (fun z ↦ Ω (z, Fin.cons (1, 0) (inclVec w))) ((t, y), (0, u)))
        0 1 := by
  rw [← dMB_slice]
  have hf := hΩ.smoothMBOn_comp_fibPt hV 2
  show dMB (fun p ↦ weakIntegral (fun t ↦ Ω (fibPt (p, t))) 0 1) ((y, w), (u, 0)) = _
  have h := ContDiffMBOn.dMB_weakIntegral_of_mackey isOpen_univ zero_le_one (subset_univ _)
    (hV.prod isOpen_univ) hf (x := (y, w)) ⟨hy, mem_univ _⟩ (u, 0)
  refine h.trans ?_
  congr 1
  funext t
  have e : (fun q : (E × (Fin k → E)) × ℝ ↦ Ω (fibPt q)) =
      fun q ↦ Ω ((fibLin : (E × (Fin k → E)) × ℝ →L[ℝ] _) q + ((0, 0), Fin.cons (1, 0) 0)) :=
    funext fun q ↦ by rw [fibPt_eq]
  have hA := dMB_comp_affine Ω (fibLin : (E × (Fin k → E)) × ℝ →L[ℝ] _).toLinearMap
    ((0, 0), Fin.cons (1, 0) 0) ((y, w), t) ((u, 0), 0)
  simp only [ContinuousLinearMap.coe_coe] at hA
  rw [e, hA, ← fibPt_eq, fibLin_dir, dMB_slice]
  rfl

/-- **The local homotopy formula** (Glöckner–Neeb, (3.40), in a chart):
`d I(Ω) + I(dΩ) = Ω|_{t = 1} - Ω|_{t = 0}` for a local form `Ω` of degree `k + 1` on `ℝ × V`. -/
theorem IsLocalForm.dLoc_fibLoc_add {Ω : (ℝ × E) × (Fin (k + 1) → ℝ × E) → F}
    (hΩ : IsLocalForm (k + 1) Ω (univ ×ˢ V)) (hV : IsOpen V) {y : E} (hy : y ∈ V)
    (v : Fin (k + 1) → E) :
    LocallyConvex.Manifolds.dLoc (fibLoc Ω) (y, v) +
        fibLoc (LocallyConvex.Manifolds.dLoc Ω) (y, v) =
      sliceLoc 1 Ω (y, v) - sliceLoc 0 Ω (y, v) := by
  have hW : IsOpen (univ ×ˢ V : Set (ℝ × E)) := isOpen_univ.prod hV
  have hS : ∀ W, SmoothMBOn (fun z ↦ Ω (z, W)) (univ ×ˢ V) := fun W ↦ hΩ.smooth_slice hW W
  -- the curves `Dⱼ`
  set D : Fin (k + 1) → ℝ → F := fun j t ↦
    dMB (fun z ↦ Ω (z, Fin.cons (1, 0) (inclVec (j.removeNth v)))) ((t, y), (0, v j))
  have hDs : ∀ j, SmoothMBOn (fun z ↦ dMB (fun z ↦ Ω (z, Fin.cons (1, 0)
      (inclVec (j.removeNth v)))) (z, (0, v j))) (univ ×ˢ V) := fun j ↦
    SmoothMBOn.dMB_dir hW (hS _) _
  have hDI : ∀ j, HasWeakIntegral (D j) 0 1 (weakIntegral (D j) 0 1) := fun j ↦
    hasWeakIntegral_curve hV (hDs j 1) hy
  have hDc : ∀ j (s : Set ℝ), ContinuousOn (D j) s := fun j s ↦
    continuousOn_curve hV (hDs j 0) hy s
  -- the curve `Dₑ` and the fundamental theorem of calculus
  set γ : ℝ → F := fun t ↦ Ω ((t, y), inclVec v)
  set De : ℝ → F := fun t ↦ dMB (fun z ↦ Ω (z, inclVec v)) ((t, y), (1, 0))
  have hDec : ∀ s : Set ℝ, ContinuousOn De s := fun s ↦
    continuousOn_curve hV (SmoothMBOn.dMB_dir hW (hS _) _ 0) hy s
  have hγ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDirDerivAt γ t 1 (De t) := fun t _ ↦
    ((hS (inclVec v) 1).2.1 (t, y) ⟨mem_univ _, hy⟩ (1, 0)).congr fun s ↦ by simp [γ]
  have hFTC : HasWeakIntegral De 0 1 (γ 1 - γ 0) := hasWeakIntegral_sub_of_hasDirDerivAt hγ (hDec _)
  -- the two sides
  have h1 : LocallyConvex.Manifolds.dLoc (fibLoc Ω) (y, v) =
      ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) • weakIntegral (D j) 0 1 := by
    rw [IsLocalForm.dLoc_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hΩ.dMB_fibLoc hV hy]
  have hsum : HasWeakIntegral (fun t ↦ ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) • D j t) 0 1
      (∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) • weakIntegral (D j) 0 1) :=
    hasWeakIntegral_finsetSum _ (fun j _ ↦ (hDc j _).const_smul _)
      fun j _ ↦ (hDI j).const_smul _
  have h2 : fibLoc (LocallyConvex.Manifolds.dLoc Ω) (y, v) =
      (γ 1 - γ 0) - ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) • weakIntegral (D j) 0 1 := by
    have e : (fun t ↦ LocallyConvex.Manifolds.dLoc Ω (fibPt ((y, v), t))) =
        fun t ↦ De t - ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) • D j t :=
      funext fun t ↦ dLoc_fibPt Ω t y v
    rw [fibLoc, e]
    exact (hFTC.sub zero_le_one (hDec _)
      (continuousOn_finsetSum _ fun j _ ↦ (hDc j _).const_smul _) hsum).weakIntegral_eq
  rw [h1, h2]
  simp only [sliceLoc, γ]
  abel

omit [MackeyComplete F] in
/-- **The local homotopy formula in degree `0`**: `I(dΩ) = Ω|_{t = 1} - Ω|_{t = 0}`. -/
theorem IsLocalForm.fibLoc_dLoc_zero {Ω : (ℝ × E) × (Fin 0 → ℝ × E) → F}
    (hΩ : IsLocalForm 0 Ω (univ ×ˢ V)) (hV : IsOpen V) {y : E} (hy : y ∈ V) (v : Fin 0 → E) :
    fibLoc (LocallyConvex.Manifolds.dLoc Ω) (y, v) = sliceLoc 1 Ω (y, v) - sliceLoc 0 Ω (y, v) := by
  have hW : IsOpen (univ ×ˢ V : Set (ℝ × E)) := isOpen_univ.prod hV
  have hS : SmoothMBOn (fun z ↦ Ω (z, inclVec v)) (univ ×ˢ V) := hΩ.smooth_slice hW _
  have hγ : ∀ t ∈ uIcc (0 : ℝ) 1, HasDirDerivAt (fun t ↦ Ω ((t, y), inclVec v)) t 1
      (dMB (fun z ↦ Ω (z, inclVec v)) ((t, y), (1, 0))) := fun t _ ↦
    ((hS 1).2.1 (t, y) ⟨mem_univ _, hy⟩ (1, 0)).congr fun s ↦ by simp
  have hFTC := hasWeakIntegral_sub_of_hasDirDerivAt hγ
    (continuousOn_curve hV (SmoothMBOn.dMB_dir hW hS _ 0) hy _)
  have e : (fun t ↦ LocallyConvex.Manifolds.dLoc Ω (fibPt ((y, v), t))) =
      fun t ↦ dMB (fun z ↦ Ω (z, inclVec v)) ((t, y), (1, 0)) :=
    funext fun t ↦ dLoc_fibPt_zero Ω t y v
  rw [fibLoc, e, hFTC.weakIntegral_eq]
  rfl

end LocalHomotopy

/-! ### The manifold `ℝ × M` -/

section Cylinder

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

/-- The chart `id × i` of `ℝ × M`. -/
def prodAtlas (i : atlas E M) : atlas (ModelProd ℝ E) (ℝ × M) :=
  ⟨(OpenPartialHomeomorph.refl ℝ).prod i.1,
    Set.mem_image2_of_mem (by simp [chartedSpaceSelf_atlas]) i.2⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
@[simp] theorem prodAtlas_coe (i : atlas E M) :
    (prodAtlas i).1 = (OpenPartialHomeomorph.refl ℝ).prod i.1 :=
  rfl

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
/-- The preferred chart of `ℝ × M` at `(t, x)` is `id × (chart at x)`. -/
theorem prefChart_prod (t : ℝ) (x : M) :
    prefChart (E := ModelProd ℝ E) ((t, x) : ℝ × M) = prodAtlas (prefChart x) :=
  Subtype.ext (by simp [prodChartedSpace_chartAt, chartAt_self_eq])

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
theorem prodAtlas_target (i : atlas E M) :
    (prodAtlas i).1.target = (univ ×ˢ i.1.target : Set (ℝ × E)) := by
  simp

/-- Tangent coordinate changes between charts `id × i` and `id × j`. -/
theorem tangentCoordChange_prodAtlas (i j : atlas E M) {x : M}
    (hx : x ∈ i.1.source ∩ j.1.source) (t a : ℝ) (w : E) :
    tangentCoordChange (prodAtlas i) (prodAtlas j) ((t, x) : ℝ × M) ((a, w) : ModelProd ℝ E) =
      ((a, tangentCoordChange i j x w) : ℝ × E) := by
  have hy : i.1 x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source :=
    ⟨i.1.map_source hx.1, by simp [i.1.left_inv hx.1, hx.2]⟩
  have hg : HasDirDerivAt (j.1 ∘ i.1.symm) (i.1 x) w (dMB (j.1 ∘ i.1.symm) (i.1 x, w)) :=
    (smoothMBOn_transition' i j 1).2.1 _ hy w
  have h1 : HasDirDerivAt (fun p : ℝ × E ↦ p.1) (t, i.1 x) (a, w) a := by
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_sub_cancel_left]
    field_simp
  have h2 : HasDirDerivAt (fun p : ℝ × E ↦ (j.1 ∘ i.1.symm) p.2) (t, i.1 x) (a, w)
      (dMB (j.1 ∘ i.1.symm) (i.1 x, w)) := hg.congr fun s ↦ by simp
  have e : ((prodAtlas j).1 ∘ (prodAtlas i).1.symm) =
      fun p : ℝ × E ↦ (p.1, (j.1 ∘ i.1.symm) p.2) :=
    funext fun p ↦ rfl
  unfold tangentCoordChange
  rw [e]
  exact (h1.prodMk h2).dMB_eq

theorem tangentCoordChange_zero (i j : atlas E M) {x : M} (hx : x ∈ i.1.source ∩ j.1.source) :
    tangentCoordChange i j x 0 = 0 := by
  obtain ⟨T, hT⟩ := exists_linear_tangentCoordChange i j hx
  rw [hT, map_zero]

/-- The slice inclusion `iₜ : M → ℝ × M`, `x ↦ (t, x)`. -/
def sliceIncl (t : ℝ) (x : M) : ℝ × M := (t, x)

omit [MBManifold E M] in
/-- The slice inclusions are smooth. -/
theorem smoothMBM_sliceIncl (t : ℝ) : SmoothMBM E (ModelProd ℝ E) (sliceIncl (M := M) t) := by
  intro k
  refine ⟨(continuous_const.prodMk continuous_id).continuousOn, fun x _ ↦ ?_⟩
  set c := chartAt E x
  have hD := isOpen_chartDomain (f := sliceIncl (M := M) t) isOpen_univ
    (continuous_const.prodMk continuous_id).continuousOn c
    (chartAt (ModelProd ℝ E) (sliceIncl t x))
  have h : ContDiffMBOn k (fun y : E ↦ ((t, y) : ℝ × E)) univ :=
    ContDiffMBOn.prodMk isOpen_univ (contDiffMBOn_const k t univ) (smoothMBOn_id univ k)
  refine ContDiffMBOn.congr_of_isOpen hD (fun y hy ↦ ?_) (h.mono (subset_univ _))
  simp only [sliceIncl, comp_apply, prodChartedSpace_chartAt, chartAt_self_eq]
  show _ = ((t, c (c.symm y)) : ℝ × E)
  rw [c.right_inv hy.1]

/-- The pullback along a slice inclusion: `(iₜ*ω)ₓ(v) = ω_{(t, x)}((0, v₁), …, (0, vₙ))`. -/
theorem DifferentialForm.pullback_sliceIncl_apply {F : Type u} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [T2Space F] {n : ℕ} (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F n) (t : ℝ) (x : M)
    (v : Fin n → E) :
    ω.pullback (smoothMBM_sliceIncl t) x v = ω (t, x) (inclVec v) := by
  rw [DifferentialForm.pullback_apply]
  congr 1
  funext m
  set c := chartAt E x
  have hev : (chartAt (ModelProd ℝ E) (sliceIncl t x) ∘ sliceIncl t ∘ c.symm) =ᶠ[𝓝 (c x)]
      fun y : E ↦ ((t, y) : ℝ × E) :=
    Filter.eventually_of_mem (c.open_target.mem_nhds (c.map_source (mem_chart_source E x)))
      fun y hy ↦ by
        simp only [sliceIncl, comp_apply, prodChartedSpace_chartAt, chartAt_self_eq]
        show ((t, c (c.symm y)) : ℝ × E) = _
        rw [c.right_inv hy]
  rw [dMB_congr_of_eventuallyEq hev]
  have hd : HasDirDerivAt (fun y : E ↦ ((t, y) : ℝ × E)) (c x) (v m) ((0 : ℝ), v m) := by
    unfold HasDirDerivAt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    simp [smul_smul, inv_mul_cancel₀ hs]
  exact hd.dMB_eq

end Cylinder

/-! ### The fiber integral of forms and the homotopy formula -/

section FiberIntegral

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {k : ℕ}

namespace DifferentialForm

omit [LocallyConvexSpace ℝ E] [MBManifold E M] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- In the preferred chart at `x`, the local representative of any family of multilinear maps
at `x` is its value at `x`. -/
theorem formLocalRep_prefChart {n : ℕ} (f : M → (Fin n → E) → F) (x : M) (v : Fin n → E) :
    formLocalRep n (prefChart x) f (chartAt E x x, v) = f x v := by
  simp only [formLocalRep, prefChart]
  rw [(chartAt E x).left_inv (mem_chart_source E x)]
  congr 1
  funext m
  exact tangentCoordChange_self _ (mem_chart_source E x) _

/-- The fiber integral, pointwise: `I(ω)ₓ(v) = ∫₀¹ ω_{(t, x)}((1, 0), (0, v₁), …) dt`. -/
def fibIntFun (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1)) (x : M)
    (v : Fin k → E) : F :=
  weakIntegral (fun t ↦ ω (t, x) (Fin.cons (1, 0) (inclVec v))) 0 1

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- In the chart `i`, the fiber integral is the local fiber integral in the chart `id × i`. -/
theorem formLocalRep_fibIntFun (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1))
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : Fin k → E) :
    formLocalRep k i (fibIntFun ω) (y, v) = fibLoc (ω.localRep (prodAtlas i)) (y, v) := by
  set x := i.1.symm y
  have hx : x ∈ i.1.source ∩ (prefChart x).1.source := ⟨i.1.map_target hy, mem_chart_source E x⟩
  simp only [formLocalRep, fibIntFun, fibLoc, fibPt, localRep]
  congr 1
  funext t
  have hsymm : (prodAtlas i).1.symm ((t, y) : ModelProd ℝ E) = ((t, x) : ℝ × M) := rfl
  rw [hsymm, prefChart_prod]
  congr 1
  funext m
  cases m using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    rw [tangentCoordChange_prodAtlas i _ hx, tangentCoordChange_zero i _ hx]
  | succ j =>
    simp only [Fin.cons_succ, inclVec]
    rw [tangentCoordChange_prodAtlas i _ hx]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The local representatives of a form on `ℝ × M` in the charts `id × i` are local forms on
`ℝ × i(U)`. -/
theorem isLocalForm_localRep_prodAtlas {n : ℕ} (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F n)
    (i : atlas E M) :
    IsLocalForm n (ω.localRep (prodAtlas i) : (ℝ × E) × (Fin n → ℝ × E) → F)
      (univ ×ˢ i.1.target) := by
  have h := ω.isLocalForm_localRep (prodAtlas i)
  rwa [prodAtlas_target] at h

variable [MackeyComplete F]

/-- **The fiber integral** `I : Ωᵏ⁺¹(ℝ × M, F) → Ωᵏ(M, F)` (Glöckner–Neeb, proof of
Lemma 3.6.25), for a Mackey complete space `F`. -/
def fibInt (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1)) :
    DifferentialForm E M F k where
  toFun := fibIntFun ω
  alternating' x := by
    set i : atlas E M := prefChart x
    have hy : chartAt E x x ∈ i.1.target := (chartAt E x).map_source (mem_chart_source E x)
    obtain ⟨A, hA⟩ := ((isLocalForm_localRep_prodAtlas ω i).isLocalForm_fibLoc
      i.1.open_target).alternating _ hy
    refine ⟨A, fun v ↦ ?_⟩
    rw [← hA, ← formLocalRep_fibIntFun ω i hy, formLocalRep_prefChart]
  smooth' i n := ContDiffMBOn.congr_of_isOpen (i.1.open_target.prod isOpen_univ)
      (fun p hp ↦ (formLocalRep_fibIntFun ω i hp.1 p.2).symm) <|
    ((isLocalForm_localRep_prodAtlas ω i).isLocalForm_fibLoc i.1.open_target).smooth n

theorem fibInt_apply (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1)) (x : M)
    (v : Fin k → E) :
    fibInt ω x v = weakIntegral (fun t ↦ ω (t, x) (Fin.cons (1, 0) (inclVec v))) 0 1 :=
  rfl

theorem localRep_fibInt (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1))
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (v : Fin k → E) :
    (fibInt ω).localRep i (y, v) = fibLoc (ω.localRep (prodAtlas i)) (y, v) :=
  formLocalRep_fibIntFun ω i hy v

omit [MackeyComplete F] in
/-- In the preferred chart, the restriction to a slice is the local restriction. -/
theorem pullback_sliceIncl_eq_sliceLoc {n : ℕ}
    (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F n) (t : ℝ) (x : M) (v : Fin n → E) :
    ω.pullback (smoothMBM_sliceIncl t) x v =
      sliceLoc t (ω.localRep (prodAtlas (prefChart x))) (chartAt E x x, v) := by
  rw [pullback_sliceIncl_apply, sliceLoc, ← prefChart_prod t x,
    show ((t, chartAt E x x) : ℝ × E) = chartAt (ModelProd ℝ E) ((t, x) : ℝ × M) (t, x) by
      simp only [prodChartedSpace_chartAt, chartAt_self_eq]; rfl]
  exact (ω.localRep_prefChart (t, x) _).symm

/-- **The homotopy formula** (Glöckner–Neeb, (3.40)): `d I(ω) + I(dω) = i₁*ω - i₀*ω` for
`ω ∈ Ωᵏ⁺¹(ℝ × M, F)`. -/
theorem d_fibInt_add (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1)) :
    (fibInt ω).d + fibInt ω.d =
      ω.pullback (smoothMBM_sliceIncl 1) - ω.pullback (smoothMBM_sliceIncl 0) := by
  ext x v
  set i : atlas E M := prefChart x
  set y := chartAt E x x
  have hy : y ∈ i.1.target := (chartAt E x).map_source (mem_chart_source E x)
  have hΩ := isLocalForm_localRep_prodAtlas ω i
  rw [add_apply, sub_apply, pullback_sliceIncl_eq_sliceLoc, pullback_sliceIncl_eq_sliceLoc,
    ← hΩ.dLoc_fibLoc_add i.1.open_target hy]
  congr 1
  · rw [d_apply]
    exact dLoc_congr i.1.open_target (fun p hp ↦ localRep_fibInt ω i hp.1 p.2) hy v

/-- **The homotopy formula in degree `0`**: `I(df) = i₁*f - i₀*f`. -/
theorem fibInt_d_zero (ω : DifferentialForm (ModelProd ℝ E) (ℝ × M) F 0) :
    fibInt ω.d = ω.pullback (smoothMBM_sliceIncl 1) - ω.pullback (smoothMBM_sliceIncl 0) := by
  ext x v
  set i : atlas E M := prefChart x
  set y := chartAt E x x
  have hy : y ∈ i.1.target := (chartAt E x).map_source (mem_chart_source E x)
  have hΩ := isLocalForm_localRep_prodAtlas ω i
  rw [sub_apply, pullback_sliceIncl_eq_sliceLoc, pullback_sliceIncl_eq_sliceLoc,
    ← hΩ.fibLoc_dLoc_zero i.1.open_target hy]
  rw [← formLocalRep_prefChart (fibInt ω.d).toFun x v]
  change (fibInt ω.d).localRep i (y, v) = _
  rw [localRep_fibInt ω.d i hy]
  simp only [fibLoc]
  congr 1
  funext t
  exact ω.localRep_d (prodAtlas i) (by rw [prodAtlas_target]; exact ⟨mem_univ _, hy⟩) _

end DifferentialForm

end FiberIntegral

/-! ### The Homotopy Lemma and the Poincaré Lemma -/

section Poincare

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {k : ℕ}
  {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] [MBManifold E' N]

namespace DifferentialForm

/-- The pullback only depends on the map, not on the proof of its smoothness. -/
theorem pullback_congr_fun {n : ℕ} {φ ψ : M → N} (hφ : SmoothMBM E E' φ) (hψ : SmoothMBM E E' ψ)
    (h : φ = ψ) (ω : DifferentialForm E' N F n) : ω.pullback hφ = ω.pullback hψ := by
  subst h
  rfl

theorem pullback_zero' {n : ℕ} {φ : M → N} (hφ : SmoothMBM E E' φ) :
    (0 : DifferentialForm E' N F n).pullback hφ = 0 :=
  rfl

/-- **Pullbacks of forms of positive degree along constant maps vanish.** -/
theorem pullback_const_eq_zero {n : ℕ} (q : N) (hc : SmoothMBM E E' (fun _ : M ↦ q))
    (ω : DifferentialForm E' N F (n + 1)) : ω.pullback hc = 0 := by
  ext x v
  rw [pullback_apply, zero_apply]
  have hd : ∀ w : E, dMB (chartAt E' q ∘ (fun _ : M ↦ q) ∘ (chartAt E x).symm)
      (chartAt E x x, w) = 0 := fun w ↦ by
    have h : HasDirDerivAt (chartAt E' q ∘ (fun _ : M ↦ q) ∘ (chartAt E x).symm)
        (chartAt E x x) w 0 := by
      simp only [HasDirDerivAt, comp_apply, sub_self, smul_zero]
      exact tendsto_const_nhds
    exact h.dMB_eq
  simp only [hd]
  obtain ⟨A, hA⟩ := ω.alternating' q
  rw [hA]
  exact A.map_zero

variable [MackeyComplete F]

theorem fibInt_zero :
    fibInt (0 : DifferentialForm (ModelProd ℝ E) (ℝ × M) F (k + 1)) = 0 := by
  ext x v
  rw [fibInt_apply, zero_apply]
  simpa using (hasWeakIntegral_const (0 : F) 0 1).weakIntegral_eq

/-- **The Homotopy Lemma** (Glöckner–Neeb, Lemma 3.6.25), at the level of forms: if
`H : ℝ × M → N` is smooth, `Hₜ = H(t, ·)` and `α` is a closed `(k + 1)`-form on `N` with values
in a Mackey complete space, then `H₁*α - H₀*α = d I(H*α)`. -/
theorem pullback_sub_pullback_eq_d_fibInt {H : ℝ × M → N} (hH : SmoothMBM (ModelProd ℝ E) E' H)
    {α : DifferentialForm E' N F (k + 1)} (hα : α.IsClosed) :
    α.pullback (hH.comp (smoothMBM_sliceIncl 1)) - α.pullback (hH.comp (smoothMBM_sliceIncl 0)) =
      (fibInt (α.pullback hH)).d := by
  have hd : (α.pullback hH).d = 0 := by
    rw [d_pullback, show α.d = 0 from ext hα]
    rfl
  have h := d_fibInt_add (α.pullback hH)
  rw [hd, fibInt_zero, add_zero, pullback_pullback, pullback_pullback] at h
  exact h.symm

/-- **The Homotopy Lemma in degree `0`**: for a closed function `f` on `N`, `H₁*f = H₀*f`. -/
theorem pullback_eq_pullback_of_isClosed_zero {H : ℝ × M → N}
    (hH : SmoothMBM (ModelProd ℝ E) E' H) {f : DifferentialForm E' N F 0} (hf : f.IsClosed) :
    f.pullback (hH.comp (smoothMBM_sliceIncl 1)) =
      f.pullback (hH.comp (smoothMBM_sliceIncl 0)) := by
  have hd : (f.pullback hH).d = 0 := by
    rw [d_pullback, show f.d = 0 from ext hf]
    rfl
  have h := fibInt_d_zero (f.pullback hH)
  rw [hd, fibInt_zero, pullback_pullback, pullback_pullback] at h
  exact (sub_eq_zero.mp h.symm)

end DifferentialForm

open DifferentialForm

variable [MackeyComplete F]

/-- **The Homotopy Lemma** (Glöckner–Neeb, Lemma 3.6.25): homotopic smooth maps
`H₀, H₁ : M → N` induce the same maps `H^n_dR(N, F) → H^n_dR(M, F)` in de Rham cohomology with
values in a Mackey complete space `F`, for every `n`. Homotopies are smooth maps on `ℝ × M`. -/
theorem deRhamMap_homotopy {H : ℝ × M → N} (hH : SmoothMBM (ModelProd ℝ E) E' H) (n : ℕ) :
    deRhamMap (F := F) (hH.comp (smoothMBM_sliceIncl 1)) n =
      deRhamMap (hH.comp (smoothMBM_sliceIncl 0)) n := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun ω ↦ ?_)
  obtain ⟨ω, hω⟩ := ω
  have hω' : ω.IsClosed := mem_closedForms.mp hω
  show DeRham.mk (ω.pullback (hH.comp (smoothMBM_sliceIncl 1))) (hω'.pullback _) =
    DeRham.mk (ω.pullback (hH.comp (smoothMBM_sliceIncl 0))) (hω'.pullback _)
  rw [DeRham.mk_eq_mk_iff]
  cases n with
  | zero =>
    rw [pullback_eq_pullback_of_isClosed_zero hH hω', sub_self]
    exact Submodule.zero_mem _
  | succ k =>
    rw [pullback_sub_pullback_eq_d_fibInt hH hω']
    exact ⟨_, rfl⟩

variable (E M) in
/-- `M` is **smoothly contractible** to `p` (Glöckner–Neeb, Definition 3.6.27), with homotopies
defined on `ℝ × M`: there is a smooth `H : ℝ × M → M` with `H(0, x) = x` and `H(1, x) = p`. -/
def SmoothlyContractible : Prop :=
  ∃ (H : ℝ × M → M) (p : M), SmoothMBM (ModelProd ℝ E) E H ∧ (∀ x, H (0, x) = x) ∧
    ∀ x, H (1, x) = p

/-- **The Poincaré Lemma** (Glöckner–Neeb, Theorem 3.6.28): on a smoothly contractible manifold,
every closed form of positive degree with values in a Mackey complete space is exact. -/
theorem DifferentialForm.IsClosed.isExact_of_smoothlyContractible (hM : SmoothlyContractible E M)
    {α : DifferentialForm E M F (k + 1)} (hα : α.IsClosed) : α.IsExact := by
  obtain ⟨H, p, hH, h0, h1⟩ := hM
  have key := pullback_sub_pullback_eq_d_fibInt hH hα
  have e0 : α.pullback (hH.comp (smoothMBM_sliceIncl 0)) = α := by
    rw [pullback_congr_fun (hH.comp (smoothMBM_sliceIncl 0))
      (fun k ↦ smoothMBMOn_id (E := E) (M := M) isOpen_univ k)
      (funext fun x ↦ h0 x : H ∘ sliceIncl 0 = id), pullback_id]
  have e1 : α.pullback (hH.comp (smoothMBM_sliceIncl 1)) = 0 := by
    have hc : SmoothMBM E E (fun _ : M ↦ p) := fun k ↦ smoothMBMOn_const univ p k
    rw [pullback_congr_fun (hH.comp (smoothMBM_sliceIncl 1)) hc
      (funext fun x ↦ h1 x : H ∘ sliceIncl 1 = fun _ ↦ p), pullback_const_eq_zero]
  rw [e0, e1, zero_sub] at key
  exact ⟨-fibInt (α.pullback hH), by rw [d_neg, ← key, neg_neg]⟩

/-- The Poincaré Lemma in cohomology: `H^n_dR(M, F) = 0` for `n ≥ 1`. -/
theorem deRham_subsingleton_of_smoothlyContractible (hM : SmoothlyContractible E M) :
    Subsingleton (DeRham E M F (k + 1)) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H ω =>
  induction b using Submodule.Quotient.induction_on with
  | H η =>
  obtain ⟨ω, hω⟩ := ω
  obtain ⟨η, hη⟩ := η
  rw [Submodule.Quotient.eq]
  exact (mem_closedForms.mp (Submodule.sub_mem _ hω hη)).isExact_of_smoothlyContractible hM

end Poincare

/-! ### Star-shaped open sets (Corollary 3.6.29) -/

section StarShaped

/-- The reparametrization `c(t) = (1 - t)² / ((1 - t)² + t²)` used to contract star-shaped sets
along all of `ℝ`: it is smooth, `c(0) = 1`, `c(1) = 0` and `0 ≤ c ≤ 1`. -/
def contrParam (t : ℝ) : ℝ := (1 - t) ^ 2 / ((1 - t) ^ 2 + t ^ 2)

theorem contrParam_denom_pos (t : ℝ) : 0 < (1 - t) ^ 2 + t ^ 2 := by
  have h : (1 - t) ^ 2 + t ^ 2 = 2 * (t - 1 / 2) ^ 2 + 1 / 2 := by ring
  rw [h]
  positivity

theorem contrParam_zero : contrParam 0 = 1 := by norm_num [contrParam]

theorem contrParam_one : contrParam 1 = 0 := by norm_num [contrParam]

theorem contrParam_nonneg (t : ℝ) : 0 ≤ contrParam t :=
  div_nonneg (sq_nonneg _) (contrParam_denom_pos t).le

theorem contrParam_le_one (t : ℝ) : contrParam t ≤ 1 :=
  div_le_one_of_le₀ (le_add_of_nonneg_right (sq_nonneg t)) (contrParam_denom_pos t).le

theorem contDiff_contrParam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) contrParam :=
  ContDiff.div (by fun_prop) (by fun_prop) fun t ↦ (contrParam_denom_pos t).ne'

theorem smoothMBOn_contrParam : SmoothMBOn contrParam univ :=
  (smoothMBOn_iff_contDiffOn isOpen_univ).2 contDiff_contrParam.contDiffOn

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

open TopologicalSpace in
/-- The contraction `(t, x) ↦ p + c(t) (x - p)` of an open set star-shaped with respect to
`p`. -/
def starContraction (U : Opens E) (p : E) (hU : StarConvex ℝ p (U : Set E)) : ℝ × U → U :=
  fun q ↦ ⟨p + contrParam q.1 • ((q.2 : E) - p),
    hU.add_smul_sub_mem q.2.2 (contrParam_nonneg _) (contrParam_le_one _)⟩

open TopologicalSpace in
/-- **Open star-shaped subsets are smoothly contractible.** -/
theorem smoothlyContractible_of_starConvex (U : Opens E) {p : E} (hp : p ∈ U)
    (hU : StarConvex ℝ p (U : Set E)) : SmoothlyContractible E U := by
  refine ⟨starContraction U p hU, ⟨p, hp⟩, fun k ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hc : Continuous contrParam := contDiff_contrParam.continuous
    have hcont : Continuous (starContraction U p hU) :=
      continuous_induced_rng.2 (by
        change Continuous fun q : ℝ × U ↦ p + contrParam q.1 • ((q.2 : E) - p)
        fun_prop)
    refine ⟨hcont.continuousOn, fun q _ ↦ ?_⟩
    -- the local representative is `(s, z) ↦ p + c(s) (z - p)`
    have hG : ContDiffMBOn k (fun r : ℝ × E ↦ p + contrParam r.1 • (r.2 - p)) univ := by
      have h1 : ContDiffMBOn k (fun r : ℝ × E ↦ (contrParam r.1, r.2 - p)) univ := by
        refine ContDiffMBOn.prodMk isOpen_univ ?_ ?_
        · exact (smoothMBOn_contrParam k).comp isOpen_univ isOpen_univ
            ((ContinuousLinearMap.fst ℝ ℝ E).contDiffMBOn k univ) (mapsTo_univ _ _)
        · have h := ((ContinuousLinearMap.snd ℝ ℝ E).contDiffMBOn k univ).add isOpen_univ
            (contDiffMBOn_const k (-p) univ)
          exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun r _ ↦ by simp [sub_eq_add_neg]) h
      have h2 := (DifferentialForm.contDiffMBOn_smul_pair (F := E) k).comp isOpen_univ
        isOpen_univ h1
        (mapsTo_univ _ _)
      exact ContDiffMBOn.congr_of_isOpen isOpen_univ (fun r _ ↦ by simp)
        ((contDiffMBOn_const k p univ).add isOpen_univ h2)
    refine ContDiffMBOn.congr_of_isOpen (isOpen_chartDomain isOpen_univ hcont.continuousOn _ _)
      (fun r hr ↦ ?_) (hG.mono (subset_univ _))
    have hr2 : (((chartAt E q.2).symm r.2 : U) : E) = r.2 := by
      have := (chartAt E q.2).right_inv (show r.2 ∈ (chartAt E q.2).target from by
        have h := hr.1
        simp only [prodChartedSpace_chartAt, chartAt_self_eq,
          OpenPartialHomeomorph.prod_target, OpenPartialHomeomorph.refl_target] at h
        exact h.2)
      exact this
    show p + contrParam r.1 • (r.2 - p) = ((starContraction U p hU (r.1, (chartAt E q.2).symm r.2)
      : U) : E)
    simp only [starContraction, hr2]
  · exact Subtype.ext (by simp [starContraction, contrParam_zero])
  · exact Subtype.ext (by simp [starContraction, contrParam_one])

open TopologicalSpace in
/-- **The Poincaré Lemma for star-shaped open sets** (Glöckner–Neeb, Corollary 3.6.29): on an
open subset of `E` which is star-shaped with respect to one of its points, every closed form of
positive degree with values in a Mackey complete space is exact. -/
theorem DifferentialForm.IsClosed.isExact_of_starConvex {F : Type u} [AddCommGroup F]
    [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F] [MackeyComplete F] {k : ℕ} {U : Opens E} {p : E}
    (hp : p ∈ U) (hU : StarConvex ℝ p (U : Set E)) {α : DifferentialForm E U F (k + 1)}
    (hα : α.IsClosed) : α.IsExact :=
  hα.isExact_of_smoothlyContractible (smoothlyContractible_of_starConvex U hp hU)

end StarShaped

end LocallyConvex.Manifolds

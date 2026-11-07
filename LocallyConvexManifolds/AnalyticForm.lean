/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexAnalysis.AnalyticOperations
import LocallyConvexManifolds.Analytic
import LocallyConvexManifolds.Wedge
import LocallyConvexManifolds.LieDerivative
import LocallyConvexManifolds.DeRham

/-!
# Real analytic differential forms

Reference: H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*, Remark 3.6.18: on a real
analytic manifold modeled on a real locally convex space, a differential form is *real analytic*
if its local representatives `(y, v₁, …, vₙ) ↦ ω_{φ⁻¹ y}(Tφ⁻¹ v₁, …, Tφ⁻¹ vₙ)` are real
analytic, and "all of the preceding constructions, results and proofs carry over directly".

Real analyticity is in the sense of Milnor (`LocallyConvex.Analysis.RealAnalyticOn`: restrictions
of complex analytic maps on open subsets of the complexification). Since a real analytic manifold
is in particular smooth (`RealAnalyticManifold.mbManifold`), a real analytic form is a smooth form
`ω ∈ Ωⁿ(M, F)` with an extra property, `DifferentialForm.IsRealAnalytic`, and the real analytic
forms are a subspace `Ωⁿ_ω(M, F)` of `Ωⁿ(M, F)`. The constructions on smooth forms then preserve
real analyticity:

## Main results

* `analyticForms`: the subspace `Ωⁿ_ω(M, F)` of real analytic forms;
* `IsRealAnalytic.d`: `dω` is real analytic if `ω` is (in a chart, `dω` is a sum of terms
  `dω_loc ∘ L` with `L` continuous linear, and `dω_loc` is real analytic by
  `LocallyConvex.Analysis.RealAnalyticOn.dMB`); `analyticDLinear` is `d : Ωⁿ_ω → Ωⁿ⁺¹_ω`;
* `IsRealAnalytic.compCLM`, `IsRealAnalytic.wedge`: composition with continuous linear maps and
  wedge products with respect to continuous bilinear maps;
* `IsRealAnalytic.pullback`: pullbacks along real analytic maps;
* `SmoothVectorField.IsRealAnalytic`: real analytic vector fields, with
  `IsRealAnalytic.bracket`; `IsRealAnalytic.interior`, `IsRealAnalytic.lieDeriv`: the insertion
  of a real analytic vector field and the Lie derivative along it preserve real analytic forms.
  The identities of Proposition 3.6.16 then hold in `Ωⁿ_ω(M, F)`, since they hold in `Ωⁿ(M, F)`;
* `AnalyticDeRham`: the real analytic de Rham cohomology
  `H^n_ω(M, F) = Z^n_ω(M, F) / B^n_ω(M, F)`, and the natural linear map
  `AnalyticDeRham.toDeRham : H^n_ω(M, F) → H^n_dR(M, F)`.

The analytic de Rham cohomology is defined with real analytic primitives: a real analytic form is
*analytically exact* if it is `dη` for a real analytic `η`. Whether a closed real analytic form
which is exact (as a smooth form) has a real analytic primitive, i.e. whether `toDeRham` is
injective, is a question we do not address. For a real analytic submanifold `V` of `ℝ^n` the map
is an isomorphism: this is stated by H. Cartan, *Variétés analytiques réelles et variétés
analytiques complexes*, Bull. Soc. Math. France 85 (1957), §7, consequence (4), p. 89, as a
consequence of his Theorem 3 (Theorem B for coherent analytic sheaves on analytic subsets of
`ℝ^n`); Cartan omits the proof and refers to his earlier seminar and colloquium notes. Every
second countable real analytic manifold is of this kind by Grauert's embedding theorem (1958).
The proof (complexifications, sheaf cohomology on Stein manifolds) has no counterpart for general
locally convex models.

No completeness of `E` or `F` is assumed.
-/

open Set Function
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe u v

/-! ### Preliminaries on real analytic maps -/

section Preliminaries

variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- `(a, w) ↦ (a, w₀, …, w_{n-1})`, as a continuous linear map `E × Eⁿ → Eⁿ⁺¹`. -/
def consCLM (n : ℕ) : E × (Fin n → E) →L[ℝ] (Fin (n + 1) → E) :=
  ContinuousLinearMap.pi fun k ↦ Fin.cases (ContinuousLinearMap.fst ℝ E _)
    (fun j ↦ ContinuousLinearMap.proj j ∘L ContinuousLinearMap.snd ℝ E _) k

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem consCLM_apply {n : ℕ} (a : E) (w : Fin n → E) :
    consCLM n (a, w) = (Fin.cons a w : Fin (n + 1) → E) := by
  funext k
  cases k using Fin.cases <;> rfl

/-- Real analyticity of a map into `Eⁿ` follows from that of its components. -/
theorem realAnalyticOn_pi : ∀ {n : ℕ} {g : Fin n → X → E} {U : Set X},
    (∀ k, RealAnalyticOn (g k) U) → RealAnalyticOn (fun x k ↦ g k x) U
  | 0, g, U, _ => by
    have : (fun x k ↦ g k x) = fun _ ↦ (fun k ↦ Fin.elim0 k : Fin 0 → E) :=
      funext fun _ ↦ funext fun k ↦ k.elim0
    rw [this]
    exact realAnalyticOn_const _ U
  | n + 1, g, U, hg => by
    have h := ((hg 0).prodMk (realAnalyticOn_pi (g := fun k ↦ g k.succ) fun k ↦ hg k.succ)).clm_comp
      (consCLM n)
    refine realAnalyticOn_congr (fun x _ ↦ ?_) h
    simp only [consCLM_apply]
    funext k
    cases k using Fin.cases <;> rfl

/-- Precomposition with a continuous linear map, on a set `U ⊆ L⁻¹(V)`. -/
theorem _root_.LocallyConvex.Analysis.RealAnalyticOn.comp_clm_of_mapsTo
    {F : Type v} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [T2Space F] {g : E → F} {V : Set E} (hg : RealAnalyticOn g V) (L : X →L[ℝ] E) {U : Set X}
    (hUV : MapsTo L U V) : RealAnalyticOn (fun x ↦ g (L x)) U :=
  (hg.comp_clm L).mono hUV

end Preliminaries

/-! ### Local operations -/

section Local

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] {n : ℕ}

/-- The local exterior derivative of a real analytic local form is real analytic. -/
theorem realAnalyticOn_dLoc
    {ω : E × (Fin n → E) → F} {U : Set E} (hU : IsOpen U)
    (hω : RealAnalyticOn ω (U ×ˢ univ)) : RealAnalyticOn (dLoc ω) (U ×ˢ univ) := by
  rw [IsLocalForm.dLoc_eq_sum_dMB]
  refine RealAnalyticOn.sum _ fun i _ ↦ RealAnalyticOn.const_smul ?_ _
  exact (hω.dMB (hU.prod isOpen_univ)).comp_clm_of_mapsTo (IsLocalForm.termCLM i)
    fun p hp ↦ by exact ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩

/-- The local pullback of a real analytic local form along a real analytic map is real
analytic. -/
theorem realAnalyticOn_pullbackLoc
    {τ : E → E'} {ω : E' × (Fin n → E') → F} {U : Set E}
    {V : Set E'} (hU : IsOpen U) (hω : RealAnalyticOn ω (V ×ˢ univ)) (hτ : RealAnalyticOn τ U)
    (hUV : MapsTo τ U V) : RealAnalyticOn (pullbackLoc τ ω) (U ×ˢ univ) := by
  have h₁ : RealAnalyticOn (fun p : E × (Fin n → E) ↦ τ p.1) (U ×ˢ univ) :=
    hτ.comp_clm_of_mapsTo (ContinuousLinearMap.fst ℝ E (Fin n → E)) fun p hp ↦ hp.1
  have h₂ : ∀ k : Fin n, RealAnalyticOn (fun p : E × (Fin n → E) ↦ dMB τ (p.1, p.2 k))
      (U ×ˢ univ) := fun k ↦ by
    let L : E × (Fin n → E) →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E (Fin n → E)).prod
      ((ContinuousLinearMap.proj k) ∘L ContinuousLinearMap.snd ℝ E (Fin n → E))
    have hL : MapsTo L (U ×ˢ univ) (U ×ˢ univ) := fun p hp ↦ by simpa [L] using hp.1
    have h := (hτ.dMB hU).comp (L.realAnalyticOn (U ×ˢ univ)) hL
    refine realAnalyticOn_congr (fun p _ ↦ ?_) h
    simp [L]
  have hΨ : RealAnalyticOn (fun p : E × (Fin n → E) ↦ (τ p.1, fun k ↦ dMB τ (p.1, p.2 k)))
      (U ×ˢ univ) := by
    have hpi : RealAnalyticOn
        (fun p : E × (Fin n → E) ↦ fun k ↦ dMB τ (p.1, p.2 k))
        (U ×ˢ univ) := realAnalyticOn_pi h₂
    exact RealAnalyticOn.prodMk (F := E') (G := Fin n → E') h₁ hpi
  have hmaps : MapsTo (fun p : E × (Fin n → E) ↦
      (τ p.1, fun k ↦ dMB τ (p.1, p.2 k))) (U ×ˢ univ) (V ×ˢ univ) :=
    fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩
  have h := RealAnalyticOn.comp (F := E' × (Fin n → E')) hω hΨ hmaps
  exact realAnalyticOn_congr (g := pullbackLoc τ ω) (fun _ _ ↦ rfl) h

/-- The insertion of a real analytic vector field into a real analytic local form is real
analytic. -/
theorem realAnalyticOn_iLoc
    {ω : E × (Fin (n + 1) → E) → F} {X : E → E} {U : Set E}
    (hω : RealAnalyticOn ω (U ×ˢ univ)) (hX : RealAnalyticOn X U) :
    RealAnalyticOn (iLoc X ω) (U ×ˢ univ) := by
  have h₁ : RealAnalyticOn (fun p : E × (Fin n → E) ↦ X p.1) (U ×ˢ univ) :=
    hX.comp_clm_of_mapsTo (ContinuousLinearMap.fst ℝ E (Fin n → E)) fun p hp ↦ hp.1
  have h₂ : RealAnalyticOn (fun p : E × (Fin n → E) ↦ (p.1, consCLM n (X p.1, p.2)))
      (U ×ˢ univ) :=
    ((ContinuousLinearMap.fst ℝ E _).realAnalyticOn _).prodMk
      ((h₁.prodMk ((ContinuousLinearMap.snd ℝ E _).realAnalyticOn _)).clm_comp (consCLM n))
  refine realAnalyticOn_congr (fun p _ ↦ ?_) (hω.comp h₂ fun p hp ↦ ⟨hp.1, mem_univ _⟩)
  simp only [comp_apply, consCLM_apply]
  rfl

/-- The local Lie bracket of real analytic vector fields is real analytic. -/
theorem realAnalyticOn_localBracket
    {X Y : E → E} {U : Set E} (hU : IsOpen U)
    (hX : RealAnalyticOn X U) (hY : RealAnalyticOn Y U) :
    RealAnalyticOn (localBracket X Y) U := by
  have hid := (ContinuousLinearMap.id ℝ E).realAnalyticOn U
  exact ((hY.dMB hU).comp (hid.prodMk hX) fun y hy ↦ ⟨hy, mem_univ _⟩).sub
    ((hX.dMB hU).comp (hid.prodMk hY) fun y hy ↦ ⟨hy, mem_univ _⟩)

end Local

/-! ### Real analytic forms -/

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [RealAnalyticManifold E M]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type u} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G] {n : ℕ}

namespace DifferentialForm

/-- A differential form on a real analytic manifold is **real analytic** if its local
representatives `(y, v) ↦ ω_{i⁻¹ y}(Ti⁻¹ v)` in the charts `i` of the atlas are real analytic
(Glöckner–Neeb, Remark 3.6.18). -/
def IsRealAnalytic (ω : DifferentialForm E M F n) : Prop :=
  ∀ i : atlas E M, RealAnalyticOn (ω.localRep i) (i.1.target ×ˢ univ)

omit [RealAnalyticManifold E M] in
theorem isRealAnalytic_zero : (0 : DifferentialForm E M F n).IsRealAnalytic := fun _ ↦
  realAnalyticOn_const (0 : F) _

omit [RealAnalyticManifold E M] in
theorem IsRealAnalytic.add {ω η : DifferentialForm E M F n} (hω : ω.IsRealAnalytic)
    (hη : η.IsRealAnalytic) : (ω + η).IsRealAnalytic := fun i ↦ (hω i).add (hη i)

omit [RealAnalyticManifold E M] in
theorem IsRealAnalytic.smul {ω : DifferentialForm E M F n} (hω : ω.IsRealAnalytic) (c : ℝ) :
    (c • ω).IsRealAnalytic := fun i ↦ (hω i).const_smul c

variable (E M F n) in
/-- The subspace `Ωⁿ_ω(M, F)` of real analytic `n`-forms. -/
def analyticForms : Submodule ℝ (DifferentialForm E M F n) where
  carrier := {ω | ω.IsRealAnalytic}
  zero_mem' := isRealAnalytic_zero
  add_mem' := IsRealAnalytic.add
  smul_mem' c _ hω := IsRealAnalytic.smul hω c

omit [RealAnalyticManifold E M] in
theorem mem_analyticForms {ω : DifferentialForm E M F n} :
    ω ∈ analyticForms E M F n ↔ ω.IsRealAnalytic :=
  Iff.rfl

/-- **The exterior derivative of a real analytic form is real analytic.** -/
theorem IsRealAnalytic.d {ω : DifferentialForm E M F n} (hω : ω.IsRealAnalytic) :
    ω.d.IsRealAnalytic := fun i ↦
  realAnalyticOn_congr (fun p hp ↦ (ω.localRep_d i hp.1 p.2).symm)
    (realAnalyticOn_dLoc i.1.open_target (hω i))

variable (E M F n) in
/-- The exterior derivative `d : Ωⁿ_ω(M, F) → Ωⁿ⁺¹_ω(M, F)`. -/
def analyticDLinear : analyticForms E M F n →ₗ[ℝ] analyticForms E M F (n + 1) :=
  (dLinear E M F n).restrict fun _ hω ↦ IsRealAnalytic.d hω

@[simp] theorem analyticDLinear_apply (ω : analyticForms E M F n) :
    (analyticDLinear E M F n ω : DifferentialForm E M F (n + 1)) =
      (ω : DifferentialForm E M F n).d :=
  rfl

omit [RealAnalyticManifold E M] in
/-- Composition with a continuous linear map preserves real analytic forms. -/
theorem IsRealAnalytic.compCLM {ω : DifferentialForm E M F n} (hω : ω.IsRealAnalytic)
    (α : F →L[ℝ] G) : (ω.compCLM α).IsRealAnalytic := fun i ↦ (hω i).clm_comp α

section Wedge

variable {E₁ E₂ E₃ : Type u}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [AddCommGroup E₃] [Module ℝ E₃] [TopologicalSpace E₃] [IsTopologicalAddGroup E₃]
  [ContinuousSMul ℝ E₃] [LocallyConvexSpace ℝ E₃] [T2Space E₃]
  {β : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] E₃} {p q : ℕ}

omit [RealAnalyticManifold E M] in
/-- **Wedge products of real analytic forms are real analytic**: in a chart, the wedge product is
a finite sum of terms `β(ω_loc ∘ L, η_loc ∘ L')` with `L`, `L'` continuous linear. -/
theorem IsRealAnalytic.wedge (hβ : Continuous fun r : E₁ × E₂ ↦ β r.1 r.2)
    {ω : DifferentialForm E M E₁ p} {η : DifferentialForm E M E₂ q} (hω : ω.IsRealAnalytic)
    (hη : η.IsRealAnalytic) : (ω.wedge β hβ η).IsRealAnalytic := fun i ↦ by
  rw [localRep_wedge]
  refine RealAnalyticOn.const_smul ?_ _
  refine RealAnalyticOn.sum _ fun σ _ ↦ RealAnalyticOn.const_smul ?_ _
  exact RealAnalyticOn.bilin β hβ
    ((hω i).comp_clm_of_mapsTo (wedgeLeftCLM σ) fun r hr ↦ ⟨hr.1, mem_univ _⟩)
    ((hη i).comp_clm_of_mapsTo (wedgeRightCLM σ) fun r hr ↦ ⟨hr.1, mem_univ _⟩)

end Wedge

section Pullback

variable {E₀ : Type u} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E₀ N] [RealAnalyticManifold E₀ N] {φ : N → M}

/-- **Pullbacks of real analytic forms along real analytic maps are real analytic.** As for
smoothness of pullbacks, near each point the local representative of `φ*ω` in the chart `i` is
the local pullback of the representative of `ω` in the preferred chart `j` at the image point,
along the real analytic map `j ∘ φ ∘ i⁻¹`; real analyticity is local
(`LocallyConvex.Analysis.RealAnalyticOn.of_local`, Glöckner–Neeb, Lemma 2.2.3). -/
theorem IsRealAnalytic.pullback (hφ : SmoothMBM E₀ E φ)
    (hφa : RealAnalyticMOn (E := E₀) (F := E) φ univ) {ω : DifferentialForm E M F n}
    (hω : ω.IsRealAnalytic) : (ω.pullback hφ).IsRealAnalytic := fun i ↦ by
  have hT : IsOpen (i.1.target ×ˢ (univ : Set (Fin n → E₀))) := i.1.open_target.prod isOpen_univ
  refine RealAnalyticOn.of_local hT fun p hp ↦ ?_
  set j : atlas E M := prefChart (φ (i.1.symm p.1))
  set W := chartDomain φ univ i.1 j.1
  have hW : IsOpen W := isOpen_chartDomain isOpen_univ (hφ 1).1 i.1 j.1
  have hτ : RealAnalyticOn (j.1 ∘ φ ∘ i.1.symm) W :=
    hφa.realAnalyticOn_chart isOpen_univ
      (StructureGroupoid.subset_maximalAtlas _ i.2) (StructureGroupoid.subset_maximalAtlas _ j.2)
  have hWj : MapsTo (j.1 ∘ φ ∘ i.1.symm) W j.1.target := fun z hz ↦ j.1.map_source hz.2.2
  have hpW : p.1 ∈ W := ⟨hp.1, mem_univ _, mem_chart_source E _⟩
  refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨hpW, mem_univ _⟩, ?_⟩
  have hsub : (i.1.target ×ˢ univ) ∩ (W ×ˢ univ) = W ×ˢ (univ : Set (Fin n → E₀)) := by
    rw [Set.prod_inter_prod, inter_univ, inter_eq_right.mpr (fun z (hz : z ∈ W) ↦ hz.1)]
  rw [hsub]
  exact realAnalyticOn_congr (fun q hq ↦ (formLocalRep_pullbackFun' (hφ 1) ω i j hq.1 q.2).symm)
    (realAnalyticOn_pullbackLoc hW (hω j) hτ hWj)

end Pullback

end DifferentialForm

/-! ### Real analytic vector fields, insertion and Lie derivatives -/

namespace SmoothVectorField

/-- A smooth vector field on a real analytic manifold is **real analytic** if its local
representatives in the charts of the atlas are real analytic. -/
def IsRealAnalytic (X : SmoothVectorField E M) : Prop :=
  ∀ i : atlas E M, RealAnalyticOn (X.rep i) i.1.target

/-- The Lie bracket of real analytic vector fields is real analytic. -/
theorem IsRealAnalytic.bracket {X Y : SmoothVectorField E M} (hX : X.IsRealAnalytic)
    (hY : Y.IsRealAnalytic) : (X.bracket Y).IsRealAnalytic := fun i ↦
  realAnalyticOn_congr (fun _ hy ↦ (localRep_bracket X Y i hy).symm)
    (realAnalyticOn_localBracket i.1.open_target (hX i) (hY i))

end SmoothVectorField

namespace DifferentialForm

variable {X : SmoothVectorField E M}

/-- The insertion of a real analytic vector field into a real analytic form is real analytic. -/
theorem IsRealAnalytic.interior (hX : X.IsRealAnalytic) {ω : DifferentialForm E M F (n + 1)}
    (hω : ω.IsRealAnalytic) : (interior X ω).IsRealAnalytic := fun i ↦
  realAnalyticOn_congr (fun p hp ↦ (localRep_interior X ω i hp.1 p.2).symm)
    (realAnalyticOn_iLoc (hω i) (hX i))

/-- The Lie derivative of a real analytic form along a real analytic vector field is real
analytic: `L_X = d ∘ i_X + i_X ∘ d`. -/
theorem IsRealAnalytic.lieDeriv (hX : X.IsRealAnalytic) {ω : DifferentialForm E M F n}
    (hω : ω.IsRealAnalytic) : (lieDeriv X ω).IsRealAnalytic := by
  cases n with
  | zero => exact hω.d.interior hX
  | succ n =>
    rw [lieDeriv_succ]
    exact (hω.interior hX).d.add (hω.d.interior hX)

end DifferentialForm

/-! ### Real analytic de Rham cohomology -/

namespace DifferentialForm

variable (E M F) in
/-- The closed real analytic `n`-forms `Z^n_ω(M, F)`. -/
def analyticClosedForms (n : ℕ) : Submodule ℝ (DifferentialForm E M F n) :=
  closedForms E M F n ⊓ analyticForms E M F n

variable (E M F) in
/-- The *analytically exact* `n`-forms `B^n_ω(M, F) = d(Ω^{n-1}_ω(M, F))`, the exterior
derivatives of real analytic forms, with `B^0_ω(M, F) = 0`. -/
def analyticExactForms : (n : ℕ) → Submodule ℝ (DifferentialForm E M F n)
  | 0 => ⊥
  | n + 1 => (analyticForms E M F n).map (dLinear E M F n)

theorem analyticExactForms_le_analyticClosedForms (n : ℕ) :
    analyticExactForms E M F n ≤ analyticClosedForms E M F n := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨η, hη, rfl⟩
    exact ⟨exactForms_le_closedForms (n + 1) ⟨η, rfl⟩, IsRealAnalytic.d hη⟩

theorem analyticExactForms_le_exactForms (n : ℕ) :
    analyticExactForms E M F n ≤ exactForms E M F n := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    rintro _ ⟨η, -, rfl⟩
    exact ⟨η, rfl⟩

end DifferentialForm

open DifferentialForm

variable (E M F) in
/-- The real analytic de Rham cohomology `H^n_ω(M, F) = Z^n_ω(M, F) / B^n_ω(M, F)`. -/
abbrev AnalyticDeRham (n : ℕ) : Type _ :=
  analyticClosedForms E M F n ⧸
    (analyticExactForms E M F n).comap (analyticClosedForms E M F n).subtype

variable (E M F) in
/-- The natural linear map `H^n_ω(M, F) → H^n_dR(M, F)`, sending the class of a closed real
analytic form to its de Rham class. -/
def AnalyticDeRham.toDeRham (n : ℕ) : AnalyticDeRham E M F n →ₗ[ℝ] DeRham E M F n :=
  Submodule.mapQ _ _ (Submodule.inclusion inf_le_left) fun _ hω ↦
    analyticExactForms_le_exactForms n hω

theorem AnalyticDeRham.toDeRham_mk {n : ℕ} (ω : DifferentialForm E M F n)
    (hω : ω ∈ analyticClosedForms E M F n) :
    AnalyticDeRham.toDeRham E M F n (Submodule.Quotient.mk ⟨ω, hω⟩) =
      DeRham.mk ω (mem_closedForms.mp hω.1) :=
  rfl

end LocallyConvex.Manifolds

/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Homotopy
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Symplectic manifolds

A symplectic form on a manifold `M` modeled on a locally convex space `E` is a closed real-valued
`2`-form `ω` which is nondegenerate at every point. In infinite dimensions "nondegenerate" splits
in two:

* `ω` is **weakly nondegenerate** if `ωₓ(v, w) = 0` for all `w` forces `v = 0`, i.e. the flat
  map `ω♭ₓ : TₓM → T'ₓM`, `v ↦ ωₓ(v, ·)`, is injective;
* `ω` is **strongly nondegenerate** if moreover every continuous linear functional on `TₓM` is of
  the form `ωₓ(v, ·)`, i.e. `ω♭ₓ` is bijective onto the topological dual.

Strong symplectic forms are rare: a normed space carrying a continuous skew-symmetric bilinear
form with surjective flat map is reflexive (`surjective_inclusionInDoubleDual_of_skew`), so a
nonempty strong symplectic manifold modeled on a normed space has a reflexive model
(`SymplecticForm.IsStrong.surjective_inclusionInDoubleDual`). No completeness is used in this
argument. Many symplectic forms of interest (for instance on spaces of smooth functions, which
are not normable) are only weakly nondegenerate.

## Main definitions and results

* `SymplecticForm E M`: a closed weakly nondegenerate `2`-form; `SymplecticForm.IsStrong`;
* `SymplecticForm.IsHamiltonianFor ω X f`: `i_X ω = df`. Hamiltonian vector fields are unique
  (`IsHamiltonianFor.unique`), but need not exist for weak forms;
* `SymplecticForm.IsSymplecticField ω X`: `L_X ω = 0`, equivalently `i_X ω` is closed
  (`isSymplecticField_iff`). Hamiltonian fields are symplectic, and on a smoothly contractible
  manifold every symplectic field is Hamiltonian (`IsSymplecticField.exists_isHamiltonianFor`,
  from the Poincaré Lemma);
* `interior_bracket`: for symplectic `X, Y`, `i_{[X, Y]} ω = d(ω(Y, X))`, so the bracket of two
  symplectic fields is Hamiltonian;
* conservation of energy (`IsHamiltonianFor.lieDeriv_self`), the Poisson bracket `{f, g}` and its
  Jacobi identity (`poisson_jacobi`);
* symplectomorphisms and the transport of Hamiltonian fields along them;
* the canonical symplectic form `ω = dθ` on `H × H` for a real inner product space `H`
  (`canonicalSymplectic`), weak in general and strong when `H` is complete.

The Darboux theorem is not formalized. For strong symplectic forms on Banach manifolds it was
proved by A. Weinstein (*Symplectic structures on Banach manifolds*, Bull. Amer. Math. Soc. 75
(1969), §1, Theorem) with Moser's trick, which needs flows of time-dependent vector fields; these
need not exist on locally convex manifolds. For weak symplectic forms the theorem fails even on
Hilbert spaces (J. Marsden, *Darboux's theorem fails for weak symplectic forms*, Proc. Amer. Math.
Soc. 32 (1972), Proposition, p. 591). Real-valued forms require models in `Type`, since the
value space of a form lives in the universe of the model.
-/

open Set Function
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

universe v

/-! ### Reflexivity of strong symplectic normed spaces -/

section Linear

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Strong symplectic normed spaces are reflexive.** If `ω` is a continuous skew-symmetric
bilinear form on a normed space `V` whose flat map `V → V'` is surjective, then the canonical
embedding of `V` into its bidual is surjective. Given `Φ ∈ V''`, choose `v` with
`ω(v, ·) = -Φ ∘ ω♭`; then `Φ(ω(w, ·)) = ω(w, v)` for all `w`, and every functional is of the form
`ω(w, ·)`. No completeness is needed. -/
theorem surjective_inclusionInDoubleDual_of_skew (ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hskew : ∀ v w, ω v w = -ω w v) (hsurj : Surjective ω) :
    Surjective (NormedSpace.inclusionInDoubleDual ℝ V) := by
  intro Φ
  obtain ⟨v, hv⟩ := hsurj (-(Φ.comp ω))
  refine ⟨v, ContinuousLinearMap.ext fun φ ↦ ?_⟩
  obtain ⟨w, rfl⟩ := hsurj φ
  rw [NormedSpace.dual_def, hskew, hv]
  simp

end Linear

variable {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

open DifferentialForm SmoothVectorField

/-! ### Vector fields and their values -/

/-- A smooth vector field is determined by its values in the preferred charts. -/
theorem SmoothVectorField.ext_vec {X Y : SmoothVectorField E M} (h : ∀ x, X.vec x = Y.vec x) :
    X = Y := by
  obtain ⟨X, hX, sX⟩ := X
  obtain ⟨Y, hY, sY⟩ := Y
  have : X = Y := by
    funext x
    have h1 := hX x
    have h2 := hY x
    have h3 := h x
    simp only [SmoothVectorField.vec] at h3
    revert h1 h2 h3
    obtain ⟨p, a⟩ := X x
    obtain ⟨q, b⟩ := Y x
    rintro rfl rfl h3
    exact congrArg _ h3
  subst this
  rfl

/-! ### Symplectic forms -/

variable (E M) in
/-- A (weak) **symplectic form**: a closed real-valued `2`-form which is weakly nondegenerate at
every point. -/
structure SymplecticForm where
  /-- The underlying `2`-form. -/
  form : DifferentialForm E M ℝ 2
  isClosed : form.IsClosed
  nondegenerate : ∀ x v, (∀ w, form x ![v, w] = 0) → v = 0

namespace SymplecticForm

variable (ω : SymplecticForm E M)

/-- A symplectic form is **strong** if at every point every continuous linear functional on the
tangent space is of the form `ωₓ(v, ·)`. -/
def IsStrong : Prop := ∀ (x : M) (φ : E →L[ℝ] ℝ), ∃ v, ∀ w, ω.form x ![v, w] = φ w

theorem form_swap (x : M) (v w : E) : ω.form x ![v, w] = -ω.form x ![w, v] := by
  obtain ⟨A, hA⟩ := ω.form.alternating' x
  rw [hA, hA]
  have := A.map_swap ![w, v] (i := 0) (j := 1) (by decide)
  rw [← this]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem form_sub_left (x : M) (u v w : E) :
    ω.form x ![u - v, w] = ω.form x ![u, w] - ω.form x ![v, w] := by
  obtain ⟨A, hA⟩ := ω.form.alternating' x
  rw [hA, hA, hA]
  have := A.map_update_sub ![u, w] 0 u v
  convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl)

/-- The value `ωₓ` of a form at a point is continuous on `E × E`. -/
theorem continuous_form (x : M) : Continuous (ω.form x) := by
  have h := ((ω.form.smooth' (prefChart x)) 0).continuousOn
  have hy : chartAt E x x ∈ (prefChart (E := E) x).1.target :=
    (chartAt E x).map_source (mem_chart_source E x)
  have hc : Continuous fun u : Fin 2 → E ↦ ω.form.localRep (prefChart x) (chartAt E x x, u) := by
    refine continuous_iff_continuousAt.2 fun u ↦ ?_
    exact (h.continuousAt
      (prod_mem_nhds ((prefChart (E := E) x).1.open_target.mem_nhds hy) Filter.univ_mem)).comp
      (continuous_const.prodMk continuous_id).continuousAt
  convert hc using 1
  funext u
  exact (ω.form.localRep_prefChart x u).symm

end SymplecticForm

namespace SymplecticForm

section Normed

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {N : Type v} [TopologicalSpace N] [ChartedSpace V N] [MBManifold V N]
  (ω : SymplecticForm V N)

/-- The value of a symplectic form at a point, as a continuous bilinear form on a normed model. -/
def flatCLM (x : N) : V →L[ℝ] V →L[ℝ] ℝ :=
  let A := Classical.choose (ω.form.alternating' x)
  have hA : ω.form x = ⇑A := funext (Classical.choose_spec (ω.form.alternating' x))
  let C : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ :=
    { toMultilinearMap := A.toMultilinearMap
      cont := by
        change Continuous (A : (Fin 2 → V) → ℝ)
        rw [← hA]
        exact ω.continuous_form x }
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w ↦ A ![v, w])
      (fun v v' w ↦ by
        have := A.map_update_add ![v, w] 0 v v'
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun c v w ↦ by
        have := A.map_update_smul ![v, w] 0 c v
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun v w w' ↦ by
        have := A.map_update_add ![v, w] 1 w w'
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl))
      (fun c v w ↦ by
        have := A.map_update_smul ![v, w] 1 c w
        convert this using 2 <;> (congr 1; funext k; fin_cases k <;> rfl)))
    ‖C‖ (fun v w ↦ by
      change ‖C ![v, w]‖ ≤ ‖C‖ * ‖v‖ * ‖w‖
      calc ‖C ![v, w]‖ ≤ ‖C‖ * ∏ i, ‖(![v, w] : Fin 2 → V) i‖ := C.le_opNorm _
        _ = ‖C‖ * ‖v‖ * ‖w‖ := by simp [Fin.prod_univ_two, mul_assoc])

theorem flatCLM_apply (x : N) (v w : V) : ω.flatCLM x v w = ω.form x ![v, w] := by
  exact (Classical.choose_spec (ω.form.alternating' x) _).symm

/-- **The model of a strong symplectic manifold is reflexive**: if a normed space `E` models a
nonempty manifold carrying a strong symplectic form, the canonical map `E → E''` is surjective.
In particular non-reflexive Banach spaces such as `ℓ¹` or `c₀` are not models of strong
symplectic manifolds. -/
theorem IsStrong.surjective_inclusionInDoubleDual (hω : ω.IsStrong) (x : N) :
    Surjective (NormedSpace.inclusionInDoubleDual ℝ V) := by
  refine surjective_inclusionInDoubleDual_of_skew (ω.flatCLM x)
    (fun v w ↦ by simp only [flatCLM_apply]; exact ω.form_swap x v w) fun φ ↦ ?_
  obtain ⟨v, hv⟩ := hω x φ
  exact ⟨v, ContinuousLinearMap.ext fun w ↦ by rw [flatCLM_apply, hv]⟩

end Normed

variable (ω : SymplecticForm E M)

/-! ### Insertion of vector fields -/

theorem interior_interior_swap (X Y : SmoothVectorField E M) :
    interior X (interior Y ω.form) = -interior Y (interior X ω.form) := by
  ext x v
  obtain rfl : v = ![] := Subsingleton.elim _ _
  exact ω.form_swap x (Y.vec x) (X.vec x)

/-- **Weak nondegeneracy, globally**: a vector field is determined by its insertion into `ω`. -/
theorem interior_injective {X Y : SmoothVectorField E M}
    (h : interior X ω.form = interior Y ω.form) : X = Y := by
  refine SmoothVectorField.ext_vec fun x ↦ sub_eq_zero.1 (ω.nondegenerate x _ fun w ↦ ?_)
  have hX := congrArg (fun η : DifferentialForm E M ℝ 1 ↦ η x ![w]) h
  simp only [interior_apply] at hX
  have e : ∀ a : E, (Fin.cons a ![w] : Fin 2 → E) = ![a, w] := fun a ↦ rfl
  rw [e, e] at hX
  rw [ω.form_sub_left, hX, sub_self]

/-! ### Hamiltonian and symplectic vector fields -/

/-- `X` is a **Hamiltonian vector field** of the function `f` (a `0`-form): `i_X ω = df`. -/
def IsHamiltonianFor (X : SmoothVectorField E M) (f : DifferentialForm E M ℝ 0) : Prop :=
  interior X ω.form = f.d

theorem IsHamiltonianFor.eq {ω : SymplecticForm E M} {X : SmoothVectorField E M}
    {f : DifferentialForm E M ℝ 0} (h : ω.IsHamiltonianFor X f) : interior X ω.form = f.d :=
  h

/-- Hamiltonian vector fields are unique (weak nondegeneracy suffices; existence may fail for
weak symplectic forms). -/
theorem IsHamiltonianFor.unique {ω : SymplecticForm E M} {X Y : SmoothVectorField E M}
    {f : DifferentialForm E M ℝ 0} (hX : ω.IsHamiltonianFor X f) (hY : ω.IsHamiltonianFor Y f) :
    X = Y :=
  ω.interior_injective (hX.trans hY.symm)

/-- `X` is a **symplectic vector field**: `L_X ω = 0`. -/
def IsSymplecticField (X : SmoothVectorField E M) : Prop := lieDeriv X ω.form = 0

theorem IsSymplecticField.eq {X : SmoothVectorField E M} (h : ω.IsSymplecticField X) :
    lieDeriv X ω.form = 0 :=
  h

/-- Since `ω` is closed, `L_X ω = d(i_X ω)`: `X` is symplectic iff `i_X ω` is closed. -/
theorem isSymplecticField_iff (X : SmoothVectorField E M) :
    ω.IsSymplecticField X ↔ (interior X ω.form).IsClosed := by
  rw [IsSymplecticField, ω.isClosed.lieDeriv_eq]
  exact ⟨fun h x v ↦ by rw [h]; rfl, fun h ↦ ext h⟩

/-- Hamiltonian vector fields are symplectic. -/
theorem IsHamiltonianFor.isSymplecticField {ω : SymplecticForm E M} {X : SmoothVectorField E M}
    {f : DifferentialForm E M ℝ 0} (hX : ω.IsHamiltonianFor X f) : ω.IsSymplecticField X := by
  rw [isSymplecticField_iff, (hX).eq]
  intro x v
  rw [d_d_eq_zero]
  rfl

/-- **Symplectic fields are locally Hamiltonian**: on a smoothly contractible manifold every
symplectic vector field is Hamiltonian. This is the Poincaré Lemma applied to the closed
`1`-form `i_X ω`. -/
theorem IsSymplecticField.exists_isHamiltonianFor (hM : SmoothlyContractible E M)
    {X : SmoothVectorField E M} (hX : ω.IsSymplecticField X) :
    ∃ f : DifferentialForm E M ℝ 0, ω.IsHamiltonianFor X f := by
  obtain ⟨f, hf⟩ := ((ω.isSymplecticField_iff X).1 hX).isExact_of_smoothlyContractible hM
  exact ⟨f, hf.symm⟩

/-- **The bracket of symplectic fields is Hamiltonian**: if `L_X ω = L_Y ω = 0`, then
`i_{[X, Y]} ω = d(ω(Y, X))`. This follows from `[L_X, i_Y] = i_{[X, Y]}` and Cartan's formula. -/
theorem interior_bracket {X Y : SmoothVectorField E M} (hX : ω.IsSymplecticField X)
    (hY : ω.IsSymplecticField Y) :
    interior (X.bracket Y) ω.form = (interior X (interior Y ω.form)).d := by
  have h := lieDeriv_interior_sub X Y ω.form
  have hYc : (interior Y ω.form).d = 0 := ext ((ω.isSymplecticField_iff Y).1 hY)
  rw [hX.eq, interior_zero, sub_zero, lieDeriv_succ, hYc,
    interior_zero, add_zero] at h
  exact h.symm

theorem IsSymplecticField.bracket {X Y : SmoothVectorField E M} (hX : ω.IsSymplecticField X)
    (hY : ω.IsSymplecticField Y) :
    ω.IsHamiltonianFor (X.bracket Y) (interior X (interior Y ω.form)) :=
  ω.interior_bracket hX hY

/-- **Conservation of energy**: a function is constant along its Hamiltonian vector field,
`L_X f = df(X) = ω(X, X) = 0`. -/
theorem IsHamiltonianFor.lieDeriv_self {ω : SymplecticForm E M} {X : SmoothVectorField E M}
    {f : DifferentialForm E M ℝ 0} (hX : ω.IsHamiltonianFor X f) : lieDeriv X f = 0 := by
  rw [lieDeriv_zero, ← (hX).eq, DifferentialForm.interior_interior]

/-! ### The Poisson bracket -/

theorem _root_.LocallyConvex.Manifolds.SmoothVectorField.lieDeriv_neg' (X : SmoothVectorField E M)
    {n : ℕ} (η : DifferentialForm E M ℝ n) : lieDeriv X (-η) = -lieDeriv X η :=
  (lieDerivLinear ℝ n X).map_neg η

/-- The **Poisson bracket** `{f, g} = ω(X_f, X_g) = -X_f(g)`, defined for a function `f` with
Hamiltonian vector field `X_f`. -/
def poisson (Xf : SmoothVectorField E M) (g : DifferentialForm E M ℝ 0) :
    DifferentialForm E M ℝ 0 :=
  -lieDeriv Xf g

/-- `{f, g} = ω(X_f, X_g)`. -/
theorem poisson_eq {Xf Xg : SmoothVectorField E M} {f g : DifferentialForm E M ℝ 0}
    (_hf : ω.IsHamiltonianFor Xf f) (hg : ω.IsHamiltonianFor Xg g) :
    poisson Xf g = interior Xg (interior Xf ω.form) := by
  rw [poisson, lieDeriv_zero, ← (hg).eq, interior_interior_swap, neg_neg]

/-- `{f, g} = X_g(f)`. -/
theorem poisson_eq_lieDeriv {Xf Xg : SmoothVectorField E M} {f g : DifferentialForm E M ℝ 0}
    (hf : ω.IsHamiltonianFor Xf f) (hg : ω.IsHamiltonianFor Xg g) :
    poisson Xf g = lieDeriv Xg f := by
  rw [ω.poisson_eq hf hg, lieDeriv_zero, (hf).eq]

/-- Antisymmetry of the Poisson bracket. -/
theorem poisson_antisymm {Xf Xg : SmoothVectorField E M} {f g : DifferentialForm E M ℝ 0}
    (hf : ω.IsHamiltonianFor Xf f) (hg : ω.IsHamiltonianFor Xg g) :
    poisson Xf g = -poisson Xg f := by
  rw [ω.poisson_eq hf hg, ω.poisson_eq hg hf, interior_interior_swap]

/-- The Hamiltonian vector field of `{f, g}` is `-[X_f, X_g]`; equivalently, `[X_f, X_g]` is the
Hamiltonian field of `-{f, g}`. -/
theorem isHamiltonianFor_bracket {Xf Xg : SmoothVectorField E M} {f g : DifferentialForm E M ℝ 0}
    (hf : ω.IsHamiltonianFor Xf f) (hg : ω.IsHamiltonianFor Xg g) :
    ω.IsHamiltonianFor (Xf.bracket Xg) (-poisson Xf g) := by
  have h := (hf.isSymplecticField).bracket ω hg.isSymplecticField
  rw [IsHamiltonianFor, ω.poisson_eq hf hg, interior_interior_swap, neg_neg]
  exact h

/-- **The Jacobi identity** for the Poisson bracket, in the form
`{f, {g, h}} - {g, {f, h}} = {{f, g}, h}`; here `{{f, g}, h} = -{h, {f, g}}` is computed with
the Hamiltonian field `X_h` of `h`. -/
theorem poisson_jacobi {Xf Xg Xh : SmoothVectorField E M} {f g h : DifferentialForm E M ℝ 0}
    (hf : ω.IsHamiltonianFor Xf f) (hg : ω.IsHamiltonianFor Xg g)
    (hh : ω.IsHamiltonianFor Xh h) :
    poisson Xf (poisson Xg h) - poisson Xg (poisson Xf h) = -poisson Xh (poisson Xf g) := by
  have key : lieDeriv (Xf.bracket Xg) h = -lieDeriv Xh (lieDeriv Xf g) := by
    rw [lieDeriv_zero, ← (hh).eq, interior_interior_swap,
      (ω.isHamiltonianFor_bracket hf hg).eq, poisson, d_neg, interior_neg,
      neg_neg, ← lieDeriv_zero]
    simp only [lieDeriv_zero, d_neg, interior_neg]
  have e : ∀ (X Y : SmoothVectorField E M) (k : DifferentialForm E M ℝ 0),
      poisson X (poisson Y k) = lieDeriv X (lieDeriv Y k) := fun X Y k ↦ by
    simp only [poisson, lieDeriv_neg', neg_neg]
  rw [e, e, e, lieDeriv_lieDeriv_sub, key]

end SymplecticForm

/-! ### Symplectomorphisms -/

section Symplectomorphism

variable {E₀ : Type} [AddCommGroup E₀] [Module ℝ E₀] [TopologicalSpace E₀]
  [IsTopologicalAddGroup E₀] [ContinuousSMul ℝ E₀] [LocallyConvexSpace ℝ E₀] [T2Space E₀]
  {N : Type v} [TopologicalSpace N] [ChartedSpace E₀ N] [MBManifold E₀ N]
  {E₁ : Type} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {P : Type v} [TopologicalSpace P] [ChartedSpace E₁ P] [MBManifold E₁ P]

/-- `φ : N → M` is **symplectic** if `φ*ω = ω₀`. (No invertibility is required; a symplectic
diffeomorphism is a symplectomorphism.) -/
def IsSymplecticMap {φ : N → M} (hφ : SmoothMBM E₀ E φ) (ω₀ : SymplecticForm E₀ N)
    (ω : SymplecticForm E M) : Prop :=
  ω.form.pullback hφ = ω₀.form

theorem isSymplecticMap_id (ω : SymplecticForm E M) :
    IsSymplecticMap (fun k ↦ smoothMBMOn_id (E := E) (M := M) isOpen_univ k) ω ω :=
  pullback_id ω.form

theorem IsSymplecticMap.comp {φ : N → M} {ψ : P → N} {hφ : SmoothMBM E₀ E φ}
    {hψ : SmoothMBM E₁ E₀ ψ} {ω₁ : SymplecticForm E₁ P} {ω₀ : SymplecticForm E₀ N}
    {ω : SymplecticForm E M} (h₁ : IsSymplecticMap hφ ω₀ ω) (h₂ : IsSymplecticMap hψ ω₁ ω₀) :
    IsSymplecticMap (hφ.comp hψ) ω₁ ω := by
  rw [IsSymplecticMap, ← h₂, ← h₁, pullback_pullback]

/-- **Symplectic maps preserve Hamiltonian fields**: if `φ*ω = ω₀`, `X` and `Y` are
`φ`-related and `Y` is the Hamiltonian field of `f`, then `X` is the Hamiltonian field of
`f ∘ φ`. -/
theorem IsSymplecticMap.isHamiltonianFor {φ : N → M} {hφ : SmoothMBM E₀ E φ}
    {ω₀ : SymplecticForm E₀ N} {ω : SymplecticForm E M} (h : IsSymplecticMap hφ ω₀ ω)
    {X : SmoothVectorField E₀ N} {Y : SmoothVectorField E M} (hXY : IsRelated φ X Y)
    {f : DifferentialForm E M ℝ 0} (hY : ω.IsHamiltonianFor Y f) :
    ω₀.IsHamiltonianFor X (f.pullback hφ) := by
  rw [SymplecticForm.IsHamiltonianFor, ← h, ← pullback_interior hφ hXY,
    (hY).eq, d_pullback]

end Symplectomorphism

/-! ### The canonical symplectic form on `H × H` -/

section Canonical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The only chart of the model space is the identity. -/
theorem atlas_self {E : Type} [TopologicalSpace E] (i : atlas E E) :
    i.1 = OpenPartialHomeomorph.refl E :=
  chartedSpaceSelf_atlas.1 i.2

theorem prefChart_self {E : Type} [TopologicalSpace E] (i : atlas E E) (z : E) :
    prefChart (E := E) z = i :=
  Subtype.ext (by rw [atlas_self i]; exact chartAt_self_eq)

/-- On the model space, local representatives of forms are the forms themselves. -/
theorem formLocalRep_self {E : Type} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] {F : Type} {n : ℕ}
    (i : atlas E E) (ω : E → (Fin n → E) → F) (p : E × (Fin n → E)) :
    formLocalRep n i ω p = ω p.1 p.2 := by
  simp only [formLocalRep, atlas_self i, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, id_eq, prefChart_self i]
  congr 1
  funext k
  exact tangentCoordChange_self i (by rw [atlas_self i]; trivial) _

/-- The **Liouville form** on `H × H`, `θ_{(x, a)}(y, b) = ⟨x, b⟩`. -/
def liouvilleForm : DifferentialForm (H × H) (H × H) ℝ 1 where
  toFun x v := inner ℝ x.1 (v 0).2
  alternating' x :=
    ⟨AlternatingMap.ofSubsingleton ℝ (H × H) ℝ 0
      ((innerₛₗ ℝ x.1).comp (LinearMap.snd ℝ H H)), fun v ↦ rfl⟩
  smooth' i := by
    have hU : IsOpen (i.1.target ×ˢ (univ : Set (Fin 1 → H × H))) :=
      i.1.open_target.prod isOpen_univ
    have hs : SmoothMBOn (fun p : (H × H) × (Fin 1 → H × H) ↦ inner ℝ p.1.1 (p.2 0).2)
        (i.1.target ×ˢ univ) := by
      refine (smoothMBOn_iff_contDiffOn hU).2 (ContDiff.contDiffOn ?_)
      have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : (H × H) × (Fin 1 → H × H) ↦ (p.2 0).2 :=
        ((ContinuousLinearMap.snd ℝ H H).comp ((ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin 1 ↦ H × H) 0).comp
            (ContinuousLinearMap.snd ℝ (H × H) (Fin 1 → H × H)))).contDiff
      exact contDiff_inner.comp (contDiff_fst.fst.prodMk h2)
    exact fun k ↦ ContDiffMBOn.congr_of_isOpen hU
      (fun p _ ↦ (formLocalRep_self i (fun x v ↦ inner ℝ x.1 (v 0).2) p).symm) (hs k)

/-- `dθ((y, b), (y', b')) = ⟨y, b'⟩ - ⟨y', b⟩`. -/
theorem liouvilleForm_d_apply (x u w : H × H) :
    (liouvilleForm (H := H)).d x ![u, w] = inner ℝ u.1 w.2 - inner ℝ w.1 u.2 := by
  have key : ∀ a : H × H, ∀ c : H, dMB (fun z : H × H ↦ inner ℝ z.1 c) (x, a) = inner ℝ a.1 c := by
    intro a c
    have e : (fun z : H × H ↦ inner ℝ z.1 c) =
        ⇑((innerSL ℝ c).comp (ContinuousLinearMap.fst ℝ H H)) := by
      funext z; simp [real_inner_comm]
    rw [e, (ContinuousLinearMap.hasDirDerivAt _ x a).dMB_eq]
    simp [real_inner_comm]
  have hrep : ∀ v : Fin 1 → H × H, (fun z ↦ liouvilleForm.localRep (prefChart x) (z, v)) =
      fun z : H × H ↦ inner ℝ z.1 (v 0).2 := fun v ↦ funext fun z ↦
    formLocalRep_self (prefChart x) _ (z, v)
  rw [d_apply, dLoc, Fin.sum_univ_two, chartAt_self_eq]
  simp only [OpenPartialHomeomorph.refl_apply, id_eq]
  rw [hrep, hrep]
  simp [key, sub_eq_add_neg]
  rfl

/-- **The canonical symplectic form** `ω = dθ` on `H × H`, for any real inner product space `H`
(no completeness): `ω((y, b), (y', b')) = ⟨y, b'⟩ - ⟨y', b⟩`. It is exact, hence closed, and
weakly nondegenerate. It is the skew form `Ḡ` induced by the symmetric form
`G = ⟨·, ·⟩` in Marsden (Proc. Amer. Math. Soc. 32 (1972), p. 590). -/
def canonicalSymplectic : SymplecticForm (H × H) (H × H) where
  form := (liouvilleForm (H := H)).d
  isClosed x v := by rw [d_d_eq_zero]; rfl
  nondegenerate x u hu := by
    have h1 := hu (0, u.1)
    have h2 := hu (u.2, 0)
    rw [liouvilleForm_d_apply] at h1 h2
    simp only [inner_zero_left, sub_zero, zero_sub, neg_eq_zero, inner_zero_right,
      real_inner_self_eq_norm_sq] at h1 h2
    exact Prod.ext (by simpa using h1) (by simpa using h2)

theorem canonicalSymplectic_isExact : (canonicalSymplectic (H := H)).form.IsExact :=
  ⟨liouvilleForm, rfl⟩

/-- If `H` is a Hilbert space, the canonical symplectic form is strong (Riesz representation).
For incomplete `H` it is only weakly nondegenerate: `H × H` is then not reflexive, so it carries
no strong symplectic form at all (`IsStrong.surjective_inclusionInDoubleDual`). -/
theorem canonicalSymplectic_isStrong [CompleteSpace H] :
    (canonicalSymplectic (H := H)).IsStrong := by
  intro x φ
  set a₁ := (InnerProductSpace.toDual ℝ H).symm (φ.comp (ContinuousLinearMap.inl ℝ H H))
  set a₂ := (InnerProductSpace.toDual ℝ H).symm (φ.comp (ContinuousLinearMap.inr ℝ H H))
  refine ⟨(a₂, -a₁), fun w ↦ ?_⟩
  change (liouvilleForm (H := H)).d x ![(a₂, -a₁), w] = φ w
  rw [liouvilleForm_d_apply]
  simp only [inner_neg_right, sub_neg_eq_add, a₁, a₂, InnerProductSpace.toDual_symm_apply]
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply, add_comm]
  simp only [ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply]
  rw [← map_add]
  simp

end Canonical

end LocallyConvex.Manifolds

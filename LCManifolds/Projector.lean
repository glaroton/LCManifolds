/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.SubmanifoldNotions
import LCManifolds.Spray
import LCAnalysis.Rules
import LCManifolds.CovariantCurve

/-!
# Derive and project: connections given by a field of projectors

References: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Sección
"La derivada covariante: derivar y proyectar", Teorema *esproyectar*.

Let `X ⊆ F` be an embedded submanifold of a locally convex space `F`, modeled on a closed
subspace `S`. Its tangent space at `p` is a subspace `T_p X ⊆ F`: in any slice chart `φ`,
`T_p X = {w | dφ_p w ∈ S}` (`mem_tangentSpace_iff`). A *field of projectors* is a smooth map
`E : X × F → F`, linear in the second variable, with `E_p² = E_p` and range `T_p X`
(`ProjectorField`). The connection it defines has, in a slice chart with inverse
`ψ = φ⁻¹|_S`, the Christoffel symbols

  `Γ_y(a, b) = - dφ (E (d²ψ_y(a, b)))`,

so that the covariant derivative is "derive in the ambient space and project":
`∇_X Y = E (dY · X)`.

Main results:

* `ProjectorField.connection`: the connection, with symmetric symbols
  (`connection_isSymmetric`); the change of charts law `symb_transition` follows from the
  second-order chain rule `LCAnalysis.dMB_dMB_comp`;
* `ProjectorField.dMB_param_localCovDeriv`: in a slice chart, `dψ (∇_A B) = E (d(dψ · B) · A)`,
  i.e. the covariant derivative is the projection of the ambient derivative;
* `ProjectorField.connection_isGeodesic_iff` (Teorema *esproyectar*): a `C²` curve `α` in `X` is
  a geodesic iff its acceleration in `F` is normal, `E_α (α̈) = 0`.
* `ProjectorField.dMB_localE_param`: the identity of the book, `E_{*p,v} w = (1 - E) d²ψ(a, b)`
  for `v = dψ a`, `w = dψ b`; hence `E_{*p,v} w = E_{*p,w} v` (`dMB_localE_param_symm`).

**Subtleties.**

* In the book `E` is a smooth map `X → 𝓑(F)`. For locally convex `F` there is no good topology
  on the space of operators, so `E` is a map `X × F → F`, linear in the second variable, and its
  smoothness is joint.
* The symmetry of the symbols comes from the symmetry of second derivatives (Schwarz) of `ψ`.
  The book's `Γ_p(v, w) = E_{*p,v} w` is the normal part `(1 - E) d²ψ(a, b)` read in `F`.
* No complement of `S` is needed: the projectors `E_p` themselves provide the complements
  `ker E_p` of the tangent spaces, but they are not assumed to come from a global splitting of
  `F`.
-/

open Set Filter
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

variable {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-! ### Calculus facts -/

omit [LocallyConvexSpace ℝ F] [T2Space F] in
/-- If a `C¹` map sends the points of a closed subspace `S` near `y ∈ S` into `S`, its
derivative at `y` sends `S` into `S`. -/
theorem dMB_mem_of_mapsTo {S : Submodule ℝ F} (hS : IsClosed (S : Set F)) {τ : F → F}
    {T : Set F} (hT : IsOpen T) (hτ : ContDiffMBOn 1 τ T)
    (hmaps : ∀ z ∈ T, z ∈ S → τ z ∈ S) {y : F} (hy : y ∈ T) (hyS : y ∈ S) {s : F}
    (hs : s ∈ S) : dMB τ (y, s) ∈ S := by
  refine hS.mem_of_tendsto (hτ.hasDirDerivAt hy s) ?_
  have hl : Tendsto (fun t : ℝ ↦ y + t • s) (𝓝[≠] 0) (𝓝 y) := by
    have : Continuous fun t : ℝ ↦ y + t • s := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [hl (hT.mem_nhds hy)] with t ht
  exact S.smul_mem _ (S.sub_mem (hmaps _ ht (S.add_mem hyS (S.smul_mem t hs)))
    (hmaps y hy hyS))

/-- A chart of the maximal atlas of `F` is smooth on its source. -/
theorem smoothMBOn_of_mem_maximalAtlas {φ : OpenPartialHomeomorph F F}
    (hφ : φ ∈ (mbGroupoid F).maximalAtlas F) : SmoothMBOn φ φ.source := by
  have h := smoothMBOn_transition_of_mem_maximalAtlas (M := F)
    (StructureGroupoid.id_mem_maximalAtlas (mbGroupoid F)) hφ
  simpa using h

/-- The inverse of a chart of the maximal atlas of `F` is smooth on its target. -/
theorem smoothMBOn_symm_of_mem_maximalAtlas {φ : OpenPartialHomeomorph F F}
    (hφ : φ ∈ (mbGroupoid F).maximalAtlas F) : SmoothMBOn φ.symm φ.target := by
  have h := smoothMBOn_transition_of_mem_maximalAtlas (M := F) hφ
    (StructureGroupoid.id_mem_maximalAtlas (mbGroupoid F))
  simpa using h

/-- `dφ` is a left inverse of `dφ⁻¹`. -/
theorem dMB_chart_dMB_symm {φ : OpenPartialHomeomorph F F}
    (hφ : φ ∈ (mbGroupoid F).maximalAtlas F) {y : F} (hy : y ∈ φ.target) (w : F) :
    dMB φ (φ.symm y, dMB φ.symm (y, w)) = w := by
  have h := dMB_transition_leftInverse (M := F) hφ
    (StructureGroupoid.id_mem_maximalAtlas (mbGroupoid F)) (y := y) (by simpa using hy) w
  simpa using h

/-- `dφ⁻¹` is a left inverse of `dφ`. -/
theorem dMB_symm_dMB_chart {φ : OpenPartialHomeomorph F F}
    (hφ : φ ∈ (mbGroupoid F).maximalAtlas F) {x : F} (hx : x ∈ φ.source) (w : F) :
    dMB φ.symm (φ x, dMB φ (x, w)) = w := by
  have h := dMB_transition_leftInverse (M := F)
    (StructureGroupoid.id_mem_maximalAtlas (mbGroupoid F)) hφ (y := x) (by simpa using hx) w
  simpa using h

/-! ### Tangent spaces of embedded submanifolds of `F` -/

variable {X : Set F} {S : Submodule ℝ F}

/-- For two slice charts at `x`, the derivatives `dφ_x w` and `dφ'_x w` lie in `S` together. -/
theorem dMB_mem_iff_of_isSliceChart (hS : IsClosed (S : Set F))
    {φ φ' : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (hφ' : IsSliceChart X S φ')
    {x : F} (hxX : x ∈ X) (hx : x ∈ φ.source) (hx' : x ∈ φ'.source) (w : F) :
    dMB φ (x, w) ∈ S ↔ dMB φ' (x, w) ∈ S := by
  -- `τ = φ' ∘ φ⁻¹` maps the slice to the slice, and so does its derivative
  have key : ∀ {φ φ' : OpenPartialHomeomorph F F}, IsSliceChart X S φ → IsSliceChart X S φ' →
      x ∈ φ.source → x ∈ φ'.source → dMB φ (x, w) ∈ S → dMB φ' (x, w) ∈ S := by
    intro φ φ' hφ hφ' hx hx' hw
    set T := φ.target ∩ φ.symm ⁻¹' φ'.source
    have hT : IsOpen T := φ.isOpen_inter_preimage_symm φ'.open_source
    have hτ : ContDiffMBOn 1 (φ' ∘ φ.symm) T :=
      smoothMBOn_transition_of_mem_maximalAtlas (M := F) hφ.1 hφ'.1 1
    have hy : φ x ∈ T := ⟨φ.map_source hx, by rw [mem_preimage, φ.left_inv hx]; exact hx'⟩
    have hmaps : ∀ z ∈ T, z ∈ S → (φ' ∘ φ.symm) z ∈ S := by
      intro z hz hzS
      have hzX : φ.symm z ∈ X := (hφ.2 _ (φ.map_target hz.1)).mpr (by rwa [φ.right_inv hz.1])
      exact (hφ'.2 _ hz.2).mp hzX
    have hyS : φ x ∈ S := (hφ.2 x hx).mp hxX
    have hd := dMB_mem_of_mapsTo hS hT hτ hmaps hy hyS hw
    -- `dτ (dφ w) = dφ' w`
    have hsrc : IsOpen (φ.source ∩ φ ⁻¹' T) := φ.isOpen_inter_preimage hT
    have hφs : ContDiffMBOn 1 φ (φ.source ∩ φ ⁻¹' T) :=
      ((smoothMBOn_of_mem_maximalAtlas hφ.1) 1).mono inter_subset_left
    have hev : (φ' ∘ φ.symm) ∘ φ =ᶠ[𝓝 x] φ' :=
      Filter.eventuallyEq_of_mem (φ.open_source.mem_nhds hx) fun z hz ↦ by
        simp [φ.left_inv hz]
    have hxs : x ∈ φ.source ∩ φ ⁻¹' T := ⟨hx, hy⟩
    rw [← ContDiffMBOn.dMB_comp hT hτ hφs (fun z hz ↦ hz.2) hxs w,
      dMB_congr_of_eventuallyEq hev] at hd
    exact hd
  exact ⟨key hφ hφ' hx hx', key hφ' hφ hx' hx⟩

/-- The tangent space `T_p X ⊆ F` of an embedded submanifold, read in the preferred slice chart:
`w ∈ T_p X` iff `dφ_p w ∈ S`. -/
def IsEmbeddedSubmanifold.tangentSpace (h : IsEmbeddedSubmanifold X S) (p : X) : Set F :=
  {w | dMB (h.exists_sliceChart p p.2).choose (p, w) ∈ S}

/-- The tangent space can be read in any slice chart. -/
theorem IsEmbeddedSubmanifold.mem_tangentSpace_iff (h : IsEmbeddedSubmanifold X S) (p : X)
    {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (hp : (p : F) ∈ φ.source)
    (w : F) : w ∈ h.tangentSpace p ↔ dMB φ (p, w) ∈ S :=
  dMB_mem_iff_of_isSliceChart h.isClosed (h.exists_sliceChart p p.2).choose_spec.1 hφ p.2
    (h.exists_sliceChart p p.2).choose_spec.2 hp w

/-- In a slice chart, the tangent space is the image of `S` under `dφ⁻¹`. -/
theorem IsEmbeddedSubmanifold.dMB_symm_mem_tangentSpace (h : IsEmbeddedSubmanifold X S)
    {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (p : X) {y : F}
    (hy : y ∈ φ.target) (hpy : (p : F) = φ.symm y) {s : F} (hs : s ∈ S) :
    dMB φ.symm (y, s) ∈ h.tangentSpace p := by
  have hp : (p : F) ∈ φ.source := by rw [hpy]; exact φ.map_target hy
  rw [h.mem_tangentSpace_iff p hφ hp, hpy, dMB_chart_dMB_symm hφ.1 hy]
  exact hs

/-! ### Fields of projectors -/

/-- A field of projectors onto the tangent spaces of `X`: a map `E : X × F → F`, linear in the
second variable, with `E_p² = E_p` and range `T_p X`, which is smooth in the slice charts. -/
structure ProjectorField (h : IsEmbeddedSubmanifold X S) where
  /-- The projector at `p`, applied to `w`. -/
  E : X → F → F
  map_add : ∀ p w w', E p (w + w') = E p w + E p w'
  map_smul : ∀ p (c : ℝ) w, E p (c • w) = c • E p w
  idem : ∀ p w, E p (E p w) = E p w
  range_eq : ∀ p, Set.range (E p) = h.tangentSpace p
  smooth : ∀ {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (p₀ : X),
    SmoothMBOn (fun q : S × F ↦ E ((sliceChart hφ p₀).symm q.1) q.2)
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ)

namespace ProjectorField

variable {h : IsEmbeddedSubmanifold X S} (P : ProjectorField h)

theorem mem_tangentSpace (p : X) (w : F) : P.E p w ∈ h.tangentSpace p := by
  rw [← P.range_eq]
  exact ⟨w, rfl⟩

theorem E_eq_self {p : X} {w : F} (hw : w ∈ h.tangentSpace p) : P.E p w = w := by
  rw [← P.range_eq] at hw
  obtain ⟨w', rfl⟩ := hw
  exact P.idem p w'

/-- The local parametrization `ψ = φ⁻¹|_S` of `X` in the slice chart `φ`. -/
def param (φ : OpenPartialHomeomorph F F) : S → F := φ.symm ∘ S.subtypeL

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem isOpen_dom (φ : OpenPartialHomeomorph F F) :
    IsOpen (Subtype.val ⁻¹' φ.target : Set S) :=
  φ.open_target.preimage continuous_subtype_val

theorem smoothMBOn_param {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) :
    SmoothMBOn (param φ) (Subtype.val ⁻¹' φ.target : Set S) := fun k ↦
  ((smoothMBOn_symm_of_mem_maximalAtlas hφ.1) k).comp (isOpen_dom φ) φ.open_target
    (S.subtypeL.contDiffMBOn k _) fun _ hy ↦ hy

variable {φ : OpenPartialHomeomorph F F} (hφ : IsSliceChart X S φ) (p₀ : X)

/-- The ambient value of the symbols, `- dφ (E (d²ψ_y(a, b)))`, lies in `S`. -/
theorem symb_mem {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    -dMB φ (φ.symm y, P.E ((sliceChart hφ p₀).symm y) (dMB (dMB (param φ)) ((y, b), (a, 0)))) ∈
      S := by
  apply S.neg_mem
  have hx : (((sliceChart hφ p₀).symm y : X) : F) = φ.symm y := sliceChart_symm_apply_coe hφ p₀ hy
  have hmem := (h.mem_tangentSpace_iff ((sliceChart hφ p₀).symm y) hφ
    (by rw [hx]; exact φ.map_target hy) _).mp (P.mem_tangentSpace ((sliceChart hφ p₀).symm y)
      (dMB (dMB (param φ)) ((y, b), (a, 0))))
  rwa [hx] at hmem

open scoped Classical in
/-- The Christoffel symbols in the slice chart `φ`: `Γ_y(a, b) = - dφ (E (d²ψ_y(a, b)))`,
where `ψ = φ⁻¹|_S`. Outside the chart domain they are set to `0`. -/
def symb (y a b : S) : S :=
  if hy : (y : F) ∈ φ.target then ⟨_, P.symb_mem hφ p₀ hy a b⟩ else 0

theorem coe_symb {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    (P.symb hφ p₀ y a b : F) =
      -dMB φ (φ.symm y,
        P.E ((sliceChart hφ p₀).symm y) (dMB (dMB (param φ)) ((y, b), (a, 0)))) := by
  simp only [symb, hy, ↓reduceDIte]

theorem symb_of_not_mem {y : S} (hy : (y : F) ∉ φ.target) (a b : S) :
    P.symb hφ p₀ y a b = 0 := by
  simp only [symb, hy, ↓reduceDIte]

/-- **The symbols are symmetric**, by the symmetry of the second derivative of `ψ`. -/
theorem symb_symm (y a b : S) : P.symb hφ p₀ y a b = P.symb hφ p₀ y b a := by
  by_cases hy : (y : F) ∈ φ.target
  · refine Subtype.ext ?_
    rw [coe_symb P hφ p₀ hy, coe_symb P hφ p₀ hy,
      ((smoothMBOn_param hφ) 2).dMB_dMB_symm (isOpen_dom φ) hy b a]
  · rw [symb_of_not_mem P hφ p₀ hy, symb_of_not_mem P hφ p₀ hy]

theorem symb_add_left (y a a' b : S) :
    P.symb hφ p₀ y (a + a') b = P.symb hφ p₀ y a b + P.symb hφ p₀ y a' b := by
  by_cases hy : (y : F) ∈ φ.target
  · refine Subtype.ext ?_
    have hφs : ContDiffMBOn 1 φ φ.source := (smoothMBOn_of_mem_maximalAtlas hφ.1) 1
    rw [Submodule.coe_add, coe_symb P hφ p₀ hy, coe_symb P hφ p₀ hy, coe_symb P hφ p₀ hy,
      dMB_dMB_add_left (isOpen_dom φ) ((smoothMBOn_param hφ) 2) hy, P.map_add,
      hφs.dMB_add φ.open_source (φ.map_target hy), neg_add]
  · rw [symb_of_not_mem P hφ p₀ hy, symb_of_not_mem P hφ p₀ hy, symb_of_not_mem P hφ p₀ hy,
      add_zero]

theorem symb_smul_left (y : S) (c : ℝ) (a b : S) :
    P.symb hφ p₀ y (c • a) b = c • P.symb hφ p₀ y a b := by
  by_cases hy : (y : F) ∈ φ.target
  · refine Subtype.ext ?_
    have hφs : ContDiffMBOn 1 φ φ.source := (smoothMBOn_of_mem_maximalAtlas hφ.1) 1
    rw [Submodule.coe_smul, coe_symb P hφ p₀ hy, coe_symb P hφ p₀ hy,
      dMB_dMB_smul_left ((smoothMBOn_param hφ) 2) hy, P.map_smul,
      hφs.dMB_smul (φ.map_target hy), smul_neg]
  · rw [symb_of_not_mem P hφ p₀ hy, symb_of_not_mem P hφ p₀ hy, smul_zero]

theorem symb_add_right (y a b b' : S) :
    P.symb hφ p₀ y a (b + b') = P.symb hφ p₀ y a b + P.symb hφ p₀ y a b' := by
  rw [symb_symm, symb_add_left, symb_symm P hφ p₀ y b, symb_symm P hφ p₀ y b']

theorem symb_smul_right (y : S) (c : ℝ) (a b : S) :
    P.symb hφ p₀ y a (c • b) = c • P.symb hφ p₀ y a b := by
  rw [symb_symm, symb_smul_left, symb_symm P hφ p₀ y b]

/-- **The symbols are smooth** on the chart domain. -/
theorem smoothMBOn_symb :
    SmoothMBOn (fun q : S × (S × S) ↦ P.symb hφ p₀ q.1 q.2.1 q.2.2)
      ((Subtype.val ⁻¹' φ.target : Set S) ×ˢ univ) := by
  intro k
  set D : Set S := Subtype.val ⁻¹' φ.target
  have hD : IsOpen D := isOpen_dom φ
  have hU : IsOpen (D ×ˢ (univ : Set (S × S))) := hD.prod isOpen_univ
  have hψ := smoothMBOn_param hφ
  -- `q ↦ ((y, b), (a, 0))`
  set ι : S × (S × S) →L[ℝ] (S × S) × (S × S) :=
    ((ContinuousLinearMap.fst ℝ S (S × S)).prod
      ((ContinuousLinearMap.snd ℝ S S).comp (ContinuousLinearMap.snd ℝ S (S × S)))).prod
    (((ContinuousLinearMap.fst ℝ S S).comp (ContinuousLinearMap.snd ℝ S (S × S))).prod 0)
  have hd2 : ContDiffMBOn k (dMB (dMB (param φ)) ∘ ι) (D ×ˢ univ) :=
    (hψ (k + 2)).2.2.2.2.comp hU ((hD.prod isOpen_univ).prod isOpen_univ) (ι.contDiffMBOn k _)
      fun q hq ↦ ⟨⟨hq.1, mem_univ _⟩, mem_univ _⟩
  -- `q ↦ E (y) (d²ψ_y(a, b))`
  have hfst : ContDiffMBOn k (fun q : S × (S × S) ↦ q.1) (D ×ˢ univ) :=
    (ContinuousLinearMap.fst ℝ S (S × S)).contDiffMBOn k _
  have hpair := ContDiffMBOn.prodMk hU hfst hd2
  have hE : ContDiffMBOn k (fun q : S × (S × S) ↦
      P.E ((sliceChart hφ p₀).symm q.1) ((dMB (dMB (param φ)) ∘ ι) q)) (D ×ˢ univ) :=
    (P.smooth hφ p₀ k).comp hU (hD.prod isOpen_univ) hpair fun q hq ↦ ⟨hq.1, mem_univ _⟩
  -- `q ↦ dφ (ψ y, …)`
  have hψ1 : ContDiffMBOn k (fun q : S × (S × S) ↦ param φ q.1) (D ×ˢ univ) :=
    ContDiffMBOn.comp (g := param φ) (f := fun q : S × (S × S) ↦ q.1) hU hD (hψ k) hfst
      fun q hq ↦ hq.1
  have hpair' := ContDiffMBOn.prodMk hU hψ1 hE
  have hdφ : ContDiffMBOn k (dMB φ) (φ.source ×ˢ univ) :=
    ((smoothMBOn_of_mem_maximalAtlas hφ.1) (k + 1)).2.2
  have hG := (-ContinuousLinearMap.id ℝ F).contDiffMBOn k univ |>.comp
    hU isOpen_univ (hdφ.comp hU (φ.open_source.prod isOpen_univ) hpair'
      fun q hq ↦ ⟨φ.map_target hq.1, mem_univ _⟩) (mapsTo_univ _ _)
  refine ContDiffMBOn.codRestrict h.isClosed hU hG fun q hq ↦ ?_
  rw [coe_symb P hφ p₀ hq.1]
  rfl

theorem map_sub (p : X) (w w' : F) : P.E p (w - w') = P.E p w - P.E p w' := by
  have := P.map_add p (w - w') w'
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/-- The derivative of a map with values in `S`, read in `F`. -/
theorem coe_dMB_of_subtype {τ : S → S} {W : Set S} (hτ : ContDiffMBOn 1 τ W) {y : S}
    (hy : y ∈ W) (v : S) : ((dMB τ (y, v) : S) : F) = dMB (Subtype.val ∘ τ) (y, v) := by
  have := ContDiffMBOn.dMB_comp isOpen_univ (S.subtypeL.contDiffMBOn 1 univ) hτ
    (mapsTo_univ _ _) hy v
  rw [(S.subtypeL.hasDirDerivAt _ _).dMB_eq] at this
  exact this.symm

/-- **Change of charts law for the symbols** (the `transition` field of a connection). -/
theorem symb_transition {φ' : OpenPartialHomeomorph F F} (hφ' : IsSliceChart X S φ') (p₁ : X)
    {y : S} (hy : y ∈ (sliceChart hφ p₀).target ∩
      (sliceChart hφ p₀).symm ⁻¹' (sliceChart hφ' p₁).source) (a b : S) :
    P.symb hφ' p₁ ((sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) y)
        (dMB (sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) (y, a))
        (dMB (sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) (y, b)) =
      dMB (sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm) (y, P.symb hφ p₀ y a b) +
        dMB (dMB (sliceChart hφ' p₁ ∘ (sliceChart hφ p₀).symm)) ((y, b), (a, 0)) := by
  set e := sliceChart hφ p₀
  set e' := sliceChart hφ' p₁
  set τ : S → S := e' ∘ e.symm
  set W := e.target ∩ e.symm ⁻¹' e'.source
  have hW : IsOpen W := e.isOpen_inter_preimage_symm e'.open_source
  have hτ : SmoothMBOn τ W := by
    have := smoothMBOn_sliceChart_transition h.isClosed hφ hφ' p₀ p₁
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans] at this
  have hφs : ContDiffMBOn 1 φ φ.source := (smoothMBOn_of_mem_maximalAtlas hφ.1) 1
  have hφ's : ContDiffMBOn 1 φ' φ'.source := (smoothMBOn_of_mem_maximalAtlas hφ'.1) 1
  have hφsymm : ContDiffMBOn 1 φ.symm φ.target := (smoothMBOn_symm_of_mem_maximalAtlas hφ.1) 1
  have hφ'symm : ContDiffMBOn 1 φ'.symm φ'.target :=
    (smoothMBOn_symm_of_mem_maximalAtlas hφ'.1) 1
  -- the point `x = e⁻¹ y` of `X`
  set x : X := e.symm y
  have hyT : (y : F) ∈ φ.target := hy.1
  have hx : (x : F) = φ.symm y := sliceChart_symm_apply_coe hφ p₀ hyT
  have hxφ : (x : F) ∈ φ.source := by rw [hx]; exact φ.map_target hyT
  have hφx : φ x = y := by rw [hx, φ.right_inv hyT]
  have hxφ' : (x : F) ∈ φ'.source := hy.2
  have hτy : ((τ y : S) : F) = φ' x := sliceChart_apply_coe hφ' p₁ hxφ'
  have hτyT : ((τ y : S) : F) ∈ φ'.target := by rw [hτy]; exact φ'.map_source hxφ'
  have hxτ : (x : F) = φ'.symm (τ y) := by rw [hτy, φ'.left_inv hxφ']
  have hx' : e'.symm (τ y) = x := e'.left_inv hy.2
  -- `ψ' ∘ τ = ψ` near `y`
  have hψψ' : ∀ z ∈ W, (param φ' ∘ τ) z = param φ z := by
    intro z hz
    change φ'.symm ((e' (e.symm z) : S) : F) = φ.symm z
    rw [sliceChart_apply_coe hφ' p₁ hz.2, φ'.left_inv hz.2, sliceChart_symm_apply_coe hφ p₀ hz.1]
  have hmapsτ : MapsTo τ W (Subtype.val ⁻¹' φ'.target) := fun z hz ↦ e'.map_source hz.2
  -- second derivatives
  have hd2 : dMB (dMB (param φ)) ((y, b), (a, 0)) =
      dMB (dMB (param φ')) ((τ y, dMB τ (y, b)), (dMB τ (y, a), 0)) +
        dMB (param φ') (τ y, dMB (dMB τ) ((y, b), (a, 0))) := by
    rw [← dMB_dMB_comp hW (isOpen_dom φ') ((smoothMBOn_param hφ') 2) (hτ 2) hmapsτ hy a b]
    have hW2 : IsOpen (W ×ˢ (univ : Set S)) := hW.prod isOpen_univ
    have hev : dMB (param φ) =ᶠ[𝓝 (y, b)] dMB (param φ' ∘ τ) :=
      Filter.eventuallyEq_of_mem (hW2.mem_nhds ⟨hy, mem_univ b⟩) fun q hq ↦
        (dMB_congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hW.mem_nhds hq.1)
          fun z hz ↦ (hψψ' z hz).symm) q.2)
    exact dMB_congr_of_eventuallyEq hev _
  -- `dψ'` is `dφ'⁻¹` on `S`
  have hdψ' : ∀ s : S, dMB (param φ') (τ y, s) = dMB φ'.symm ((τ y : F), (s : F)) := by
    intro s
    rw [param, ContDiffMBOn.dMB_comp φ'.open_target hφ'symm
      (S.subtypeL.contDiffMBOn 1 (Subtype.val ⁻¹' φ'.target)) (fun z hz ↦ hz)
      (show τ y ∈ (Subtype.val ⁻¹' φ'.target : Set S) from hτyT) s,
      (S.subtypeL.hasDirDerivAt _ _).dMB_eq]
    rfl
  -- the normal correction `n = dψ'(d²τ)` is tangent, so `E` fixes it
  set s := dMB (dMB τ) ((y, b), (a, 0))
  have hn : P.E x (dMB (param φ') (τ y, s)) = dMB (param φ') (τ y, s) := by
    rw [hdψ']
    exact P.E_eq_self (h.dMB_symm_mem_tangentSpace hφ' x hτyT hxτ s.2)
  have hn' : dMB φ' ((x : F), dMB (param φ') (τ y, s)) = s := by
    rw [hdψ', hxτ, dMB_chart_dMB_symm hφ'.1 hτyT]
  -- `dτ` read in `F`: `dτ(y, v) = dφ'(x, dφ⁻¹(y, v))`
  have hdτ : ∀ v : S,
      ((dMB τ (y, v) : S) : F) = dMB φ' ((x : F), dMB φ.symm ((y : F), (v : F))) := by
    intro v
    rw [coe_dMB_of_subtype ((hτ 1)) hy v]
    have hT : IsOpen (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
      φ.isOpen_inter_preimage_symm φ'.open_source
    have hev : Subtype.val ∘ τ =ᶠ[𝓝 y] (φ' ∘ φ.symm) ∘ S.subtypeL :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hy) fun z hz ↦ by
        change ((e' (e.symm z) : S) : F) = φ' (φ.symm z)
        rw [sliceChart_apply_coe hφ' p₁ hz.2, sliceChart_symm_apply_coe hφ p₀ hz.1]
    have hyT' : (y : F) ∈ φ.target ∩ φ.symm ⁻¹' φ'.source :=
      ⟨hyT, by rw [mem_preimage, ← hx]; exact hxφ'⟩
    have hcomp : ContDiffMBOn 1 (φ' ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
      smoothMBOn_transition_of_mem_maximalAtlas (M := F) hφ.1 hφ'.1 1
    rw [dMB_congr_of_eventuallyEq hev, ContDiffMBOn.dMB_comp hT hcomp
      (S.subtypeL.contDiffMBOn 1 (Subtype.val ⁻¹' (φ.target ∩ φ.symm ⁻¹' φ'.source)))
      (fun z hz ↦ hz)
      (show y ∈ (Subtype.val ⁻¹' (φ.target ∩ φ.symm ⁻¹' φ'.source) : Set S) from hyT') v,
      (S.subtypeL.hasDirDerivAt _ _).dMB_eq]
    change dMB (φ' ∘ φ.symm) ((y : F), (v : F)) = _
    rw [ContDiffMBOn.dMB_comp φ'.open_source hφ's (hφsymm.mono inter_subset_left)
      (fun z hz ↦ hz.2) hyT' v, ← hx]
  -- linear maps
  obtain ⟨Lφ', hLφ'⟩ := hφ's.exists_clm φ'.open_source hxφ'
  obtain ⟨Lφs, hLφs⟩ := hφsymm.exists_clm φ.open_target hyT
  -- now compare in `F`
  refine Subtype.ext ?_
  rw [Submodule.coe_add, coe_symb P hφ' p₁ hτyT, hdτ, coe_symb P hφ p₀ hyT, hx', ← hxτ, ← hx,
    show (sliceChart hφ p₀).symm y = x from rfl]
  have hd2' : dMB (dMB (param φ')) ((τ y, dMB τ (y, b)), (dMB τ (y, a), 0)) =
      dMB (dMB (param φ)) ((y, b), (a, 0)) - dMB (param φ') (τ y, s) := by
    rw [hd2, add_sub_cancel_right]
  set w := P.E x (dMB (dMB (param φ)) ((y, b), (a, 0)))
  have hsym : dMB φ.symm ((y : F), -dMB φ ((x : F), w)) = -w := by
    rw [← hLφs, map_neg, hLφs, ← hφx, dMB_symm_dMB_chart hφ.1 hxφ]
  rw [hd2', P.map_sub, hn, hsym]
  simp only [← hLφ', map_neg]
  rw [show P.E x (dMB (dMB (param φ)) ((y, b), (a, 0))) = w from rfl, _root_.map_sub,
    hLφ' (dMB (param φ') (τ y, s)), hn']
  abel

/-! ### Derive and project -/

include hφ in
/-- `dψ` is `dφ⁻¹` on `S`. -/
theorem dMB_param {y : S} (hy : (y : F) ∈ φ.target) (s : S) :
    dMB (param φ) (y, s) = dMB φ.symm ((y : F), (s : F)) := by
  have hφsymm : ContDiffMBOn 1 φ.symm φ.target := (smoothMBOn_symm_of_mem_maximalAtlas hφ.1) 1
  rw [param, ContDiffMBOn.dMB_comp φ.open_target hφsymm
    (S.subtypeL.contDiffMBOn 1 (Subtype.val ⁻¹' φ.target)) (fun z hz ↦ hz)
    (show y ∈ (Subtype.val ⁻¹' φ.target : Set S) from hy) s,
    (S.subtypeL.hasDirDerivAt _ _).dMB_eq]
  rfl

/-- The image of `dψ` is tangent, so the projector fixes it. -/
theorem E_dMB_param {y : S} (hy : (y : F) ∈ φ.target) (s : S) :
    P.E ((sliceChart hφ p₀).symm y) (dMB (param φ) (y, s)) = dMB (param φ) (y, s) := by
  rw [dMB_param hφ hy]
  exact P.E_eq_self (h.dMB_symm_mem_tangentSpace hφ _ hy (sliceChart_symm_apply_coe hφ p₀ hy) s.2)

/-- `dψ (Γ_y(a, b)) = - E (d²ψ_y(a, b))`. -/
theorem dMB_param_symb {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    dMB (param φ) (y, P.symb hφ p₀ y a b) =
      -P.E ((sliceChart hφ p₀).symm y) (dMB (dMB (param φ)) ((y, b), (a, 0))) := by
  have hφsymm : ContDiffMBOn 1 φ.symm φ.target := (smoothMBOn_symm_of_mem_maximalAtlas hφ.1) 1
  obtain ⟨L, hL⟩ := hφsymm.exists_clm φ.open_target hy
  rw [dMB_param hφ hy, coe_symb P hφ p₀ hy, ← hL, map_neg, hL]
  have := dMB_symm_dMB_chart hφ.1 (φ.map_target hy)
    (P.E ((sliceChart hφ p₀).symm y) (dMB (dMB (param φ)) ((y, b), (a, 0))))
  rw [φ.right_inv hy] at this
  rw [this]

include hφ in
/-- `dψ_y` is injective on `S`. -/
theorem dMB_param_injective {y : S} (hy : (y : F) ∈ φ.target) :
    Function.Injective fun s : S ↦ dMB (param φ) (y, s) := by
  intro s s' hss'
  have hss : dMB (param φ) (y, s) = dMB (param φ) (y, s') := hss'
  rw [dMB_param hφ hy, dMB_param hφ hy] at hss
  have h1 := dMB_chart_dMB_symm hφ.1 hy s
  rw [hss, dMB_chart_dMB_symm hφ.1 hy] at h1
  exact Subtype.ext h1.symm

/-- **Derive in the ambient space and project** (Remark after Teorema *esproyectar*): in a slice
chart, the covariant derivative of `B` along `A`, pushed to `F` by `dψ`, is the projection of
the ambient derivative of the field `y ↦ dψ_y (B y)`. -/
theorem dMB_param_localCovDeriv {A B : S → S} {U : Set S} (hU : IsOpen U)
    (hUd : U ⊆ (Subtype.val ⁻¹' φ.target : Set S)) (hB : ContDiffMBOn 1 B U) {y : S}
    (hy : y ∈ U) :
    dMB (param φ) (y, localCovDeriv (P.symb hφ p₀) A B y) =
      P.E ((sliceChart hφ p₀).symm y) (dMB (fun y' ↦ dMB (param φ) (y', B y')) (y, A y)) := by
  have hyd : (y : F) ∈ φ.target := hUd hy
  rw [dMB_dMB_comp_apply (isOpen_dom φ) hU hUd ((smoothMBOn_param hφ) 2) hB hy (A y),
    P.map_add, E_dMB_param P hφ p₀ hyd, localCovDeriv]
  obtain ⟨L, hL⟩ := ((smoothMBOn_param hφ) 1).exists_clm (isOpen_dom φ) hyd
  rw [← hL, _root_.map_sub, hL, hL, dMB_param_symb P hφ p₀ hyd]
  abel

/-- **Geodesics have normal acceleration**, in a slice chart: for a curve `c` in the chart
domain, with `α = ψ ∘ c`, `E (α̈) = dψ (c̈ - Γ(ċ, ċ))`. -/
theorem E_accel_eq {c : ℝ → S} {O : Set ℝ} (hO : IsOpen O) (hc : ContDiffMBOn 2 c O)
    (hcd : MapsTo c O (Subtype.val ⁻¹' φ.target)) {t : ℝ} (ht : t ∈ O) :
    P.E ((sliceChart hφ p₀).symm (c t)) (dMB (fun s ↦ dMB (param φ ∘ c) (s, 1)) (t, 1)) =
      dMB (param φ) (c t, dMB (fun s ↦ dMB c (s, 1)) (t, 1) -
        P.symb hφ p₀ (c t) (dMB c (t, 1)) (dMB c (t, 1))) := by
  have hyd : ((c t : S) : F) ∈ φ.target := hcd ht
  have hψ := smoothMBOn_param hφ
  have hc1 : ContDiffMBOn 1 c O := hc.of_le (by norm_num)
  -- the velocity of `ψ ∘ c`
  have hev : (fun s ↦ dMB (param φ ∘ c) (s, 1)) =ᶠ[𝓝 t]
      fun s ↦ dMB (param φ) (c s, dMB c (s, 1)) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds ht) fun s hs ↦
      ContDiffMBOn.dMB_comp (isOpen_dom φ) (hψ 1) hc1 hcd hs 1
  have hdc : ContDiffMBOn 1 (fun s ↦ dMB c (s, 1)) O := by
    have h2 : ContDiffMBOn 1 (dMB c) (O ×ˢ univ) := hc.2.2
    have hpair : ContDiffMBOn 1 (fun s : ℝ ↦ (s, (1 : ℝ))) O :=
      ((ContinuousLinearMap.id ℝ ℝ).contDiffMBOn 1 _).prodMk hO (contDiffMBOn_const 1 1 _)
    exact ContDiffMBOn.comp (g := dMB c) (f := fun s : ℝ ↦ (s, (1 : ℝ))) hO
      (hO.prod isOpen_univ) h2 hpair fun s hs ↦ ⟨hs, mem_univ _⟩
  rw [dMB_congr_of_eventuallyEq hev,
    dMB_dMB_curve (isOpen_dom φ) hO (hψ 2) hc1 hdc hcd ht, P.map_add, E_dMB_param P hφ p₀ hyd]
  obtain ⟨L, hL⟩ := (hψ 1).exists_clm (isOpen_dom φ) hyd
  simp only [← hL, _root_.map_sub]
  rw [hL (P.symb hφ p₀ (c t) _ _), dMB_param_symb P hφ p₀ hyd]
  abel

/-- The projector field read in the slice chart: `Ê(y, w) = E_{e⁻¹ y} w`. -/
def localE (y : S) (w : F) : F := P.E ((sliceChart hφ p₀).symm y) w

/-- **The identity of the book**: the derivative of `E` along `v = dψ a`, applied to
`w = dψ b`, is the normal part of the second derivative,
`E_{*p,v} w = (1 - E) d²ψ_y(a, b)`. -/
theorem dMB_localE_param {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    dMB (fun q : S × F ↦ P.localE hφ p₀ q.1 q.2) ((y, dMB (param φ) (y, b)), (a, 0)) =
      dMB (dMB (param φ)) ((y, b), (a, 0)) -
        P.E ((sliceChart hφ p₀).symm y) (dMB (dMB (param φ)) ((y, b), (a, 0))) := by
  set D : Set S := Subtype.val ⁻¹' φ.target
  have hD : IsOpen D := isOpen_dom φ
  have hψ := smoothMBOn_param hφ
  set Ê : S × F → F := fun q ↦ P.localE hφ p₀ q.1 q.2
  have hÊ : ContDiffMBOn 1 Ê (D ×ˢ univ) := P.smooth hφ p₀ 1
  -- `Φ y' = (y', dψ_{y'} b)`
  have hdψ : ContDiffMBOn 1 (dMB (param φ)) (D ×ˢ univ) := (hψ 2).2.2
  have hpair : ContDiffMBOn 1 (fun y' : S ↦ (y', b)) D :=
    ((ContinuousLinearMap.id ℝ S).contDiffMBOn 1 D).prodMk hD (contDiffMBOn_const 1 b D)
  have hdb : ContDiffMBOn 1 (fun y' : S ↦ dMB (param φ) (y', b)) D :=
    ContDiffMBOn.comp (g := dMB (param φ)) (f := fun y' : S ↦ (y', b)) hD
      (hD.prod isOpen_univ) hdψ hpair fun y' hy' ↦ ⟨hy', mem_univ _⟩
  have hΦ : ContDiffMBOn 1 (fun y' : S ↦ (y', dMB (param φ) (y', b))) D :=
    ((ContinuousLinearMap.id ℝ S).contDiffMBOn 1 D).prodMk hD hdb
  have hΦmaps : MapsTo (fun y' : S ↦ (y', dMB (param φ) (y', b))) D (D ×ˢ univ) :=
    fun y' hy' ↦ ⟨hy', mem_univ _⟩
  -- `Ê ∘ Φ = dψ(·) b` on `D`, since `dψ b` is tangent
  have hev : Ê ∘ (fun y' : S ↦ (y', dMB (param φ) (y', b))) =ᶠ[𝓝 y]
      fun y' ↦ dMB (param φ) (y', b) :=
    Filter.eventuallyEq_of_mem (hD.mem_nhds hy) fun y' hy' ↦ P.E_dMB_param hφ p₀ hy' b
  have hcomp := ContDiffMBOn.dMB_comp (hD.prod isOpen_univ) hÊ hΦ hΦmaps hy a
  rw [dMB_congr_of_eventuallyEq hev] at hcomp
  -- the derivative of `Φ`
  have hdΦ : dMB (fun y' : S ↦ (y', dMB (param φ) (y', b))) (y, a) =
      (a, dMB (dMB (param φ)) ((y, b), (a, 0))) := by
    change dMB (fun w ↦ ((ContinuousLinearMap.id ℝ S) w, dMB (param φ) (w, b))) (y, a) = _
    rw [(((ContinuousLinearMap.id ℝ S).hasDirDerivAt y a).prodMk
      (hdb.hasDirDerivAt hy a)).dMB_eq, dMB_slice]
    rfl
  -- `Ê` is linear in the second variable: its derivative in `(0, d)` is `E d`
  set x := (sliceChart hφ p₀).symm y
  have hcont : Continuous fun w : F ↦ P.E x w :=
    hÊ.continuousOn.comp_continuous (by fun_prop : Continuous fun w : F ↦ (y, w))
      fun w ↦ (⟨hy, mem_univ w⟩ : (y, w) ∈ D ×ˢ (univ : Set F))
  let L : F →L[ℝ] F :=
    { toFun := P.E x
      map_add' := P.map_add x
      map_smul' := P.map_smul x
      cont := hcont }
  have hsplit : (a, dMB (dMB (param φ)) ((y, b), (a, 0))) =
      (a, (0 : F)) + (0, dMB (dMB (param φ)) ((y, b), (a, 0))) := by simp
  have hmem : (y, dMB (param φ) (y, b)) ∈ D ×ˢ (univ : Set F) := ⟨hy, mem_univ _⟩
  rw [hdΦ, hsplit, hÊ.dMB_add (hD.prod isOpen_univ) hmem, dMB_slice₂] at hcomp
  have hlin : (fun w ↦ Ê (y, w)) = ⇑L := rfl
  rw [hlin, (L.hasDirDerivAt _ _).dMB_eq] at hcomp
  rw [← dMB_slice (dMB (param φ)) y a b] at hcomp
  exact eq_sub_of_add_eq hcomp.symm

/-- **The symmetry of the book**: `E_{*p,v} w = E_{*p,w} v` for tangent vectors `v = dψ a`,
`w = dψ b`. -/
theorem dMB_localE_param_symm {y : S} (hy : (y : F) ∈ φ.target) (a b : S) :
    dMB (fun q : S × F ↦ P.localE hφ p₀ q.1 q.2) ((y, dMB (param φ) (y, b)), (a, 0)) =
      dMB (fun q : S × F ↦ P.localE hφ p₀ q.1 q.2) ((y, dMB (param φ) (y, a)), (b, 0)) := by
  rw [P.dMB_localE_param hφ p₀ hy, P.dMB_localE_param hφ p₀ hy,
    ((smoothMBOn_param hφ) 2).dMB_dMB_symm (isOpen_dom φ) hy b a]

/-- **The connection defined by a field of projectors** (Teorema *esproyectar*): in the slice
chart `φ`, its symbols are `Γ_y(a, b) = - dφ (E (d²ψ_y(a, b)))`, `ψ = φ⁻¹|_S`. -/
def connection : letI := h.chartedSpace; haveI := h.mbManifold; Connection S X := by
  let := h.chartedSpace
  have := h.mbManifold
  exact
  { Γ := fun i ↦ P.symb i.2.choose_spec.choose i.2.choose_spec.choose_spec.choose
    smooth := fun i ↦ by
      have hi : (i : OpenPartialHomeomorph X S) =
          sliceChart i.2.choose_spec.choose i.2.choose_spec.choose_spec.choose :=
        i.2.choose_spec.choose_spec.choose_spec
      rw [congrArg (fun e : OpenPartialHomeomorph X S ↦ e.target) hi]
      exact P.smoothMBOn_symb _ _
    add_left := fun i ↦ P.symb_add_left _ _
    smul_left := fun i ↦ P.symb_smul_left _ _
    add_right := fun i ↦ P.symb_add_right _ _
    smul_right := fun i ↦ P.symb_smul_right _ _
    transition := fun i j y hy a b ↦ by
      have hi : (i : OpenPartialHomeomorph X S) =
          sliceChart i.2.choose_spec.choose i.2.choose_spec.choose_spec.choose :=
        i.2.choose_spec.choose_spec.choose_spec
      have hj : (j : OpenPartialHomeomorph X S) =
          sliceChart j.2.choose_spec.choose j.2.choose_spec.choose_spec.choose :=
        j.2.choose_spec.choose_spec.choose_spec
      have key := P.symb_transition i.2.choose_spec.choose i.2.choose_spec.choose_spec.choose
        j.2.choose_spec.choose j.2.choose_spec.choose_spec.choose (y := y)
        (by rw [← hi, ← hj]; exact hy) a b
      rw [← hi, ← hj] at key
      exact key }

/-- The symbols of the connection are symmetric: it is torsion free. -/
theorem connection_isSymmetric :
    letI := h.chartedSpace; haveI := h.mbManifold; (P.connection).IsSymmetric := by
  let := h.chartedSpace
  have := h.mbManifold
  intro i x a b
  exact P.symb_symm _ _ x a b

include hφ in
theorem dMB_param_zero {y : S} (hy : (y : F) ∈ φ.target) : dMB (param φ) (y, 0) = 0 := by
  obtain ⟨L, hL⟩ := ((smoothMBOn_param hφ) 1).exists_clm (isOpen_dom φ) hy
  rw [← hL, map_zero]

/-- Facts about a chart of `X` given as a slice chart. -/
theorem sliceChart_facts {e : OpenPartialHomeomorph X S} (he : e = sliceChart hφ p₀) {q : X}
    (hq : q ∈ e.source) :
    ((e q : S) : F) = φ q ∧ (q : F) ∈ φ.source ∧ (sliceChart hφ p₀).symm (e q) = q ∧
      ((e q : S) : F) ∈ φ.target := by
  subst he
  exact ⟨sliceChart_apply_coe hφ p₀ hq, hq, (sliceChart hφ p₀).left_inv hq,
    (sliceChart hφ p₀).map_source hq⟩

/-- **Teorema *esproyectar***: the geodesics of the connection defined by a field of projectors
are the curves with normal acceleration, `E_α (α̈) = 0`, where `α̈` is the acceleration in `F`. -/
theorem connection_isGeodesic_iff {α : ℝ → X} (hα : letI := h.chartedSpace; IsCkCurve S 2 α) :
    letI := h.chartedSpace; haveI := h.mbManifold
    P.connection.IsGeodesic α ↔
      ∀ t, P.E (α t) (dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1)) = 0 := by
  let := h.chartedSpace
  have := h.mbManifold
  rw [P.connection.isGeodesic_iff hα]
  -- in a chart `j`, `E (α̈) = dψ (c̈ - Γ(ċ, ċ))`, with `c = j ∘ α`
  have key : ∀ (j : atlas S X) (t : ℝ), α t ∈ j.1.source →
      P.E (α t) (dMB (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) (t, 1)) =
        dMB (param j.2.choose) (j.1 (α t), dMB (fun s ↦ dMB (j.1 ∘ α) (s, 1)) (t, 1) -
          P.connection.Γ j (j.1 (α t)) (dMB (j.1 ∘ α) (t, 1)) (dMB (j.1 ∘ α) (t, 1))) := by
    intro j t ht
    have hj : (j : OpenPartialHomeomorph X S) =
        sliceChart j.2.choose_spec.choose j.2.choose_spec.choose_spec.choose :=
      j.2.choose_spec.choose_spec.choose_spec
    set φj := j.2.choose
    set hφj := j.2.choose_spec.choose
    set pj := j.2.choose_spec.choose_spec.choose
    set O := α ⁻¹' (j : OpenPartialHomeomorph X S).source
    have hO : IsOpen O := (j : OpenPartialHomeomorph X S).open_source.preimage hα.1
    have hc : ContDiffMBOn 2 ((j : OpenPartialHomeomorph X S) ∘ α) O := hα.2 j
    -- values of the chart
    have hval : ∀ q ∈ (j : OpenPartialHomeomorph X S).source,
        (((j : OpenPartialHomeomorph X S) q : S) : F) = φj q ∧ (q : F) ∈ φj.source :=
      fun q hq ↦ ⟨(sliceChart_facts hφj pj hj hq).1, (sliceChart_facts hφj pj hj hq).2.1⟩
    have hcd : MapsTo ((j : OpenPartialHomeomorph X S) ∘ α) O
        (Subtype.val ⁻¹' φj.target) := by
      intro s hs
      change (((j : OpenPartialHomeomorph X S) (α s) : S) : F) ∈ φj.target
      rw [(hval _ hs).1]
      exact φj.map_source (hval _ hs).2
    -- `val ∘ α = ψ ∘ c` on `O`
    have hamb : ∀ s ∈ O, (Subtype.val ∘ α) s =
        (param φj ∘ ((j : OpenPartialHomeomorph X S) ∘ α)) s := by
      intro s hs
      change ((α s : X) : F) = φj.symm (((j : OpenPartialHomeomorph X S) (α s) : S) : F)
      rw [(hval _ hs).1, φj.left_inv (hval _ hs).2]
    have hev : (fun s ↦ dMB (Subtype.val ∘ α) (s, 1)) =ᶠ[𝓝 t]
        fun s ↦ dMB (param φj ∘ ((j : OpenPartialHomeomorph X S) ∘ α)) (s, 1) :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds ht) fun s hs ↦
        dMB_congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hO.mem_nhds hs) hamb) 1
    have hpt : (sliceChart hφj pj).symm ((j : OpenPartialHomeomorph X S) (α t)) = α t :=
      (sliceChart_facts hφj pj hj ht).2.2.1
    have hacc := P.E_accel_eq hφj pj hO hc hcd ht
    simp only [Function.comp_apply] at hacc
    rw [hpt] at hacc
    rw [dMB_congr_of_eventuallyEq hev, hacc]
    rfl
  -- conclude
  constructor
  · intro hgeo t
    set j : atlas S X := ⟨chartAt S (α t), chart_mem_atlas S (α t)⟩
    have ht : α t ∈ j.1.source := mem_chart_source S (α t)
    have hj : (j : OpenPartialHomeomorph X S) =
        sliceChart j.2.choose_spec.choose j.2.choose_spec.choose_spec.choose :=
      j.2.choose_spec.choose_spec.choose_spec
    have hyT : (((j : OpenPartialHomeomorph X S) (α t) : S) : F) ∈ j.2.choose.target :=
      (sliceChart_facts j.2.choose_spec.choose _ hj ht).2.2.2
    rw [key j t ht, hgeo j t ht, sub_self,
      dMB_param_zero j.2.choose_spec.choose hyT]
  · intro hE j t ht
    have hj : (j : OpenPartialHomeomorph X S) =
        sliceChart j.2.choose_spec.choose j.2.choose_spec.choose_spec.choose :=
      j.2.choose_spec.choose_spec.choose_spec
    have hyT : (((j : OpenPartialHomeomorph X S) (α t) : S) : F) ∈ j.2.choose.target :=
      (sliceChart_facts j.2.choose_spec.choose _ hj ht).2.2.2
    have h0 := key j t ht
    rw [hE t, ← dMB_param_zero j.2.choose_spec.choose hyT] at h0
    exact sub_eq_zero.mp (dMB_param_injective j.2.choose_spec.choose hyT h0).symm

end ProjectorField

end LCManifolds

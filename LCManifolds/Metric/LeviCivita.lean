/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.Connection
import LCManifolds.Metric.Bilinear

/-!
# The Levi-Civita connection: Koszul formula and uniqueness

References: S. Lang, *Fundamentals of Differential Geometry*, Ch. VIII, §4, Theorem 4.1
(metric derivative) and Theorem 4.2, condition MS 1 (metric spray), for pseudo-Riemannian
metrics in Lang's sense; G. Larotonda, *Estructuras geométricas para las variedades de Banach*,
§10.1, Teorema 10.1.1 (metric spray, pseudo-Riemannian case); A. Schmeding, *An introduction to
infinite-dimensional differential geometry*, arXiv:2112.08114v3, §4.3: Def. 4.3.6 (metric
spray), Example 4.3.7 (a weak Riemannian metric on `ℓ²` without metric spray), 4.3.14 (metric
derivative).

Let `g` be a smooth field of symmetric bilinear forms (`SymmBilinField`) of **any signature**:
Riemannian, Lorentzian, or pseudo-Riemannian of finite or infinite index. A connection `C` is
**metric** for `g` (`Connection.IsMetric`) if in every chart

`∂G(y)(u)(a, b) = − G(y)(Γ(y)(u, a), b) − G(y)(a, Γ(y)(u, b))`,

where `G(y)(a, b)` is the local representative of `g` and `∂G(y)(u)` its derivative in the base
point, in the direction `u`. With the convention `∇_X Y = dỸ · X̃ − Γ(X̃, Ỹ)` of
`LCManifolds.Connection`, this is the chart expression of `X g(Y, Z) = g(∇_X Y, Z) + g(Y, ∇_X Z)`.

## Main results

* `koszul_eq`, `Connection.koszul`: **the Koszul formula.** If `C` is symmetric and metric,
  `G(Γ(u, a), b) = ½ (−∂G(u)(a, b) − ∂G(a)(u, b) + ∂G(b)(u, a))`. This is pure algebra in each
  chart: no completeness, no nondegeneracy.
* `Connection.Γ_eq_of_isMetric`: **uniqueness.** If `g` is weakly nondegenerate, two symmetric
  metric connections have the same symbols in every chart. This covers weak Riemannian metrics
  and weak pseudo-Riemannian metrics of arbitrary index (`WeakPseudoRiemannianMetric.Γ_eq`).
* `Connection.isMetric_iff_spray`: **the metric spray.** A symmetric connection is metric if and
  only if its spray `F(v) = Γ(v, v)` satisfies, in every chart,
  `G(F(v), z) = −∂G(v)(v, z) + ½ ∂G(z)(v, v)` (Larotonda, *Estructuras*, Teorema 10.1.1,
  formulas (10.3)–(10.4)). The symbols are recovered from the spray by polarization
  (`koszul_of_spray`); the additivity of `∂G(y)` in each argument, needed for this, is
  `SymmBilinField.localDeriv_add_left` and its companions.
* `exists_symm_compatible_iff`: **the obstruction to existence**, pointwise. Symbols that are
  symmetric and compatible with `G` at a point exist if and only if, for all `u, a`, the
  functional `b ↦ koszul(u, a, b)` is represented by `G`: `koszul(u, a, ·) = G(c, ·)`.

## Existence: a word of caution

For a strong Riemannian metric on a Hilbert manifold, the Koszul functional is always
represented (Riesz), and the Levi-Civita connection exists (Lang, Ch. VIII, Theorem 4.1). For **weak**
metrics, in particular on Fréchet manifolds, where every metric is weak, the representation may
fail: Schmeding's Example 4.3.7 is a weak Riemannian metric on `ℓ²` whose Koszul functional is
not represented, so that there is no metric spray. Even when the functional is represented at
every point, the symbols so obtained still have to be smooth and to satisfy the change of charts
law of a connection, and neither follows from the pointwise statement. We therefore do not state
an existence theorem: existence is a property of the metric at hand, to be checked in examples.
-/

open Set Filter Bundle
open scoped Topology Manifold
open LCAnalysis

noncomputable section

namespace LCManifolds

universe u

/-! ### The Koszul formula: pointwise algebra -/

section Koszul

variable {E : Type*} [AddCommGroup E]

/-- The **Koszul expression** of a trilinear expression `D u a b` (to be thought of as the
derivative `∂G(u)(a, b)` of a field of bilinear forms):
`½ (−D(u)(a, b) − D(a)(u, b) + D(b)(u, a))`. -/
def koszul (D : E → E → E → ℝ) (u a b : E) : ℝ := (-D u a b - D a u b + D b u a) / 2

omit [AddCommGroup E] in
/-- **Koszul formula.** If `Γ` is symmetric and `D(u)(a, b) = −B(Γ(u, a), b) − B(a, Γ(u, b))`
for a symmetric `B`, then `B(Γ(u, a), b)` is the Koszul expression of `D`. -/
theorem koszul_eq {B : E → E → ℝ} {D : E → E → E → ℝ} {Γ : E → E → E}
    (hB : ∀ a b, B a b = B b a) (hΓ : ∀ u a, Γ u a = Γ a u)
    (hD : ∀ u a b, D u a b = -B (Γ u a) b - B a (Γ u b)) (u a b : E) :
    B (Γ u a) b = koszul D u a b := by
  simp only [koszul, hD]
  rw [hB a (Γ u b), hB u (Γ a b), hB u (Γ b a), hΓ a u, hΓ b u, hΓ b a]
  ring

/-- **Uniqueness.** If `B` is weakly nondegenerate, the symbols are determined by `D`. -/
theorem eq_of_koszul {B : E → E → ℝ} {D : E → E → E → ℝ} {Γ Γ' : E → E → E}
    (hB : ∀ a b, B a b = B b a) (hsub : ∀ c c' b, B (c - c') b = B c b - B c' b)
    (hnd : ∀ c, (∀ b, B c b = 0) → c = 0)
    (hΓ : ∀ u a, Γ u a = Γ a u) (hD : ∀ u a b, D u a b = -B (Γ u a) b - B a (Γ u b))
    (hΓ' : ∀ u a, Γ' u a = Γ' a u) (hD' : ∀ u a b, D u a b = -B (Γ' u a) b - B a (Γ' u b))
    (u a : E) : Γ u a = Γ' u a :=
  sub_eq_zero.mp <| hnd _ fun b ↦ by
    rw [hsub, koszul_eq hB hΓ hD, koszul_eq hB hΓ' hD', sub_self]

/-- **The obstruction to existence.** Let `B` be symmetric and weakly nondegenerate, and `D`
symmetric in its last two arguments. Symbols `Γ` that are symmetric and compatible with `B` exist
if and only if every Koszul functional `b ↦ koszul D u a b` is represented by `B`. -/
theorem exists_symm_compatible_iff {B : E → E → ℝ} {D : E → E → E → ℝ}
    (hB : ∀ a b, B a b = B b a) (hsub : ∀ c c' b, B (c - c') b = B c b - B c' b)
    (hnd : ∀ c, (∀ b, B c b = 0) → c = 0) (hDsymm : ∀ u a b, D u a b = D u b a) :
    (∃ Γ : E → E → E, (∀ u a, Γ u a = Γ a u) ∧
        ∀ u a b, D u a b = -B (Γ u a) b - B a (Γ u b)) ↔
      ∀ u a, ∃ c, ∀ b, B c b = koszul D u a b := by
  constructor
  · rintro ⟨Γ, hΓ, hD⟩ u a
    exact ⟨Γ u a, koszul_eq hB hΓ hD u a⟩
  · intro h
    choose Γ hΓ using h
    refine ⟨Γ, fun u a ↦ ?_, fun u a b ↦ ?_⟩
    · refine sub_eq_zero.mp <| hnd _ fun b ↦ ?_
      rw [hsub, hΓ, hΓ, koszul, koszul, hDsymm b u a]
      ring
    · rw [hΓ, hB a, hΓ, koszul, koszul, hDsymm u b a]
      ring

omit [AddCommGroup E] in
/-- On the diagonal, the Koszul expression is the **metric spray**:
`koszul(v, v, z) = −D(v)(v, z) + ½ D(z)(v, v)` (Larotonda, *Estructuras*, Teorema 10.1.1,
formula (10.3)). -/
theorem koszul_diag (D : E → E → E → ℝ) (v z : E) :
    koszul D v v z = -D v v z + D z v v / 2 := by
  simp only [koszul]
  ring

omit [AddCommGroup E] in
/-- The Koszul formula gives back the compatibility with `B`. -/
theorem compatible_of_koszul {B : E → E → ℝ} {D : E → E → E → ℝ} {Γ : E → E → E}
    (hB : ∀ a b, B a b = B b a) (hDsymm : ∀ u a b, D u a b = D u b a)
    (hK : ∀ u a b, B (Γ u a) b = koszul D u a b) (u a b : E) :
    D u a b = -B (Γ u a) b - B a (Γ u b) := by
  rw [hK, hB a, hK, koszul, koszul, hDsymm u b a]
  ring

/-- **Polarization: the spray determines the Koszul formula.** If `Γ` is symmetric and
additive, `B` and `D` are additive in each argument and `D` is symmetric in its last two, and the
spray `v ↦ Γ(v, v)` satisfies `B(Γ(v, v), z) = −D(v)(v, z) + ½ D(z)(v, v)`, then `Γ` satisfies
the Koszul formula (Larotonda, *Estructuras*, formula (10.4)). -/
theorem koszul_of_spray {B : E → E → ℝ} {D : E → E → E → ℝ} {Γ : E → E → E}
    (hBadd : ∀ c c' b, B (c + c') b = B c b + B c' b)
    (hΓ : ∀ u a, Γ u a = Γ a u)
    (hΓl : ∀ u u' a, Γ (u + u') a = Γ u a + Γ u' a)
    (hΓr : ∀ u a a', Γ u (a + a') = Γ u a + Γ u a')
    (hD1 : ∀ u u' a b, D (u + u') a b = D u a b + D u' a b)
    (hD2 : ∀ u a a' b, D u (a + a') b = D u a b + D u a' b)
    (hD3 : ∀ u a b b', D u a (b + b') = D u a b + D u a b')
    (hDsymm : ∀ u a b, D u a b = D u b a)
    (hS : ∀ v z, B (Γ v v) z = -D v v z + D z v v / 2) (u a b : E) :
    B (Γ u a) b = koszul D u a b := by
  have h := hS (u + a) b
  simp only [hΓl, hΓr, hBadd, hD1, hD2, hD3] at h
  have hu := hS u b
  have ha := hS a b
  rw [hΓ a u] at h
  rw [koszul, hDsymm b a u] at *
  linarith

/-- **Metric sprays and metric connections.** For symmetric additive symbols and a symmetric
weakly nondegenerate `B`, compatibility with `B` is equivalent to the spray formula
`B(Γ(v, v), z) = −D(v)(v, z) + ½ D(z)(v, v)`. -/
theorem compatible_iff_spray {B : E → E → ℝ} {D : E → E → E → ℝ} {Γ : E → E → E}
    (hB : ∀ a b, B a b = B b a) (hBadd : ∀ c c' b, B (c + c') b = B c b + B c' b)
    (hΓ : ∀ u a, Γ u a = Γ a u)
    (hΓl : ∀ u u' a, Γ (u + u') a = Γ u a + Γ u' a)
    (hΓr : ∀ u a a', Γ u (a + a') = Γ u a + Γ u a')
    (hD1 : ∀ u u' a b, D (u + u') a b = D u a b + D u' a b)
    (hD2 : ∀ u a a' b, D u (a + a') b = D u a b + D u a' b)
    (hD3 : ∀ u a b b', D u a (b + b') = D u a b + D u a b')
    (hDsymm : ∀ u a b, D u a b = D u b a) :
    (∀ u a b, D u a b = -B (Γ u a) b - B a (Γ u b)) ↔
      ∀ v z, B (Γ v v) z = -D v v z + D z v v / 2 := by
  constructor
  · intro hD v z
    rw [koszul_eq hB hΓ hD, koszul_diag]
  · intro hS
    exact compatible_of_koszul hB hDsymm
      (koszul_of_spray hBadd hΓ hΓl hΓr hD1 hD2 hD3 hDsymm hS)

end Koszul

/-! ### Metric connections on a manifold -/

section Manifold

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace SymmBilinField

variable (g : SymmBilinField E M)

/-- The local representative of `g` in the chart `i`: `G(y)(a, b) = g_{i⁻¹ y}(a, b)`, with
`a, b` read in the chart `i`. -/
def localForm (i : atlas E M) (y a b : E) : ℝ := bilinLocalRep g.toFun i (y, a, b)

/-- The derivative of the local representative in the base point:
`∂G(y)(u)(a, b) = d/dt G(y + t u)(a, b) |_{t = 0}`. -/
def localDeriv (i : atlas E M) (y u a b : E) : ℝ :=
  dMB (bilinLocalRep g.toFun i) ((y, a, b), (u, 0, 0))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem localForm_symm (i : atlas E M) (y a b : E) : g.localForm i y a b = g.localForm i y b a :=
  g.symm' _ _ _

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
theorem localDeriv_symm (i : atlas E M) (y u a b : E) :
    g.localDeriv i y u a b = g.localDeriv i y u b a := by
  simp only [localDeriv, dMB]
  congr 1
  funext t
  simp only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
  exact congrArg _ (congrArg₂ _ (g.symm' _ _ _) (g.symm' _ _ _))

/-- The coordinate change from a chart `i` to the preferred chart, at a point of the chart, is
additive. -/
theorem tangentCoordChange_sub (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (c c' : E) :
    tangentCoordChange i (prefAtlas E (i.1.symm y)) (i.1.symm y) (c - c') =
      tangentCoordChange i (prefAtlas E (i.1.symm y)) (i.1.symm y) c -
        tangentCoordChange i (prefAtlas E (i.1.symm y)) (i.1.symm y) c' := by
  set j := prefAtlas E (i.1.symm y)
  have hxy : i.1 (i.1.symm y) = y := i.1.right_inv hy
  have hmem : i.1 (i.1.symm y) ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source := by
    rw [hxy]
    exact ⟨hy, mem_chart_source E _⟩
  have hf := smoothMBOn_transition' i j 1
  have hsmul := hf.dMB_smul hmem (-1) c'
  have hadd := hf.dMB_add (isOpen_transition_domain i j) hmem c ((-1 : ℝ) • c')
  simp only [tangentCoordChange]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ c', hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]

/-- The coordinate change from a chart `i` to the preferred chart is undone by the coordinate
change back. -/
theorem tangentCoordChange_pref_inv (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (w : E) :
    tangentCoordChange i (prefAtlas E (i.1.symm y)) (i.1.symm y)
      (tangentCoordChange (prefAtlas E (i.1.symm y)) i (i.1.symm y) w) = w := by
  have hx : i.1.symm y ∈ i.1.source := i.1.map_target hy
  have hp : i.1.symm y ∈ (prefAtlas E (i.1.symm y)).1.source := mem_chart_source E _
  exact (tangentCoordChange_comp (prefAtlas E (i.1.symm y)) i (prefAtlas E (i.1.symm y))
    ⟨⟨hp, hx⟩, hp⟩ w).trans (tangentCoordChange_self _ hp w)

theorem localForm_sub (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (c c' b : E) :
    g.localForm i y (c - c') b = g.localForm i y c b - g.localForm i y c' b := by
  simp only [localForm, bilinLocalRep]
  rw [tangentCoordChange_sub i hy, map_sub, LinearMap.sub_apply]

/-- **Weak nondegeneracy in charts.** If `g` is weakly nondegenerate, so is each local
representative `G(y)`, since the coordinate changes are invertible. -/
theorem localForm_nondegenerate (hg : g.IsWeaklyNondegenerate) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (c : E) (hc : ∀ b, g.localForm i y c b = 0) : c = 0 := by
  set x := i.1.symm y
  set T := tangentCoordChange i (prefAtlas E x) x
  set T' := tangentCoordChange (prefAtlas E x) i x
  have hTc : T c = 0 := hg x (T c) fun w ↦ by
    have := hc (T' w)
    simp only [localForm, bilinLocalRep] at this
    rwa [tangentCoordChange_pref_inv i hy w] at this
  have hx : x ∈ i.1.source := i.1.map_target hy
  have hp : x ∈ (prefAtlas E x).1.source := mem_chart_source E _
  have hinv : ∀ v, T' (T v) = v := fun v ↦
    (tangentCoordChange_comp i (prefAtlas E x) i ⟨⟨hx, hp⟩, hx⟩ v).trans
      (tangentCoordChange_self _ hx v)
  have hT0 : T 0 = 0 := by simpa using tangentCoordChange_sub i hy 0 0
  calc c = T' (T c) := (hinv c).symm
    _ = T' (T 0) := by rw [hTc, hT0]
    _ = 0 := hinv 0

theorem localForm_add (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (c c' b : E) :
    g.localForm i y (c + c') b = g.localForm i y c b + g.localForm i y c' b := by
  have h := g.localForm_sub i hy (c + c') c' b
  rw [add_sub_cancel_right] at h
  linarith

theorem localForm_add_right (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (a b b' : E) :
    g.localForm i y a (b + b') = g.localForm i y a b + g.localForm i y a b' := by
  rw [g.localForm_symm, g.localForm_add i hy, g.localForm_symm i y b, g.localForm_symm i y b']

omit [LocallyConvexSpace ℝ E] [T2Space E] [MBManifold E M] in
/-- `∂G(y)(u)` is additive in `u`. -/
theorem localDeriv_add_dir (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (u u' a b : E) :
    g.localDeriv i y (u + u') a b = g.localDeriv i y u a b + g.localDeriv i y u' a b := by
  have hf : ContDiffMBOn 1 (bilinLocalRep g.toFun i) (i.1.target ×ˢ univ) := g.smooth' i 1
  have h := hf.dMB_add (i.1.open_target.prod isOpen_univ) (x := (y, a, b))
    ⟨hy, mem_univ _⟩ (u, 0, 0) (u', 0, 0)
  simp only [localDeriv]
  rw [← h]
  simp

/-- `∂G(y)(u)(a, b)` is additive in `a`: differentiate `G(y + t u)(a + a', b) =
G(y + t u)(a, b) + G(y + t u)(a', b)`, valid for small `t`. -/
theorem localDeriv_add_left (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (u a a' b : E) :
    g.localDeriv i y u (a + a') b = g.localDeriv i y u a b + g.localDeriv i y u a' b := by
  have hf : ContDiffMBOn 1 (bilinLocalRep g.toFun i) (i.1.target ×ˢ univ) := g.smooth' i 1
  have hd : ∀ c, HasDirDerivAt (bilinLocalRep g.toFun i) (y, c, b) (u, 0, 0)
      (g.localDeriv i y u c b) := fun c ↦ by
    have := hf.hasDirDerivAt (x := ((y, c, b) : E × E × E)) ⟨hy, mem_univ _⟩
      (((u, 0, 0) : E × E × E))
    exact this
  have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℝ), y + t • u ∈ i.1.target := by
    have hc : Continuous fun t : ℝ ↦ y + t • u := by fun_prop
    exact nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds
      (by simpa using i.1.open_target.mem_nhds hy))
  have hpt : ∀ (c : E) (t : ℝ), ((y, c, b) : E × E × E) + t • ((u, 0, 0) : E × E × E) =
      (y + t • u, c, b) := fun c t ↦ by
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
  have hsum := Filter.Tendsto.add (hd a : Tendsto _ _ _) (hd a' : Tendsto _ _ _)
  refine tendsto_nhds_unique (hd (a + a') : Tendsto _ _ _) (hsum.congr' ?_)
  filter_upwards [hnear] with t ht
  have e1 : bilinLocalRep g.toFun i (y + t • u, a + a', b) =
      bilinLocalRep g.toFun i (y + t • u, a, b) + bilinLocalRep g.toFun i (y + t • u, a', b) :=
    g.localForm_add i ht a a' b
  have e0 : bilinLocalRep g.toFun i (y, a + a', b) =
      bilinLocalRep g.toFun i (y, a, b) + bilinLocalRep g.toFun i (y, a', b) :=
    g.localForm_add i hy a a' b
  change t⁻¹ • (bilinLocalRep g.toFun i ((y, a, b) + t • (u, 0, 0)) -
      bilinLocalRep g.toFun i (y, a, b)) + t⁻¹ • (bilinLocalRep g.toFun i ((y, a', b) +
      t • (u, 0, 0)) - bilinLocalRep g.toFun i (y, a', b)) =
    t⁻¹ • (bilinLocalRep g.toFun i ((y, a + a', b) + t • (u, 0, 0)) -
      bilinLocalRep g.toFun i (y, a + a', b))
  rw [hpt, hpt, hpt, e1, e0, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- `∂G(y)(u)(a, b)` is additive in `b`. -/
theorem localDeriv_add_right (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (u a b b' : E) :
    g.localDeriv i y u a (b + b') = g.localDeriv i y u a b + g.localDeriv i y u a b' := by
  rw [g.localDeriv_symm, g.localDeriv_add_left i hy, g.localDeriv_symm i y u b,
    g.localDeriv_symm i y u b']

end SymmBilinField

namespace Connection

variable (C : Connection E M) (g : SymmBilinField E M)

/-- A connection `C` is **metric** for `g` if, in every chart,
`∂G(y)(u)(a, b) = − G(y)(Γ(y)(u, a), b) − G(y)(a, Γ(y)(u, b))`: the chart expression of
`X g(Y, Z) = g(∇_X Y, Z) + g(Y, ∇_X Z)` with `∇_X Y = dỸ · X̃ − Γ(X̃, Ỹ)`. -/
def IsMetric : Prop :=
  ∀ i : atlas E M, ∀ y ∈ i.1.target, ∀ u a b,
    g.localDeriv i y u a b = -g.localForm i y (C.Γ i y u a) b - g.localForm i y a (C.Γ i y u b)

variable {C g}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- **Koszul formula** for a symmetric metric connection, in every chart:
`G(Γ(u, a), b) = ½ (−∂G(u)(a, b) − ∂G(a)(u, b) + ∂G(b)(u, a))`. -/
theorem koszul (hC : C.IsSymmetric) (hm : C.IsMetric g) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (u a b : E) :
    g.localForm i y (C.Γ i y u a) b = LCManifolds.koszul (g.localDeriv i y) u a b :=
  koszul_eq (g.localForm_symm i y) (hC i y) (hm i y hy) u a b

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [MBManifold E M] in
/-- **A necessary condition for existence.** If `g` has a symmetric metric connection, then in
every chart the Koszul functionals `b ↦ ½ (−∂G(u)(a, b) − ∂G(a)(u, b) + ∂G(b)(u, a))` are
represented by `G`. For weak metrics this can fail (Schmeding, Example 4.3.7). -/
theorem koszul_represented (hC : C.IsSymmetric) (hm : C.IsMetric g) (i : atlas E M) {y : E}
    (hy : y ∈ i.1.target) (u a : E) :
    ∃ c, ∀ b, g.localForm i y c b = LCManifolds.koszul (g.localDeriv i y) u a b :=
  ⟨C.Γ i y u a, koszul hC hm i hy u a⟩

/-- **The metric spray** (Larotonda, *Estructuras*, Teorema 10.1.1, formula (10.3); Lang,
Ch. VIII, Theorem 4.2, MS 1). A symmetric connection is metric for `g` if and only if, in every chart, its spray
`v ↦ Γ(y)(v, v)` satisfies
`G(y)(Γ(y)(v, v), z) = −∂G(y)(v)(v, z) + ½ ∂G(y)(z)(v, v)`.
In the notation of *Estructuras*, `G(y)(a, b) = ⟨a, g(y) b⟩` and
`∂G(y)(z)(a, b) = ⟨a, g*_{y,z} b⟩`, and this is `⟨F_y(v), g(y) z⟩ = −⟨g*_{y,v} v, z⟩ +
½ ⟨g*_{y,z} v, v⟩`. The symbols are recovered from the spray by polarization, which is the
Koszul formula (formula (10.4) there). No nondegeneracy is needed for this equivalence. -/
theorem isMetric_iff_spray (hC : C.IsSymmetric) :
    C.IsMetric g ↔ ∀ i : atlas E M, ∀ y ∈ i.1.target, ∀ v z,
      g.localForm i y (C.Γ i y v v) z = -g.localDeriv i y v v z + g.localDeriv i y z v v / 2 := by
  have key : ∀ i : atlas E M, ∀ y ∈ i.1.target,
      (∀ u a b, g.localDeriv i y u a b =
          -g.localForm i y (C.Γ i y u a) b - g.localForm i y a (C.Γ i y u b)) ↔
        ∀ v z, g.localForm i y (C.Γ i y v v) z =
          -g.localDeriv i y v v z + g.localDeriv i y z v v / 2 := fun i y hy ↦
    compatible_iff_spray (g.localForm_symm i y) (g.localForm_add i hy) (hC i y)
      (C.add_left i y) (fun u a a' ↦ C.add_right i y u a a') (g.localDeriv_add_dir i hy)
      (g.localDeriv_add_left i hy) (g.localDeriv_add_right i hy) (g.localDeriv_symm i y)
  exact forall_congr' fun i ↦ forall₂_congr fun y hy ↦ key i y hy

/-- **Uniqueness of the Levi-Civita connection.** If `g` is weakly nondegenerate, two symmetric
metric connections have the same symbols in every chart. No completeness and no positivity are
assumed: this holds for weak metrics of any signature. -/
theorem Γ_eq_of_isMetric (hg : g.IsWeaklyNondegenerate) {C' : Connection E M}
    (hC : C.IsSymmetric) (hm : C.IsMetric g) (hC' : C'.IsSymmetric) (hm' : C'.IsMetric g)
    (i : atlas E M) {y : E} (hy : y ∈ i.1.target) (u a : E) :
    C.Γ i y u a = C'.Γ i y u a :=
  eq_of_koszul (g.localForm_symm i y) (g.localForm_sub i hy)
    (g.localForm_nondegenerate hg i hy) (hC i y) (hm i y hy) (hC' i y) (hm' i y hy) u a

/-- Two symmetric metric connections of a weakly nondegenerate `g` have the same covariant
derivative. -/
theorem covDeriv_eq_of_isMetric (hg : g.IsWeaklyNondegenerate) {C' : Connection E M}
    (hC : C.IsSymmetric) (hm : C.IsMetric g) (hC' : C'.IsSymmetric) (hm' : C'.IsMetric g)
    (X Y : M → TangentBundle E M) : C.covDeriv X Y = C'.covDeriv X Y := by
  funext x
  simp only [covDeriv, localCovDeriv]
  rw [Γ_eq_of_isMetric hg hC hm hC' hm' _ ((chartAt E x).map_source (mem_chart_source E x))]

end Connection

/-- **Levi-Civita is unique for weak pseudo-Riemannian metrics of any index**, finite or
infinite, in particular for weak Riemannian and weak Lorentzian metrics. -/
theorem WeakPseudoRiemannianMetric.covDeriv_eq (g : WeakPseudoRiemannianMetric E M)
    {C C' : Connection E M} (hC : C.IsSymmetric) (hm : C.IsMetric g.toSymmBilinField)
    (hC' : C'.IsSymmetric) (hm' : C'.IsMetric g.toSymmBilinField)
    (X Y : M → TangentBundle E M) : C.covDeriv X Y = C'.covDeriv X Y :=
  Connection.covDeriv_eq_of_isMetric g.isWeaklyNondegenerate hC hm hC' hm' X Y

/-- **Levi-Civita is unique for weak Riemannian metrics.** -/
theorem WeakRiemannianMetric.covDeriv_eq (g : WeakRiemannianMetric E M)
    {C C' : Connection E M} (hC : C.IsSymmetric) (hm : C.IsMetric g.toSymmBilinField)
    (hC' : C'.IsSymmetric) (hm' : C'.IsMetric g.toSymmBilinField)
    (X Y : M → TangentBundle E M) : C.covDeriv X Y = C'.covDeriv X Y :=
  g.toWeakPseudoRiemannianMetric.covDeriv_eq hC hm hC' hm' X Y

end Manifold

end LCManifolds

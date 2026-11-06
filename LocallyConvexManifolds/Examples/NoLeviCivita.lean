/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Metric.LeviCivita
import LocallyConvexAnalysis.MBFrechet

/-!
# A weak Riemannian metric without Levi-Civita connection

Reference: A. Schmeding, *An introduction to infinite-dimensional differential geometry*,
arXiv:2112.08114v3, Example 4.3.7 (a weak Riemannian metric on `ℓ²` without metric spray,
pointed out to Schmeding by C. Maor).

Let `H` be a real inner product space and `T : H → H` a continuous linear operator which is
symmetric and positive definite, `⟨T x, x⟩ > 0` for `x ≠ 0`. For `v ∈ H`, the conformal metric

`g_p(x, y) = e^{⟨v, p⟩} ⟨T x, y⟩`

is a weak Riemannian metric on the manifold `H` (`conformalMetric`). Its derivative in the base
point is `∂G(p)(w)(x, y) = ⟨v, w⟩ g_p(x, y)` (`localDeriv_conformal`), and the Koszul functional
of `(x, x)` is `b ↦ g_p(c, b)` for some `c` if and only if `⟨T x, x⟩ v ∈ T(H)`, up to a term
which is already in `T(H)`. Hence:

* `not_exists_isMetric`: **if `v ∉ T(H)`, there is no symmetric metric connection** for `g`
  (`Connection.koszul_represented` fails at `x = v`).

When `T` is invertible, `g` is a strong metric on a Hilbert space and the Levi-Civita connection
exists. So the obstruction is genuinely infinite-dimensional: it needs a symmetric positive
definite `T` which is not surjective, that is, a metric `⟨T ·, ·⟩` whose topology is strictly
coarser than that of `H`. On `ℓ²` the diagonal operator `T x = (x_n / (n + 1))_n` is such an
operator, and `v = (1 / (n + 1))_n` is not in its range (`L2.not_exists_isMetric`).

Schmeding's example uses the weight `n⁻³` and the conformal factor `e^{-‖p‖²}`; the obstruction
is the same, and a linear exponent `⟨v, p⟩` makes the computation shorter.
-/

open Set Filter Bundle
open scoped Topology Manifold InnerProductSpace ContDiff
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Manifolds

namespace NoLeviCivita

section General

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The bilinear form `g_p(x, y) = e^{⟨v, p⟩} ⟨T x, y⟩`. -/
def form (T : H →L[ℝ] H) (v p : H) : LinearMap.BilinForm ℝ H :=
  LinearMap.mk₂ ℝ (fun x y ↦ Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ)
    (fun x x' y ↦ by simp [inner_add_left, mul_add])
    (fun c x y ↦ by simp [inner_smul_left, smul_eq_mul]; ring)
    (fun x y y' ↦ by simp [inner_add_right, mul_add])
    (fun c x y ↦ by simp [inner_smul_right, smul_eq_mul]; ring)

theorem form_apply (T : H →L[ℝ] H) (v p x y : H) :
    form T v p x y = Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ := rfl

/-- The local representative, as a function of `(p, x, y)`. -/
def rep (T : H →L[ℝ] H) (v : H) (q : H × H × H) : ℝ :=
  Real.exp ⟪v, q.1⟫_ℝ * ⟪T q.2.1, q.2.2⟫_ℝ

theorem contDiff_rep (T : H →L[ℝ] H) (v : H) : ContDiff ℝ ∞ (rep T v) := by
  unfold rep
  refine ContDiff.mul ?_ ?_
  · exact (contDiff_const.inner ℝ contDiff_fst).exp
  · exact ((T.contDiff.comp (contDiff_fst.comp contDiff_snd)).inner ℝ
      (contDiff_snd.comp contDiff_snd))

omit [InnerProductSpace ℝ H] in
theorem atlas_eq (i : atlas H H) : i.1 = OpenPartialHomeomorph.refl H :=
  chartedSpaceSelf_atlas.mp i.2

theorem tangentCoordChange_self' (i j : atlas H H) (y a : H) : tangentCoordChange i j y a = a := by
  have hij : i = j := Subtype.ext ((atlas_eq i).trans (atlas_eq j).symm)
  subst hij
  exact tangentCoordChange_self i (by simp [atlas_eq i]) a

theorem bilinLocalRep_eq (T : H →L[ℝ] H) (v : H) (i : atlas H H) :
    bilinLocalRep (form T v) i = rep T v := by
  funext q
  obtain ⟨i, hi⟩ := i
  rw [chartedSpaceSelf_atlas] at hi
  subst hi
  simp [bilinLocalRep, tangentCoordChange_self', form_apply, rep]

variable {T : H →L[ℝ] H}

/-- The conformal metric `g_p(x, y) = e^{⟨v, p⟩} ⟨T x, y⟩`, a weak Riemannian metric on `H`. -/
def conformalMetric (hsymm : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ) (v : H) : WeakRiemannianMetric H H where
  toFun := form T v
  symm' p x y := by
    rw [form_apply, form_apply, hsymm x y, real_inner_comm (T y) x]
  smooth' i := by
    rw [bilinLocalRep_eq]
    have h : SmoothMBOn (rep T v) univ :=
      (smoothMBOn_iff_contDiffOn isOpen_univ).mpr (contDiff_rep T v).contDiffOn
    exact fun k ↦ (h k).mono (subset_univ _)
  pos_def' p x hx := by
    rw [form_apply]
    exact mul_pos (Real.exp_pos _) (hpos x hx)

variable (hsymm : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) (hpos : ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
include hsymm hpos

theorem localForm_conformal (v : H) (i : atlas H H) (p x y : H) :
    (conformalMetric hsymm hpos v).localForm i p x y = Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ := by
  change bilinLocalRep (form T v) i (p, x, y) = _
  rw [bilinLocalRep_eq]
  rfl

/-- **The derivative in the base point**: `∂G(p)(w)(x, y) = ⟨v, w⟩ e^{⟨v, p⟩} ⟨T x, y⟩`. -/
theorem localDeriv_conformal (v : H) (i : atlas H H) (p w x y : H) :
    (conformalMetric hsymm hpos v).localDeriv i p w x y =
      ⟪v, w⟫_ℝ * (Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ) := by
  change dMB (bilinLocalRep (form T v) i) ((p, x, y), (w, 0, 0)) = _
  rw [bilinLocalRep_eq]
  have hline : HasDerivAt (fun t : ℝ ↦ rep T v ((p, x, y) + t • (w, 0, 0)))
      (⟪v, w⟫_ℝ * (Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ ⟪v, p⟫_ℝ + t * ⟪v, w⟫_ℝ) ⟪v, w⟫_ℝ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ⟪v, w⟫_ℝ).const_add ⟪v, p⟫_ℝ
    have h2 := (h1.exp).mul_const ⟪T x, y⟫_ℝ
    have hfun : (fun t : ℝ ↦ rep T v ((p, x, y) + t • (w, 0, 0))) =
        fun t ↦ Real.exp (⟪v, p⟫_ℝ + t * ⟪v, w⟫_ℝ) * ⟪T x, y⟫_ℝ := by
      funext t
      simp [rep, inner_add_right, inner_smul_right]
    rw [hfun]
    convert h2 using 1
    simp
    ring
  have hd : HasDirDerivAt (rep T v) (p, x, y) (w, 0, 0)
      (⟪v, w⟫_ℝ * (Real.exp ⟪v, p⟫_ℝ * ⟪T x, y⟫_ℝ)) := by
    simpa [HasDirDerivAt] using hline.tendsto_slope_zero
  exact hd.dMB_eq

/-- **No Levi-Civita connection.** If `v` is not in the range of `T`, the conformal metric
`e^{⟨v, p⟩} ⟨T x, y⟩` has no symmetric metric connection: the Koszul functional of `(v, v)` is
not represented by `g`. -/
theorem not_exists_isMetric {v : H} (hv : v ∉ range T) :
    ¬ ∃ C : Connection H H, C.IsSymmetric ∧
      C.IsMetric (conformalMetric hsymm hpos v).toSymmBilinField := by
  rintro ⟨C, hC, hm⟩
  set g := (conformalMetric hsymm hpos v).toSymmBilinField
  set i : atlas H H := ⟨OpenPartialHomeomorph.refl H, chartedSpaceSelf_atlas.mpr rfl⟩
  have hv0 : v ≠ 0 := fun h ↦ hv ⟨0, by simp [h]⟩
  obtain ⟨c, hc⟩ := Connection.koszul_represented hC hm i (y := 0) (by simp [i]) v v
  set e := Real.exp ⟪v, (0 : H)⟫_ℝ
  have he : e ≠ 0 := (Real.exp_pos _).ne'
  -- `⟨T c + ⟨v, v⟩ T v, b⟩ = ½ ⟨T v, v⟩ ⟨v, b⟩` for all `b`
  have hb : ∀ b, ⟪T (c + ⟪v, v⟫_ℝ • v), b⟫_ℝ = ⟪(⟪T v, v⟫_ℝ / 2) • v, b⟫_ℝ := by
    intro b
    have h := hc b
    change g.localForm i 0 c b = koszul (g.localDeriv i 0) v v b at h
    rw [koszul_diag] at h
    rw [localForm_conformal hsymm hpos, localDeriv_conformal hsymm hpos,
      localDeriv_conformal hsymm hpos] at h
    rw [map_add, map_smul, inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have h' : e * ⟪T c, b⟫_ℝ = e * (-(⟪v, v⟫_ℝ * ⟪T v, b⟫_ℝ) + ⟪v, b⟫_ℝ * ⟪T v, v⟫_ℝ / 2) := by
      rw [h]; ring
    have := mul_left_cancel₀ he h'
    rw [real_inner_comm b v] at this ⊢
    linarith
  have hT : T (c + ⟪v, v⟫_ℝ • v) = (⟪T v, v⟫_ℝ / 2) • v :=
    ext_inner_right ℝ hb
  have hq : ⟪T v, v⟫_ℝ / 2 ≠ 0 := (half_pos (hpos v hv0)).ne'
  apply hv
  refine ⟨(⟪T v, v⟫_ℝ / 2)⁻¹ • (c + ⟪v, v⟫_ℝ • v), ?_⟩
  rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hq, one_smul]

end General

/-! ### The example on `ℓ²` -/

namespace L2

/-- The real Hilbert space `ℓ²(ℕ)`. -/
abbrev H := lp (fun _ : ℕ ↦ ℝ) 2

/-- The weights `1 / (n + 1)`. -/
def w (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem w_pos (n : ℕ) : 0 < w n := by unfold w; positivity

theorem abs_w_le (n : ℕ) : |w n| ≤ 1 := by
  rw [abs_of_pos (w_pos n)]
  unfold w
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  linarith

theorem memℓp_mul (x : H) : Memℓp (fun n ↦ w n * x n) 2 :=
  (lp.memℓp x).mono' fun n ↦ by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_w_le n)

/-- The diagonal operator `T x = (x_n / (n + 1))_n`, as a linear map. -/
def diagₗ : H →ₗ[ℝ] H where
  toFun x := ⟨fun n ↦ w n * x n, memℓp_mul x⟩
  map_add' x y := lp.ext <| funext fun n ↦ by
    change w n * (x + y) n = w n * x n + w n * y n
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := lp.ext <| funext fun n ↦ by simp; ring

/-- The diagonal operator `T x = (x_n / (n + 1))_n` on `ℓ²`: symmetric, positive definite,
and not surjective. -/
def diag : H →L[ℝ] H :=
  diagₗ.mkContinuous 1 fun x ↦ by
    rw [one_mul]
    exact lp.norm_mono two_ne_zero fun n ↦ by
      change ‖w n * x n‖ ≤ ‖x n‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using abs_w_le n)

theorem diag_apply (x : H) (n : ℕ) : diag x n = w n * x n := rfl

theorem inner_diag (x y : H) : ⟪diag x, y⟫_ℝ = ∑' n, w n * x n * y n := by
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [diag_apply, mul_comm]

theorem diag_symm (x y : H) : ⟪diag x, y⟫_ℝ = ⟪x, diag y⟫_ℝ := by
  rw [inner_diag, real_inner_comm, inner_diag]
  congr 1
  funext n
  ring

theorem diag_pos (x : H) (hx : x ≠ 0) : 0 < ⟪diag x, x⟫_ℝ := by
  obtain ⟨n, hn⟩ : ∃ n, x n ≠ 0 := by
    by_contra h
    exact hx (lp.ext (funext fun n ↦ by
      by_contra hn
      exact h ⟨n, hn⟩))
  rw [lp.inner_eq_tsum]
  refine Summable.tsum_pos (lp.summable_inner _ _) (fun m ↦ ?_) n ?_
  · simp only [diag_apply, RCLike.inner_apply, conj_trivial]
    nlinarith [w_pos m, sq_nonneg (x m)]
  · simp only [diag_apply, RCLike.inner_apply, conj_trivial]
    have := w_pos n
    have : 0 < x n * x n := mul_self_pos.mpr hn
    nlinarith

/-- The vector `v = (1 / (n + 1))_n` of `ℓ²`. -/
def v : H := ⟨w, by
  refine memℓp_gen ?_
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2]
  have : Summable fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) ^ (2 : ℕ) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [one_div] using h
  refine this.congr fun n ↦ ?_
  rw [Real.norm_of_nonneg (w_pos n).le, ← Real.rpow_natCast]
  rfl⟩

/-- `v` is not in the range of `diag`: a preimage would be the constant sequence `1`. -/
theorem v_not_mem_range : v ∉ range diag := by
  rintro ⟨c, hc⟩
  have h1 : ∀ n, c n = 1 := fun n ↦ by
    have := congrFun (congrArg (fun z : H ↦ (z : ℕ → ℝ)) hc) n
    change w n * c n = w n at this
    have hw := (w_pos n).ne'
    field_simp at this
    linarith
  have hs := (lp.memℓp c).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
  have ht := hs.tendsto_atTop_zero
  simp only [h1, norm_one, Real.one_rpow] at ht
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht)

/-- **A weak Riemannian metric on `ℓ²` without Levi-Civita connection** (after Schmeding,
Example 4.3.7): `g_p(x, y) = e^{⟨v, p⟩} Σ x_n y_n / (n + 1)`, with `v = (1 / (n + 1))_n`. -/
theorem not_exists_isMetric :
    ¬ ∃ C : Connection H H, C.IsSymmetric ∧
      C.IsMetric (conformalMetric diag_symm diag_pos v).toSymmBilinField :=
  NoLeviCivita.not_exists_isMetric diag_symm diag_pos v_not_mem_range

end L2

end NoLeviCivita

end LocallyConvex.Manifolds

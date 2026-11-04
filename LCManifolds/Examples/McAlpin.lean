/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# McAlpin's example: a complete Riemannian manifold without shortest curves

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Ejemplo 10.4.2,
taken from J. McAlpin, *Infinite dimensional manifolds and Morse theory*, PhD thesis, Columbia
University, 1965.

Let `H = ℓ²(ℕ)` (real), with standard basis `eₙ` (`e n`), and let `A` be the diagonal operator
`A eₙ = aₙ eₙ` with `a₀ = 1` and `aₙ = 1 + 2⁻ⁿ` for `n ≥ 1`. Let `S` be the unit sphere and
`M = A(S)` (`M`), an ellipsoid. Since `A` is an isomorphism of `H`, `M` is a closed submanifold of
`H` (a regular submanifold, diffeomorphic to `S` via `A`), hence complete for the distance induced
by the norm of `H`, and for its Riemannian distance, which is larger. Lengths of curves in `M` are
measured with the norm of `H`: this is the Riemannian metric of `M` as a submanifold of `H`.

Curves are chains of `C¹` arcs (`Arc`, `IsChain`): an arc is a `C¹` map `γ : ℝ → H` looked at on
an interval `[t₀, t₁]`, of length `∫_{t₀}^{t₁} ‖γ'‖` (`Arc.length`); arcs which are `C¹` only on
`[t₀, t₁]` can be extended to `ℝ`, so asking `γ` to be `C¹` on all of `ℝ` is no restriction.
The distance `d_M` (`pathDist M`) is the infimum of the lengths of the chains in `M`. We prove:

* `norm_le_norm_A`, `norm_A_eq_iff_mem_span`, `Aequiv`: `‖v‖ ≤ ‖A v‖`, with equality if and only if
  `v ∈ span{e₀}`, and `A` is an isomorphism with inverse `Ainv`, the diagonal operator `aₙ⁻¹`;
* `angle_le_chainLength_sphere`, `pi_le_chainLength_sphere`: a chain on `S` from `x` to `y` has
  length at least `angle x y`; in particular, any chain on `S` from `e₀` to `-e₀` has length
  `≥ π`. The proof compares `t ↦ angle (γ t₀) (γ t)` with `t ↦ ∫_{t₀}^t ‖γ'‖` through their right
  Dini derivatives, using the triangle inequality for angles and the estimate
  `angle u v ≤ ‖u - v‖ + 2 ‖u - v‖²` for unit vectors (`angle_le_norm_sub`);
* `pi_lt_chainLength`: **every chain in `M` from `e₀` to `-e₀` has length `> π`**. If `β` is an
  arc of `M` and `α = A⁻¹ β`, then `‖β'‖ = ‖A α'‖ ≥ ‖α'‖`. Where equality of lengths holds,
  `α' ∈ span{e₀}`, so `α` stays on the line through `e₀` and, being continuous on `S`, it is
  constant (`Arc.stop_eq_of_length_le`); hence some arc is strictly longer than its preimage,
  whose chain has length `≥ π`;
* `pathDist_le_pi`: the arcs `βₙ = A αₙ`, `αₙ(t) = cos(πt) e₀ + sin(πt) eₙ`, have length
  `≤ π aₙ → π`;
* `pathDist_eq_pi`, `not_exists_shortest`: **`d_M(e₀, -e₀) = π`, and no chain in `M` joining
  `e₀` and `-e₀` has length `π`**.

The completeness of `M` is not formalized here (only the geometric statements above are).
In finite dimension this cannot happen: on a connected, finite-dimensional Riemannian manifold
which is complete as a metric space, any two points are joined by a shortest geodesic
(Hopf–Rinow, *Estructuras*, Corolario 10.4.3; see `LCManifolds/Metric/FinslerHopfRinow.lean` for
the Finsler version). In McAlpin's example the infimum is approached by the arcs `βₙ`, which run
along the directions `eₙ` where `A` is closer and closer to an isometry, but never attained, since
the only direction where `A` is an isometry is `e₀` itself.
-/

open Set Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace LCManifolds.McAlpin

/-- The real Hilbert space `ℓ²(ℕ)`. -/
abbrev H := lp (fun _ : ℕ ↦ ℝ) 2

/-- The standard basis vector `eₙ` of `ℓ²`. -/
def e (n : ℕ) : H := lp.single 2 n 1

theorem e_apply (n m : ℕ) : e n m = if m = n then 1 else 0 := by
  unfold e; rw [lp.single_apply, Pi.single_apply]

theorem norm_e (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num), norm_one]

/-! ### The operator `A` -/

/-- The diagonal of `A`: `a₀ = 1` and `aₙ = 1 + 2⁻ⁿ` for `n ≥ 1`. -/
def a (n : ℕ) : ℝ := if n = 0 then 1 else 1 + (2 : ℝ)⁻¹ ^ n

theorem a_zero : a 0 = 1 := rfl

theorem a_of_ne_zero {n : ℕ} (hn : n ≠ 0) : a n = 1 + (2 : ℝ)⁻¹ ^ n := by
  simp [a, hn]

theorem one_le_a (n : ℕ) : 1 ≤ a n := by
  unfold a; split_ifs
  · rfl
  · have : (0:ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
    linarith

theorem one_lt_a {n : ℕ} (hn : n ≠ 0) : 1 < a n := by
  rw [a_of_ne_zero hn]; have : (0:ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  linarith

theorem a_le_two (n : ℕ) : a n ≤ 2 := by
  unfold a; split_ifs
  · norm_num
  · have : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith

theorem a_pos (n : ℕ) : 0 < a n := zero_lt_one.trans_le (one_le_a n)

/-- `aₙ → 1`. -/
theorem tendsto_a : Tendsto a atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 + (2 : ℝ)⁻¹ ^ n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [a_of_ne_zero hn]

section Diagonal

variable (c : ℕ → ℝ) {C : ℝ} (hc : ∀ n, |c n| ≤ C)
include hc

theorem norm_mul_le (x : H) (n : ℕ) : ‖c n * x n‖ ≤ ‖(C • x) n‖ := by
  rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_mul]
  gcongr
  exact (hc n).trans (le_abs_self C)

theorem memℓp_mul (x : H) : Memℓp (fun n ↦ c n * x n) 2 :=
  (lp.memℓp (C • x)).mono' (norm_mul_le c hc x)

/-- The diagonal operator with bounded diagonal `c`. -/
def diag : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun n ↦ c n * x n, memℓp_mul c hc x⟩
      map_add' x y := lp.ext <| funext fun n ↦ by
        change c n * (x + y) n = c n * x n + c n * y n
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' r x := lp.ext <| funext fun n ↦ by simp; ring }
    |C| fun x ↦ by
      rw [← Real.norm_eq_abs, ← lp.norm_const_smul (by norm_num)]
      exact lp.norm_mono two_ne_zero (norm_mul_le c hc x)

theorem diag_apply (x : H) (n : ℕ) : diag c hc x n = c n * x n := rfl

end Diagonal

theorem abs_a_le (n : ℕ) : |a n| ≤ 2 := by rw [abs_of_pos (a_pos n)]; exact a_le_two n

theorem abs_inv_a_le (n : ℕ) : |(a n)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.2 (a_pos n))]; exact inv_le_one_of_one_le₀ (one_le_a n)

/-- The diagonal operator `A eₙ = aₙ eₙ`. -/
def A : H →L[ℝ] H := diag a abs_a_le

/-- The inverse of `A`, the diagonal operator `eₙ ↦ aₙ⁻¹ eₙ`. -/
def Ainv : H →L[ℝ] H := diag (fun n ↦ (a n)⁻¹) abs_inv_a_le

theorem A_apply (x : H) (n : ℕ) : A x n = a n * x n := rfl

theorem Ainv_apply (x : H) (n : ℕ) : Ainv x n = (a n)⁻¹ * x n := rfl

theorem A_Ainv (x : H) : A (Ainv x) = x :=
  lp.ext <| funext fun n ↦ by
    change a n * ((a n)⁻¹ * x n) = x n
    rw [← mul_assoc, mul_inv_cancel₀ (a_pos n).ne', one_mul]

theorem Ainv_A (x : H) : Ainv (A x) = x :=
  lp.ext <| funext fun n ↦ by
    change (a n)⁻¹ * (a n * x n) = x n
    rw [← mul_assoc, inv_mul_cancel₀ (a_pos n).ne', one_mul]

/-- `A` as an isomorphism of Banach spaces, with inverse `Ainv`. -/
def Aequiv : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.equivOfInverse A Ainv Ainv_A A_Ainv

/-- `‖v‖ ≤ ‖A v‖`. -/
theorem norm_le_norm_A (v : H) : ‖v‖ ≤ ‖A v‖ :=
  lp.norm_mono two_ne_zero fun n ↦ by
    rw [A_apply, norm_mul, Real.norm_of_nonneg (a_pos n).le]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_a n)

theorem norm_Ainv_le (v : H) : ‖Ainv v‖ ≤ ‖v‖ := by
  simpa [A_Ainv] using norm_le_norm_A (Ainv v)

theorem A_e_zero : A (e 0) = e 0 :=
  lp.ext <| funext fun n ↦ by
    rw [A_apply, e_apply]; split_ifs with h
    · subst h; rw [a_zero, one_mul]
    · rw [mul_zero]

theorem Ainv_e_zero : Ainv (e 0) = e 0 := by
  conv_lhs => rw [← A_e_zero]
  exact Ainv_A _

/-- `‖x‖² = Σ xₙ²` in `ℓ²`. -/
theorem norm_sq_eq_tsum (x : H) : ‖x‖ ^ 2 = ∑' n, x n ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  congr 1; funext n; simp [sq]

theorem summable_sq (x : H) : Summable fun n ↦ x n ^ 2 := by
  simpa [sq] using lp.summable_inner (𝕜 := ℝ) x x

/-- `‖A v‖ = ‖v‖` if and only if `v` is a multiple of `e₀`, i.e. `vₙ = 0` for `n ≥ 1`. -/
theorem norm_A_eq_iff (v : H) : ‖A v‖ = ‖v‖ ↔ ∀ n, n ≠ 0 → v n = 0 := by
  constructor
  · intro h n hn
    by_contra hv
    have hlt : ∑' m, v m ^ 2 < ∑' m, (A v) m ^ 2 := by
      refine Summable.tsum_lt_tsum (i := n) (fun m ↦ ?_) ?_ (summable_sq v) (summable_sq _)
      · rw [A_apply, mul_pow]
        exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (one_le_a m))
      · rw [A_apply, mul_pow]
        exact lt_mul_of_one_lt_left (by positivity) (one_lt_pow₀ (one_lt_a hn) two_ne_zero)
    rw [← norm_sq_eq_tsum, ← norm_sq_eq_tsum, h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    congr 1
    refine lp.ext <| funext fun n ↦ ?_
    rw [A_apply]
    by_cases hn : n = 0
    · subst hn; rw [a_zero, one_mul]
    · rw [h n hn, mul_zero]

/-- `‖A v‖ = ‖v‖` if and only if `v ∈ span{e₀}`. -/
theorem norm_A_eq_iff_mem_span (v : H) : ‖A v‖ = ‖v‖ ↔ v ∈ Submodule.span ℝ {e 0} := by
  rw [norm_A_eq_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v 0, lp.ext <| funext fun n ↦ ?_⟩
    rw [lp.coeFn_smul, Pi.smul_apply, e_apply, smul_eq_mul]
    split_ifs with hn
    · subst hn; ring
    · rw [h n hn, mul_zero]
  · rintro ⟨r, rfl⟩ n hn
    simp [e_apply, hn]


/-! ### Angles between unit vectors -/

open InnerProductGeometry Real

/-- For unit vectors, `angle u v ≤ ‖u - v‖ + 2 ‖u - v‖²`. -/
theorem angle_le_norm_sub {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    angle u v ≤ ‖u - v‖ + 2 * ‖u - v‖ ^ 2 := by
  set θ := angle u v with hθ
  set s := θ / 2 with hs
  have hcos : cos θ = ⟪u, v⟫_ℝ := by rw [hθ, cos_angle, hu, hv]; simp
  have hd : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫_ℝ := by rw [norm_sub_sq_real, hu, hv]; ring
  have hs0 : 0 ≤ s := by have := angle_nonneg u v; rw [hs]; linarith
  have hs1 : s ≤ π / 2 := by have := angle_le_pi u v; rw [hs]; linarith
  have hσ0 : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [pi_pos])
  have hcos2 : cos θ = 1 - 2 * sin s ^ 2 := by
    have : θ = 2 * s := by rw [hs]; ring
    rw [this, cos_two_mul]; nlinarith [sin_sq_add_cos_sq s]
  have hd2 : ‖u - v‖ = 2 * sin s := by
    have h4 : ‖u - v‖ ^ 2 = (2 * sin s) ^ 2 := by rw [hd, ← hcos, hcos2]; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h4
  rw [hd2]
  have hθs : θ = 2 * s := by rw [hs]; ring
  rw [hθs]
  -- it remains to show `s ≤ sin s + 4 sin² s` on `[0, π / 2]`
  rcases hs0.eq_or_lt with h | h
  · rw [← h]; simp
  have hcube := sin_gt_sub_cube h
  have h2 : s ≤ 2 := by linarith [pi_le_four]
  have hs4 : s ^ 2 ≤ 4 := by nlinarith
  have hss : s ^ 3 ≤ 4 * s := by nlinarith [mul_le_mul_of_nonneg_left hs4 h.le]
  have hσ : s / 3 ≤ sin s := by nlinarith
  have hσ2 : s ^ 2 / 9 ≤ sin s ^ 2 := by nlinarith
  nlinarith

/-! ### Arcs and chains -/

/-- A `C¹` arc: a `C¹` map `γ : ℝ → H` considered on the interval `[t₀, t₁]`. -/
structure Arc where
  /-- The initial time. -/
  t₀ : ℝ
  /-- The final time. -/
  t₁ : ℝ
  /-- The interval is nonempty. -/
  le : t₀ ≤ t₁
  /-- The parametrization. -/
  γ : ℝ → H
  /-- The parametrization is `C¹`. -/
  contDiff : ContDiff ℝ 1 γ

namespace Arc

variable (c : Arc)

/-- The length `∫_{t₀}^{t₁} ‖γ'(t)‖ dt` of an arc, measured with the norm of `H`. -/
def length : ℝ := ∫ t in c.t₀..c.t₁, ‖deriv c.γ t‖

/-- The arc stays in `s` on its interval of definition. -/
def InSet (s : Set H) : Prop := MapsTo c.γ (Icc c.t₀ c.t₁) s

theorem continuous : Continuous c.γ := c.contDiff.continuous

theorem continuous_deriv : Continuous (deriv c.γ) := c.contDiff.continuous_deriv le_rfl

theorem hasDerivAt (t : ℝ) : HasDerivAt c.γ (deriv c.γ t) t :=
  ((c.contDiff.differentiable one_ne_zero) t).hasDerivAt

theorem length_nonneg : 0 ≤ c.length :=
  intervalIntegral.integral_nonneg c.le fun _ _ ↦ norm_nonneg _

/-- A bound on the speed bounds the length. -/
theorem length_le {C : ℝ} (h : ∀ t ∈ Icc c.t₀ c.t₁, ‖deriv c.γ t‖ ≤ C) :
    c.length ≤ C * (c.t₁ - c.t₀) := by
  have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) c.le
    (c.continuous_deriv.norm.intervalIntegrable _ _) intervalIntegrable_const h
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
  exact this

/-- The image of an arc under a continuous linear map. -/
def map (L : H →L[ℝ] H) : Arc where
  t₀ := c.t₀
  t₁ := c.t₁
  le := c.le
  γ := L ∘ c.γ
  contDiff := L.contDiff.comp c.contDiff

theorem deriv_map (L : H →L[ℝ] H) (t : ℝ) : deriv (c.map L).γ t = L (deriv c.γ t) :=
  (L.hasFDerivAt.comp_hasDerivAt t (c.hasDerivAt t)).deriv

/-- **An arc on the unit sphere is at least as long as the angle between its endpoints.** -/
theorem angle_le_length (hc : c.InSet (Metric.sphere 0 1)) :
    angle (c.γ c.t₀) (c.γ c.t₁) ≤ c.length := by
  have hnorm : ∀ t ∈ Icc c.t₀ c.t₁, ‖c.γ t‖ = 1 := fun t ht ↦ by
    simpa using hc ht
  have hne : ∀ t ∈ Icc c.t₀ c.t₁, c.γ t ≠ 0 := fun t ht h ↦ by
    simpa [h] using hnorm t ht
  have h₀ : c.t₀ ∈ Icc c.t₀ c.t₁ := left_mem_Icc.2 c.le
  set f : ℝ → ℝ := fun t ↦ angle (c.γ c.t₀) (c.γ t) with hf
  set B : ℝ → ℝ := fun t ↦ ∫ s in c.t₀..t, ‖deriv c.γ s‖ with hB
  have hBd : ∀ t, HasDerivAt B ‖deriv c.γ t‖ t := fun t ↦
    (c.continuous_deriv.norm.integral_hasStrictDerivAt c.t₀ t).hasDerivAt
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := f) (B := B)
    (B' := fun t ↦ ‖deriv c.γ t‖) (a := c.t₀) (b := c.t₁) ?_ ?_ ?_ ?_ ?_
    (right_mem_Icc.2 c.le)
  · simpa [hf, hB, length] using key
  · intro t ht
    have hcont : ContinuousAt (fun t ↦ (c.γ c.t₀, c.γ t)) t :=
      (continuous_const.prodMk c.continuous).continuousAt
    exact (ContinuousAt.comp (g := fun y : H × H ↦ angle y.1 y.2)
      (f := fun t ↦ (c.γ c.t₀, c.γ t)) (x := t)
      (continuousAt_angle (x := (c.γ c.t₀, c.γ t)) (hne _ h₀) (hne t ht)) hcont).continuousWithinAt
  · simp [hf, hB, angle_self (hne _ h₀)]
  · exact (continuous_iff_continuousAt.2 fun t ↦ (hBd t).continuousAt).continuousOn
  · exact fun t _ ↦ (hBd t).hasDerivWithinAt
  · intro x hx r hr
    refine Eventually.frequently ?_
    have hsl : Tendsto (slope c.γ x) (𝓝[>] x) (𝓝 (deriv c.γ x)) :=
      (hasDerivAt_iff_tendsto_slope.1 (c.hasDerivAt x)).mono_left
        (nhdsWithin_mono _ fun z hz ↦ ne_of_gt hz)
    have hdist : Tendsto (fun z ↦ ‖c.γ z - c.γ x‖) (𝓝[>] x) (𝓝 0) := by
      have : Tendsto (fun z ↦ c.γ z - c.γ x) (𝓝 x) (𝓝 (c.γ x - c.γ x)) :=
        (c.continuous.tendsto x).sub tendsto_const_nhds
      rw [sub_self] at this
      simpa using this.norm.mono_left nhdsWithin_le_nhds
    have hg : Tendsto (fun z ↦ ‖slope c.γ x z‖ * (1 + 2 * ‖c.γ z - c.γ x‖)) (𝓝[>] x)
        (𝓝 (‖deriv c.γ x‖ * (1 + 2 * 0))) :=
      hsl.norm.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hdist))
    rw [mul_zero, add_zero, mul_one] at hg
    filter_upwards [hg.eventually (gt_mem_nhds hr), Ioo_mem_nhdsGT hx.2] with z hz hzI
    have hxI : x ∈ Icc c.t₀ c.t₁ := Ico_subset_Icc_self hx
    have hzI' : z ∈ Icc c.t₀ c.t₁ := ⟨hx.1.trans hzI.1.le, hzI.2.le⟩
    have hxz : 0 < z - x := sub_pos.2 hzI.1
    refine lt_of_le_of_lt ?_ hz
    rw [slope_def_field, slope_def_module, norm_smul, Real.norm_of_nonneg (inv_pos.2 hxz).le,
      ← div_eq_inv_mul]
    have htri := angle_le_angle_add_angle (c.γ c.t₀) (c.γ x) (c.γ z)
    have hang := angle_le_norm_sub (hnorm x hxI) (hnorm z hzI')
    rw [norm_sub_rev] at hang
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hxz]
    simp only [hf]
    nlinarith

end Arc

/-- `IsChain s cs x y`: `cs` is a chain of `C¹` arcs in `s` from `x` to `y`, that is, consecutive
arcs share their endpoints; the empty chain joins `x` to itself. -/
def IsChain (s : Set H) : List Arc → H → H → Prop
  | [], x, y => x = y
  | c :: cs, x, y => c.InSet s ∧ c.γ c.t₀ = x ∧ IsChain s cs (c.γ c.t₁) y

/-- The length of a chain of arcs. -/
def chainLength (cs : List Arc) : ℝ := (cs.map Arc.length).sum

@[simp] theorem chainLength_nil : chainLength [] = 0 := rfl

@[simp] theorem chainLength_cons (c : Arc) (cs : List Arc) :
    chainLength (c :: cs) = c.length + chainLength cs := by
  simp [chainLength]

theorem chainLength_nonneg (cs : List Arc) : 0 ≤ chainLength cs := by
  induction cs with
  | nil => simp
  | cons c cs ih => rw [chainLength_cons]; exact add_nonneg c.length_nonneg ih

/-- The path distance of `s ⊆ H`: the infimum of the lengths of the chains of `C¹` arcs in `s`
joining `x` to `y` (`∞` if there are none). -/
def pathDist (s : Set H) (x y : H) : ℝ≥0∞ :=
  ⨅ (cs : List Arc) (_ : IsChain s cs x y), ENNReal.ofReal (chainLength cs)

/-- **Lower bound on the sphere**: a chain of arcs on the unit sphere from `x` to `y` has length
at least `angle x y`. -/
theorem angle_le_chainLength_sphere :
    ∀ (cs : List Arc) (x y : H), x ∈ Metric.sphere (0 : H) 1 →
      IsChain (Metric.sphere 0 1) cs x y → angle x y ≤ chainLength cs
  | [], x, y, hx, h => by
    have hx0 : x ≠ 0 := ne_zero_of_mem_unit_sphere ⟨x, hx⟩
    rw [← (h : x = y), angle_self hx0, chainLength_nil]
  | c :: cs, x, y, _, ⟨hc, hx, hcs⟩ => by
    have h1 := c.angle_le_length hc
    have h2 := angle_le_chainLength_sphere cs _ y (hc (right_mem_Icc.2 c.le)) hcs
    rw [hx] at h1
    rw [chainLength_cons]
    linarith [angle_le_angle_add_angle x (c.γ c.t₁) y]

/-- `angle e₀ (-e₀) = π`. -/
theorem angle_e_zero_neg : angle (e 0) (-e 0) = π := by
  rw [angle_neg_right, angle_self (by simp [← norm_ne_zero_iff, norm_e]), sub_zero]

/-- The antipodal points `±e₀` of the unit sphere are at path distance at least `π`. -/
theorem pi_le_chainLength_sphere {cs : List Arc}
    (h : IsChain (Metric.sphere 0 1) cs (e 0) (-e 0)) : π ≤ chainLength cs := by
  have := angle_le_chainLength_sphere cs _ _ (by simp [norm_e]) h
  rwa [angle_e_zero_neg] at this

/-! ### The ellipsoid `M = A(S)` -/

/-- The ellipsoid `M = A(S)`, image of the unit sphere `S` of `ℓ²` under `A`. -/
def M : Set H := A '' Metric.sphere 0 1

theorem mem_M_iff (y : H) : y ∈ M ↔ Ainv y ∈ Metric.sphere (0 : H) 1 := by
  constructor
  · rintro ⟨z, hz, rfl⟩; rwa [Ainv_A]
  · intro h; exact ⟨_, h, A_Ainv y⟩

theorem e_zero_mem_M : e 0 ∈ M := ⟨e 0, by simp [norm_e], A_e_zero⟩

namespace Arc

variable (c : Arc)

theorem map_Ainv_inSet (hc : c.InSet M) : (c.map Ainv).InSet (Metric.sphere 0 1) :=
  fun _ ht ↦ (mem_M_iff _).1 (hc ht)

/-- `L(A⁻¹ β) ≤ L(β)`. -/
theorem length_map_Ainv_le : (c.map Ainv).length ≤ c.length := by
  refine intervalIntegral.integral_mono_on c.le ?_ ?_ fun t _ ↦ ?_
  · exact (c.map Ainv).continuous_deriv.norm.intervalIntegrable _ _
  · exact c.continuous_deriv.norm.intervalIntegrable _ _
  · rw [deriv_map]; exact norm_Ainv_le _

/-- **The equality case.** If an arc `β` in `M` starting at `e₀` is not longer than its preimage
`α = A⁻¹ β` in the sphere, then `‖A α'‖ = ‖α'‖` along it, so that `α' ∈ span e₀`; hence `α` stays
on the line `ℝ e₀`, and being continuous on the sphere it stays at `e₀`. -/
theorem stop_eq_of_length_le (hc : c.InSet M) (h0 : c.γ c.t₀ = e 0)
    (hle : c.length ≤ (c.map Ainv).length) : c.γ c.t₁ = e 0 := by
  rcases c.le.eq_or_lt with heq | hlt
  · rw [← heq, h0]
  set α : ℝ → H := fun t ↦ Ainv (c.γ t) with hα
  have hα' : ∀ t, HasDerivAt α (Ainv (deriv c.γ t)) t := fun t ↦
    Ainv.hasFDerivAt.comp_hasDerivAt t (c.hasDerivAt t)
  -- `‖β'‖ = ‖A⁻¹ β'‖` on `[t₀, t₁]`
  have heq : ∀ t ∈ Icc c.t₀ c.t₁, ‖A (Ainv (deriv c.γ t))‖ = ‖Ainv (deriv c.γ t)‖ := by
    intro t ht
    rw [A_Ainv]
    by_contra hne
    have hlt' : ‖Ainv (deriv c.γ t)‖ < ‖deriv c.γ t‖ :=
      lt_of_le_of_ne (norm_Ainv_le _) (Ne.symm hne)
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hlt
      (c.map Ainv).continuous_deriv.norm.continuousOn c.continuous_deriv.norm.continuousOn
      (fun s _ ↦ by rw [deriv_map]; exact norm_Ainv_le _)
      ⟨t, ht, by rw [deriv_map]; exact hlt'⟩
    exact absurd hle (not_le.2 this)
  -- the coordinates `αₙ`, `n ≠ 0`, vanish on `[t₀, t₁]`
  have hcoord : ∀ n, n ≠ 0 → ∀ t ∈ Icc c.t₀ c.t₁, α t n = 0 := by
    intro n hn
    have hd : ∀ t, HasDerivAt (fun t ↦ α t n) (Ainv (deriv c.γ t) n) t := fun t ↦
      ((lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 2 n).hasFDerivAt.comp_hasDerivAt t (hα' t))
    have hconst := constant_of_has_deriv_right_zero (f := fun t ↦ α t n)
      (fun t _ ↦ (hd t).continuousAt.continuousWithinAt) fun t ht ↦ by
        have h0' : Ainv (deriv c.γ t) n = 0 := (norm_A_eq_iff _).1 (heq t
          (Ico_subset_Icc_self ht)) n hn
        rw [← h0']; exact (hd t).hasDerivWithinAt
    intro t ht
    rw [hconst t ht]
    simp [hα, h0, Ainv_e_zero, e_apply, hn]
  -- hence `α t = α₀(t) e₀` and `|α₀(t)| = 1` on `[t₀, t₁]`
  have hsingle : ∀ t ∈ Icc c.t₀ c.t₁, α t = lp.single 2 0 (α t 0) := fun t ht ↦
    lp.ext <| funext fun n ↦ by
      rw [lp.single_apply, Pi.single_apply]
      split_ifs with hn
      · rw [hn]
      · exact hcoord n hn t ht
  have hunit : ∀ t ∈ Icc c.t₀ c.t₁, |α t 0| = 1 := fun t ht ↦ by
    have h1 : ‖α t‖ = 1 := by simpa using (mem_M_iff _).1 (hc ht)
    rw [hsingle t ht, lp.norm_single (by norm_num), Real.norm_eq_abs] at h1
    exact h1
  have hstart : α c.t₀ 0 = 1 := by simp [hα, h0, Ainv_e_zero, e_apply]
  -- `α₀` is continuous with values in `{±1}`, so it is constant
  have hend : α c.t₁ 0 = 1 := by
    have hcont : ContinuousOn (fun t ↦ α t 0) (Icc c.t₀ c.t₁) := fun t _ ↦
      ((lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 2 0).continuous.comp
        (Ainv.continuous.comp c.continuous)).continuousAt.continuousWithinAt
    rcases abs_eq (zero_le_one) |>.1 (hunit _ (right_mem_Icc.2 c.le)) with h | h
    · exact h
    · obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' c.le hcont
        (show (0 : ℝ) ∈ Icc (α c.t₁ 0) (α c.t₀ 0) by rw [h, hstart]; norm_num)
      have := hunit t ht
      simp only at ht0
      rw [ht0, abs_zero] at this
      exact absurd this zero_ne_one
  have : α c.t₁ = e 0 := by
    rw [hsingle _ (right_mem_Icc.2 c.le), hend]; rfl
  rw [← A_Ainv (c.γ c.t₁)]
  change A (α c.t₁) = e 0
  rw [this, A_e_zero]

end Arc

/-- **Lower bound in `M`**: a chain of arcs in `M` from `x` to `y` has length at least
`angle (A⁻¹ x) (A⁻¹ y)`. -/
theorem angle_le_chainLength_M :
    ∀ (cs : List Arc) (x y : H), x ∈ M → IsChain M cs x y →
      angle (Ainv x) (Ainv y) ≤ chainLength cs
  | [], x, y, hx, h => by
    have hx0 : Ainv x ≠ 0 := ne_zero_of_mem_unit_sphere ⟨_, (mem_M_iff x).1 hx⟩
    rw [← (h : x = y), angle_self hx0, chainLength_nil]
  | c :: cs, x, y, _, ⟨hc, hx, hcs⟩ => by
    have h1 := (c.map Ainv).angle_le_length (c.map_Ainv_inSet hc)
    have h1' := c.length_map_Ainv_le
    have h2 := angle_le_chainLength_M cs _ y (hc (right_mem_Icc.2 c.le)) hcs
    change angle (Ainv (c.γ c.t₀)) (Ainv (c.γ c.t₁)) ≤ _ at h1
    rw [hx] at h1
    rw [chainLength_cons]
    linarith [angle_le_angle_add_angle (Ainv x) (Ainv (c.γ c.t₁)) (Ainv y)]

/-- A chain in `M` starting at `e₀` either is strictly longer than the angle at which it sees its
endpoint, or ends at `e₀`. -/
theorem lt_chainLength_or_eq :
    ∀ (cs : List Arc) (y : H), IsChain M cs (e 0) y →
      angle (e 0) (Ainv y) < chainLength cs ∨ y = e 0
  | [], y, h => Or.inr (h : e 0 = y).symm
  | c :: cs, y, ⟨hc, hx, hcs⟩ => by
    rw [chainLength_cons]
    have hz : c.γ c.t₁ ∈ M := hc (right_mem_Icc.2 c.le)
    by_cases hlt : (c.map Ainv).length < c.length
    · left
      have h1 := (c.map Ainv).angle_le_length (c.map_Ainv_inSet hc)
      change angle (Ainv (c.γ c.t₀)) (Ainv (c.γ c.t₁)) ≤ _ at h1
      rw [hx, Ainv_e_zero] at h1
      have h2 := angle_le_chainLength_M cs _ y hz hcs
      linarith [angle_le_angle_add_angle (e 0) (Ainv (c.γ c.t₁)) (Ainv y)]
    · have hstop := c.stop_eq_of_length_le hc hx (not_lt.1 hlt)
      rw [hstop] at hcs
      rcases lt_chainLength_or_eq cs y hcs with h | h
      · exact Or.inl (by linarith [c.length_nonneg])
      · exact Or.inr h

/-- `-e₀ ≠ e₀`. -/
theorem neg_e_zero_ne : -e 0 ≠ e 0 := by
  intro h
  have := congrArg (fun z : H ↦ z 0) h
  simp [e_apply] at this
  norm_num at this

/-- **Strict lower bound** (McAlpin): every chain of `C¹` arcs in `M` from `e₀` to `-e₀` has
length strictly greater than `π`. -/
theorem pi_lt_chainLength {cs : List Arc} (h : IsChain M cs (e 0) (-e 0)) :
    π < chainLength cs := by
  rcases lt_chainLength_or_eq cs _ h with h | h
  · rwa [map_neg, Ainv_e_zero, angle_e_zero_neg] at h
  · exact absurd h neg_e_zero_ne


/-! ### The upper bound -/

theorem A_e (n : ℕ) : A (e n) = a n • e n :=
  lp.ext <| funext fun m ↦ by
    rw [A_apply, lp.coeFn_smul, Pi.smul_apply, e_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · rw [mul_zero, mul_zero]

theorem inner_e_zero_e {n : ℕ} (hn : n ≠ 0) : ⟪e 0, e n⟫_ℝ = 0 := by
  rw [e, lp.inner_single_left, e_apply]; simp [Ne.symm hn]

theorem norm_sq_smul_add_smul {n : ℕ} (hn : n ≠ 0) (r s : ℝ) :
    ‖r • e 0 + s • e n‖ ^ 2 = r ^ 2 + s ^ 2 := by
  rw [norm_add_sq_real, inner_smul_left, inner_smul_right, inner_e_zero_e hn, norm_smul,
    norm_smul, norm_e, norm_e]
  simp [sq_abs]

/-- The great half circle `αₙ(t) = cos(πt) e₀ + sin(πt) eₙ` of `S`, from `e₀` to `-e₀`. -/
def α (n : ℕ) (t : ℝ) : H := cos (π * t) • e 0 + sin (π * t) • e n

/-- The arc `βₙ = A αₙ`, `βₙ(t) = cos(πt) e₀ + aₙ sin(πt) eₙ` on `[0, 1]`, which joins `e₀` to
`-e₀` in `M`. -/
def β (n : ℕ) : Arc where
  t₀ := 0
  t₁ := 1
  le := zero_le_one
  γ t := cos (π * t) • e 0 + (a n * sin (π * t)) • e n
  contDiff := by fun_prop

theorem β_eq_A_α (n : ℕ) (t : ℝ) : (β n).γ t = A (α n t) := by
  simp only [β, α, map_add, map_smul, A_e, smul_smul, a_zero, one_mul, mul_comm]

theorem norm_α {n : ℕ} (hn : n ≠ 0) (t : ℝ) : ‖α n t‖ = 1 := by
  have h := norm_sq_smul_add_smul hn (cos (π * t)) (sin (π * t))
  rw [cos_sq_add_sin_sq] at h
  rw [α]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

/-- `βₙ` lies in `M`. -/
theorem β_inSet {n : ℕ} (hn : n ≠ 0) : (β n).InSet M :=
  fun t _ ↦ ⟨α n t, by simp [norm_α hn], (β_eq_A_α n t).symm⟩

/-- `βₙ` joins `e₀` to `-e₀` in `M`. -/
theorem isChain_β {n : ℕ} (hn : n ≠ 0) : IsChain M [β n] (e 0) (-e 0) :=
  ⟨β_inSet hn, by simp [β], by simp [IsChain, β]⟩

/-- `L(βₙ) ≤ π aₙ`, since `‖βₙ'‖² = π² sin²(πt) + π² aₙ² cos²(πt)`. -/
theorem length_β_le {n : ℕ} (hn : n ≠ 0) : (β n).length ≤ π * a n := by
  have hd : ∀ t, HasDerivAt (β n).γ
      ((-sin (π * t) * π) • e 0 + (a n * (cos (π * t) * π)) • e n) t := fun t ↦ by
    have h1 : HasDerivAt (fun t ↦ π * t) π t := by
      simpa using (hasDerivAt_id t).const_mul π
    exact (h1.cos.smul_const (e 0)).add ((h1.sin.const_mul (a n)).smul_const (e n))
  have := (β n).length_le (C := π * a n) fun t _ ↦ by
    rw [(hd t).deriv]
    have hsq := norm_sq_smul_add_smul hn (-sin (π * t) * π) (a n * (cos (π * t) * π))
    have ha := one_le_a n
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity [pi_pos, a_pos n])
      two_ne_zero).1 ?_
    rw [hsq]
    have hs := sin_sq_add_cos_sq (π * t)
    have : sin (π * t) ^ 2 ≤ a n ^ 2 * sin (π * t) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ ha)
    nlinarith [sq_nonneg π]
  simpa [β] using this

/-! ### The distance of `M` and the absence of shortest curves -/

/-- **Upper bound**: `d_M(e₀, -e₀) ≤ π`, using the arcs `βₙ` of length `≤ π aₙ → π`. -/
theorem pathDist_le_pi : pathDist M (e 0) (-e 0) ≤ ENNReal.ofReal π := by
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (π * a n)) atTop (𝓝 (ENNReal.ofReal (π * 1))) :=
    ENNReal.tendsto_ofReal (tendsto_a.const_mul π)
  rw [mul_one] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  refine (iInf₂_le [β n] (isChain_β hn)).trans (ENNReal.ofReal_le_ofReal ?_)
  simpa using length_β_le hn

/-- **McAlpin's example** (Larotonda, *Estructuras geométricas*, Ejemplo 10.4.2):
`d_M(e₀, -e₀) = π`. -/
theorem pathDist_eq_pi : pathDist M (e 0) (-e 0) = ENNReal.ofReal π :=
  le_antisymm pathDist_le_pi <| le_iInf₂ fun _ h ↦ ENNReal.ofReal_le_ofReal (pi_lt_chainLength h).le

/-- **McAlpin's example**: there is no shortest curve in `M` joining `e₀` and `-e₀`; every chain of
`C¹` arcs joining them is strictly longer than their distance `π`. -/
theorem not_exists_shortest :
    ¬ ∃ cs : List Arc, IsChain M cs (e 0) (-e 0) ∧
      ENNReal.ofReal (chainLength cs) = pathDist M (e 0) (-e 0) := by
  rintro ⟨cs, hcs, hL⟩
  rw [pathDist_eq_pi] at hL
  have := (ENNReal.ofReal_lt_ofReal_iff (pi_pos.trans (pi_lt_chainLength hcs))).2
    (pi_lt_chainLength hcs)
  rw [hL] at this
  exact lt_irrefl _ this

end LCManifolds.McAlpin

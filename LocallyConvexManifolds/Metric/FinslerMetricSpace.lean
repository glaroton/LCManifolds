/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LocallyConvexManifolds.Metric.Finsler
import LocallyConvexManifolds.MetricGeometry.LengthMetric
import LocallyConvexManifolds.MetricGeometry.AsymmDist
import LocallyConvexManifolds.MetricGeometry.ForwardLength

/-!
# Finsler manifolds as metric spaces

Reference: G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 9, §9.1.1
(Proposición 9.1.2).

Let `μ` be a **reversible** Finsler length structure on `M`. Its distance `d_b`
(`FinslerLengthStructure.dist`, defined with piecewise `C¹` paths) is then a pseudo-(extended)
metric, and `FinslerSpace μ` is a copy of `M` with this distance. Reversibility is needed for the
symmetry of `d_b`; without it `d_b` is only a quasi-metric (`FinslerLengthStructure.dist_triangle`
still holds), and the metric theory of Cap. 8, which is symmetric, does not apply as such.

The topology of `FinslerSpace μ` is the one of `d_b`, which need not be the manifold topology of
`M`; comparing both is the subject of *Estructuras*, §9.1.2.

## Main results

* `edist_le_abs_length`, `continuous_toFinsler`: a `C¹` curve of `M` is continuous for `d_b`,
  since `d_b(γ s, γ t) ≤ |L_b(γ|[s, t])|`;
* `eVariationOn_le_length` (**Proposición 9.1.2**, first part): the metric length of a `C¹` arc
  is at most its Finsler length, `ℓ(γ) ≤ L_b(γ)`;
* `isInterior` (**Proposición 9.1.2**): `(M, d_b)` is an interior metric space, `d_ℓ = d_b`.
* `fwdVar_le_length`, `isFwdInterior`: the same without reversibility, for the asymmetric distance
  `d_b` (Mennucci, *On asymmetric distances*, 2013): the forward length of a `C¹` arc is at most its
  Finsler length, and `(M, d_b)` is forward-interior (Mennucci's g-intrinsic, Def. 3.16).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Manifolds

universe u

variable {E : Type u}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [MBManifold E M]

namespace FinslerLengthStructure

variable (μ : FinslerLengthStructure E M)

/-- A copy of `M` with the Finsler distance `d_b`, an asymmetric distance; its topology is that of
the symmetrized distance `max (d_b(x, y), d_b(y, x))` (Mennucci, §3.1). -/
def FinslerSpace (_μ : FinslerLengthStructure E M) : Type _ := M

/-- The identity `M → FinslerSpace μ`. -/
def toFinsler : M → FinslerSpace μ := id

/-- The identity `FinslerSpace μ → M`. -/
def ofFinsler : FinslerSpace μ → M := id

instance : AsymmPseudoEMetricSpace (FinslerSpace μ) :=
  AsymmPseudoEMetricSpace.ofBDist (fun x y ↦ μ.dist (μ.ofFinsler x) (μ.ofFinsler y))
    (fun _ ↦ μ.dist_self _) (fun _ _ _ ↦ μ.dist_triangle _ _ _)

theorem bdist_toFinsler (x y : M) : bdist (μ.toFinsler x) (μ.toFinsler y) = μ.dist x y := rfl

/-- **`b(γ s, γ t)` is controlled by the lengths of `γ` and of the reversed curve**, with no
reversibility: for `s ≤ t` one goes along `γ`, for `t < s` along `τ ↦ γ (-τ)`. -/
theorem bdist_le_lengths {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (s t : ℝ) :
    bdist (μ.toFinsler (γ s)) (μ.toFinsler (γ t)) ≤
      ENNReal.ofReal (|μ.length γ s t| + |μ.length (fun τ ↦ γ (-τ)) (-s) (-t)|) := by
  rw [bdist_toFinsler]
  rcases le_total s t with hst | hts
  · refine (μ.dist_le hγ hst).trans (ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  · have hδ := isCkCurve_reverse hγ
    have h := μ.dist_le hδ (neg_le_neg hts)
    simp only [neg_neg] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- **`C¹` curves are continuous for the topology of `d_b`** (the symmetrized topology), with no
reversibility. -/
theorem continuous_toFinsler {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) :
    Continuous fun t ↦ μ.toFinsler (γ t) := by
  rw [continuous_iff_continuousAt]
  intro s
  have hδ := isCkCurve_reverse hγ
  have hprim : ∀ {c : ℝ → M}, IsCkCurve E 1 c → ∀ a : ℝ, Continuous fun t ↦ μ.length c a t :=
    fun hc a ↦ intervalIntegral.continuous_primitive
      (fun _ _ ↦ (μ.continuous_velocity hc).intervalIntegrable _ _) a
  set G : ℝ → ℝ := fun t ↦ |μ.length γ s t| + |μ.length (fun τ ↦ γ (-τ)) (-s) (-t)|
  have hG : Continuous G :=
    ((hprim hγ s).abs).add (((hprim hδ (-s)).comp continuous_neg).abs)
  have hG0 : G s = 0 := by simp [G, length]
  have h0 : Tendsto (fun t ↦ ENNReal.ofReal (G t)) (𝓝 s) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto _).comp (hG.tendsto s)
    rwa [hG0, ENNReal.ofReal_zero] at h
  have hsymm : ∀ t, |μ.length γ t s| + |μ.length (fun τ ↦ γ (-τ)) (-t) (-s)| = G t := by
    intro t
    simp only [G, length]
    rw [intervalIntegral.integral_symm (b := s), abs_neg,
      intervalIntegral.integral_symm (a := -t), abs_neg]
  rw [ContinuousAt, EMetric.tendsto_nhds]
  intro ε hε
  filter_upwards [(h0.eventually (gt_mem_nhds hε))] with t ht
  rw [edist_eq_max_bdist]
  refine max_lt ((μ.bdist_le_lengths hγ t s).trans_lt ?_) ((μ.bdist_le_lengths hγ s t).trans_lt ht)
  rwa [hsymm]

/-! ### Proposición 9.1.2 without reversibility -/

/-- Lengths along a monotone sequence of times telescope. -/
theorem sum_length_range' {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (u : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, μ.length γ (u i) (u (i + 1)) = μ.length γ (u 0) (u n) := by
  induction n with
  | zero => simp [length]
  | succ n ih => rw [Finset.sum_range_succ, ih, μ.length_add hγ]

/-- **Proposición 9.1.2, `ℓ⁺(γ) ≤ L_b(γ)`, for any Finsler length structure**: the forward
length of a `C¹` arc for the asymmetric distance `d_b` is at most its Finsler length. -/
theorem fwdVar_le_length {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} :
    fwdVar (fun t ↦ μ.toFinsler (γ t)) (Icc a b) ≤ ENNReal.ofReal (μ.length γ a b) := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_
  calc ∑ i ∈ Finset.range n, bdist (μ.toFinsler (γ (u i))) (μ.toFinsler (γ (u (i + 1))))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (μ.length γ (u i) (u (i + 1))) :=
        Finset.sum_le_sum fun i _ ↦ μ.dist_le hγ (hu (Nat.le_succ i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, μ.length γ (u i) (u (i + 1))) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ ↦ μ.length_nonneg γ (hu (Nat.le_succ i))).symm
    _ = ENNReal.ofReal (μ.length γ (u 0) (u n)) := by rw [μ.sum_length_range' hγ]
    _ ≤ ENNReal.ofReal (μ.length γ a b) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := μ.length_add hγ a (u 0) b
        have h2 := μ.length_add hγ (u 0) (u n) b
        have h3 := μ.length_nonneg γ (hus 0).1
        have h4 := μ.length_nonneg γ (hus n).2
        linarith

/-- A `C¹` arc as a continuous curve of `(M, d_b)`, measured with the forward length. -/
def fwdArcPath {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    FwdPath (μ.toFinsler (γ a)) (μ.toFinsler (γ b)) where
  toFun t := μ.toFinsler (γ t)
  a := a
  b := b
  le := hab
  continuousOn := (μ.continuous_toFinsler hγ).continuousOn
  source := rfl
  target := rfl

/-- The forward rectifiable distance is bounded by the length of every chain of `C¹` arcs. -/
theorem fwdLengthDist_le_of_reach {x y : M} {L : ℝ} (h : μ.Reach x y L) :
    fwdLengthDist (μ.toFinsler x) (μ.toFinsler y) ≤ ENNReal.ofReal L := by
  induction h with
  | refl x => simp
  | @cons γ a b y L hγ hab hrest ih =>
    calc fwdLengthDist (μ.toFinsler (γ a)) (μ.toFinsler y)
        ≤ fwdLengthDist (μ.toFinsler (γ a)) (μ.toFinsler (γ b)) +
            fwdLengthDist (μ.toFinsler (γ b)) (μ.toFinsler y) := fwdLengthDist_triangle _ _ _
      _ ≤ ENNReal.ofReal (μ.length γ a b) + ENNReal.ofReal L := by
          gcongr
          exact (fwdLengthDist_le (μ.fwdArcPath hγ hab)).trans (μ.fwdVar_le_length hγ)
      _ = ENNReal.ofReal (μ.length γ a b + L) :=
          (ENNReal.ofReal_add (μ.length_nonneg γ hab) hrest.nonneg).symm

/-- **Proposición 9.1.2 for non-reversible Finsler structures**: `(M, d_b)` is a forward-interior
asymmetric metric space (Mennucci's g-intrinsic, Def. 3.16): `d_b` is the infimum of the forward
lengths of the curves continuous for the symmetrized topology. -/
theorem isFwdInterior : IsFwdInterior (FinslerSpace μ) := by
  intro x y
  refine le_antisymm ?_ (bdist_le_fwdLengthDist x y)
  exact le_iInf fun p ↦ μ.fwdLengthDist_le_of_reach (x := μ.ofFinsler x) (y := μ.ofFinsler y) p.2

variable [hrev : Fact μ.IsReversible]

/-- For a reversible `μ`, the symmetrized distance is `d_b` itself. -/
theorem edist_toFinsler (x y : M) : edist (μ.toFinsler x) (μ.toFinsler y) = μ.dist x y := by
  rw [edist_eq_max_bdist, bdist_toFinsler, bdist_toFinsler, μ.dist_comm hrev.out y x, max_self]

/-- **`d_b(γ s, γ t) ≤ |L_b(γ|[s, t])|`** for a `C¹` curve. -/
theorem edist_le_abs_length {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (s t : ℝ) :
    edist (μ.toFinsler (γ s)) (μ.toFinsler (γ t)) ≤ ENNReal.ofReal |μ.length γ s t| := by
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (μ.length_nonneg γ hst), edist_toFinsler]
    exact μ.dist_le hγ hst
  · rw [edist_comm, edist_toFinsler]
    have h := μ.dist_le hγ hts
    have hsym : μ.length γ s t = -μ.length γ t s := intervalIntegral.integral_symm _ _
    rwa [hsym, abs_neg, abs_of_nonneg (μ.length_nonneg γ hts)]

omit hrev in
/-- Lengths along a monotone sequence of times telescope. -/
theorem sum_length_range {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) (u : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, μ.length γ (u i) (u (i + 1)) = μ.length γ (u 0) (u n) := by
  induction n with
  | zero => simp [length]
  | succ n ih => rw [Finset.sum_range_succ, ih, μ.length_add hγ]

/-- **Proposición 9.1.2, `ℓ(γ) ≤ L_b(γ)`**: the length of a `C¹` arc in the metric space
`(M, d_b)` is at most its Finsler length. -/
theorem eVariationOn_le_length {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (_hab : a ≤ b) :
    eVariationOn (fun t ↦ μ.toFinsler (γ t)) (Icc a b) ≤ ENNReal.ofReal (μ.length γ a b) := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_
  calc ∑ i ∈ Finset.range n, edist (μ.toFinsler (γ (u (i + 1)))) (μ.toFinsler (γ (u i)))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (μ.length γ (u i) (u (i + 1))) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [edist_comm, edist_toFinsler]
        exact μ.dist_le hγ (hu (Nat.le_succ i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, μ.length γ (u i) (u (i + 1))) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ ↦ μ.length_nonneg γ (hu (Nat.le_succ i))).symm
    _ = ENNReal.ofReal (μ.length γ (u 0) (u n)) := by rw [μ.sum_length_range hγ]
    _ ≤ ENNReal.ofReal (μ.length γ a b) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := μ.length_add hγ a (u 0) b
        have h2 := μ.length_add hγ (u 0) (u n) b
        have h3 := μ.length_nonneg γ (hus 0).1
        have h4 := μ.length_nonneg γ (hus n).2
        linarith

/-- A `C¹` arc as a continuous curve of `(M, d_b)`. -/
def arcPath {γ : ℝ → M} (hγ : IsCkCurve E 1 γ) {a b : ℝ} (hab : a ≤ b) :
    RectPath (μ.toFinsler (γ a)) (μ.toFinsler (γ b)) where
  toFun t := μ.toFinsler (γ t)
  a := a
  b := b
  le := hab
  continuousOn := (μ.continuous_toFinsler hγ).continuousOn
  source := rfl
  target := rfl

/-- `d_ℓ` is bounded by the length of every chain of `C¹` arcs. -/
theorem lengthDist_le_of_reach {x y : M} {L : ℝ} (h : μ.Reach x y L) :
    lengthDist (μ.toFinsler x) (μ.toFinsler y) ≤ ENNReal.ofReal L := by
  induction h with
  | refl x => simp
  | @cons γ a b y L hγ hab hrest ih =>
    calc lengthDist (μ.toFinsler (γ a)) (μ.toFinsler y)
        ≤ lengthDist (μ.toFinsler (γ a)) (μ.toFinsler (γ b)) +
            lengthDist (μ.toFinsler (γ b)) (μ.toFinsler y) := lengthDist_triangle _ _ _
      _ ≤ ENNReal.ofReal (μ.length γ a b) + ENNReal.ofReal L := by
          gcongr
          exact (lengthDist_le (μ.arcPath hγ hab)).trans (μ.eVariationOn_le_length hγ hab)
      _ = ENNReal.ofReal (μ.length γ a b + L) :=
          (ENNReal.ofReal_add (μ.length_nonneg γ hab) hrest.nonneg).symm

/-- **Proposición 9.1.2**: `(M, d_b)` is an interior metric space: `d_ℓ = d_b`. -/
theorem isInterior : IsInterior (FinslerSpace μ) := by
  intro x y
  refine le_antisymm ?_ (edist_le_lengthDist x y)
  change lengthDist x y ≤ edist (μ.toFinsler (μ.ofFinsler x)) (μ.toFinsler (μ.ofFinsler y))
  rw [edist_toFinsler]
  exact le_iInf fun p ↦ μ.lengthDist_le_of_reach (x := μ.ofFinsler x) (y := μ.ofFinsler y) p.2

end FinslerLengthStructure

end LocallyConvex.Manifolds

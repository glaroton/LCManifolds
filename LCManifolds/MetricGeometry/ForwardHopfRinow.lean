/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
import LCManifolds.MetricGeometry.ForwardLength
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Shortest forward curves in asymmetric spaces

References: A. C. G. Mennucci, *On asymmetric distances*, Anal. Geom. Metr. Spaces 1 (2013),
200–231, §3; G. Larotonda, *Estructuras geométricas para las variedades de Banach*, Cap. 8,
Teorema 8.2.3 (see `HopfRinow.lean` for the symmetric case).

Let `(X, b)` be an asymmetric pseudo-(extended) metric space (`AsymmPseudoEMetricSpace`, see
`AsymmDist.lean`), with the topology of the symmetrized distance `d = max (b, b̄)`, and assume
that it is g-intrinsic (`IsFwdInterior X`, see `ForwardLength.lean`): `b(x, y)` is the infimum of
the forward lengths of the continuous curves from `x` to `y`. We prove the asymmetric analogue of
the shortest-path part of the metric Hopf–Rinow theorem: if the forward ball
`{z | b(x, z) ≤ b(x, y) + 1}` is compact and the asymmetry is bounded on it, there is a continuous
curve from `x` to `y` of forward length `b(x, y)`.

## Main results

* `bdist_le_bdist_add_edist`, `continuous_bdist`: `b(x, y) ≤ b(x', y') + d(x, x') + d(y, y')`,
  so `b` is continuous for the symmetrized topology (Mennucci, Prop. 3.2);
* `IsFwdInterior.exists_fwdPath_length_eq_of_isCompact`: existence of shortest forward curves.

## Implementation notes

As in `IsInterior.exists_rectPath_length_eq_of_isCompact`, we avoid the Arzelà–Ascoli theorem and
the lower semicontinuity of the length. The forward Lipschitz reparametrizations
`ηₙ : [0, 1] → X` of almost minimizing curves (`FwdPath.exists_lipschitz_reparam`) satisfy
`b(ηₙ u, ηₙ v) ≤ (d + 1/(n+1)) (v - u)` for `u ≤ v`, where `d = b(x, y)`, and take values in the
forward ball `{z | b(x, z) ≤ d + 1}`. A cluster point `γ` of `(ηₙ)` in the product (pointwise)
topology exists by Tychonoff's theorem, and by the continuity of `b` it satisfies
`b(γ u, γ v) ≤ d (v - u)` for `u ≤ v`; this forward bound alone gives forward length `≤ d`.

**Why bounded asymmetry.** The forward bound says nothing about `b(γ v, γ u)`, and the symmetrized
topology needs both `b(γ u, γ v)` and `b(γ v, γ u)` small for `γ` to be continuous (Mennucci,
Prop. 3.1). The hypothesis `b(w, z) ≤ C b(z, w)` on the forward ball turns `γ` into a Lipschitz
curve for `d`. Without some such hypothesis the limit curve need not be continuous: already the
running length of a curve can be continuous while the curve is not (Mennucci, Example 4.1), and,
as Mennucci points out in the abstract, a geodesic segment in the sense of Busemann need not be
continuous in this setting.

Since `X` is only pseudo-(extended) metric, `[T2Space X]` is used to identify `γ 0` with `x` and
`γ 1` with `y`.
-/

open Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace LCManifolds

variable {X : Type*} [AsymmPseudoEMetricSpace X]

/-- The asymmetric distance is `1`-Lipschitz in each variable for the symmetrized distance:
`b(x, y) ≤ b(x', y') + d(x, x') + d(y, y')` (Mennucci, Prop. 3.2). -/
theorem bdist_le_bdist_add_edist (x y x' y' : X) :
    bdist x y ≤ bdist x' y' + edist x x' + edist y y' :=
  calc bdist x y ≤ bdist x x' + bdist x' y := bdist_triangle _ _ _
    _ ≤ bdist x x' + (bdist x' y' + bdist y' y) := by gcongr; exact bdist_triangle _ _ _
    _ ≤ edist x x' + (bdist x' y' + edist y y') := by
        gcongr
        · exact bdist_le_edist _ _
        · exact bdist_le_edist' y y'
    _ = bdist x' y' + edist x x' + edist y y' := by ring

/-- **The asymmetric distance is continuous** for the symmetrized topology (Mennucci,
Prop. 3.2). -/
theorem continuous_bdist : Continuous fun p : X × X ↦ bdist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 ENNReal.ofNat_ne_top fun p q ↦ ?_
  refine (bdist_le_bdist_add_edist p.1 p.2 q.1 q.2).trans ?_
  rw [add_assoc, two_mul, Prod.edist_eq]
  gcongr
  · exact le_max_left (edist p.1 q.1) (edist p.2 q.2)
  · exact le_max_right (edist p.1 q.1) (edist p.2 q.2)

/-- **Existence of shortest forward curves** (the asymmetric analogue of the shortest-path part
of *Estructuras*, Teorema 8.2.3). Let `X` be a g-intrinsic asymmetric space and `x, y ∈ X` with
`b(x, y) < ∞`. If the forward ball `B = {z | b(x, z) ≤ b(x, y) + 1}` is compact and the
asymmetry is bounded on it, `b(w, z) ≤ C b(z, w)` for `z, w ∈ B`, then there is a curve from
`x` to `y`, continuous for the symmetrized topology, whose forward length is `b(x, y)`.

The forward Lipschitz reparametrizations of almost minimizing curves take values in `B`; a
cluster point `γ` of them in the pointwise topology (Tychonoff) satisfies
`b(γ u, γ v) ≤ b(x, y) (v - u)` for `u ≤ v`, by the continuity of `b`, and the bounded
asymmetry makes it Lipschitz for the symmetrized distance. Without the bound on the asymmetry
the limit need not be continuous (see the module docstring). -/
theorem IsFwdInterior.exists_fwdPath_length_eq_of_isCompact [T2Space X] (h : IsFwdInterior X)
    (x y : X) (hxy : bdist x y ≠ ⊤) (hK : IsCompact {z | bdist x z ≤ bdist x y + 1})
    (hasym : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ z ∈ {z | bdist x z ≤ bdist x y + 1},
      ∀ w ∈ {z | bdist x z ≤ bdist x y + 1}, bdist w z ≤ C * bdist z w) :
    ∃ p : FwdPath x y, p.length = bdist x y := by
  obtain ⟨C, hC, hCB⟩ := hasym
  set B := {z | bdist x z ≤ bdist x y + 1} with hB
  set d := (bdist x y).toReal with hd
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hbd : bdist x y = ENNReal.ofReal d := (ENNReal.ofReal_toReal hxy).symm
  -- Almost minimizing curves, reparametrized as forward Lipschitz maps on `[0, 1]`.
  have hpath : ∀ n : ℕ, ∃ η : ℝ → X, η 0 = x ∧ η 1 = y ∧ ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ v ∈ Icc (0 : ℝ) 1, u ≤ v →
        bdist (η u) (η v) ≤ ENNReal.ofReal ((d + 1 / (n + 1)) * (v - u)) := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp⟩ := h.exists_fwdPath (x := x) (y := y)
      (ε := ENNReal.ofReal (d + 1 / (n + 1))) (by
        rw [hbd]
        exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by positivity⟩)
    obtain ⟨η, h0, h1, hη⟩ := p.exists_lipschitz_reparam (ne_top_of_lt hp)
    have hL : p.length.toReal ≤ d + 1 / (n + 1) := (ENNReal.toReal_lt_of_lt_ofReal hp).le
    exact ⟨η, h0, h1, fun u hu v hv huv ↦ (hη u hu v hv huv).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hL (sub_nonneg.2 huv)))⟩
  choose η hη0 hη1 hηL using hpath
  have hinv : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n ↦
    (div_le_one (by positivity)).mpr (by linarith [n.cast_nonneg (α := ℝ)])
  set I := Icc (0 : ℝ) 1
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  -- All the curves stay in the forward ball `B`.
  have hmem : ∀ n (t : I), η n t ∈ B := by
    intro n t
    change bdist x (η n t) ≤ bdist x y + 1
    rw [hbd, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hd0 zero_le_one]
    conv_lhs => rw [← hη0 n]
    refine (hηL n 0 h0I t t.2 t.2.1).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sub_zero]
    have := mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ d + 1 / (n + 1)) t.2.2
    linarith [hinv n]
  -- A cluster point in the product topology.
  set u : ℕ → (I → X) := fun n t ↦ η n t
  obtain ⟨γ, hγB, hγ⟩ := (isCompact_univ_pi fun _ : I ↦ hK).exists_mapClusterPt (f := atTop)
    (u := u) (le_principal_iff.mpr <| mem_map.mpr <| univ_mem' fun n ↦
      mem_univ_pi.mpr fun t ↦ hmem n t)
  have hγB' : ∀ t : I, γ t ∈ B := fun t ↦ hγB t (mem_univ _)
  rw [mapClusterPt_iff_frequently] at hγ
  have happrox : ∀ (s t : I) (ε : ℝ≥0∞), 0 < ε → ∀ N : ℕ,
      ∃ n ≥ N, edist (η n s) (γ s) < ε ∧ edist (η n t) (γ t) < ε := by
    intro s t ε hε N
    have h1 : (fun f : I → X ↦ f s) ⁻¹' Metric.eball (γ s) ε ∈ 𝓝 γ :=
      (continuous_apply s).continuousAt.preimage_mem_nhds (Metric.eball_mem_nhds _ hε)
    have h2 : (fun f : I → X ↦ f t) ⁻¹' Metric.eball (γ t) ε ∈ 𝓝 γ :=
      (continuous_apply t).continuousAt.preimage_mem_nhds (Metric.eball_mem_nhds _ hε)
    have hnhds : {f : I → X | edist (f s) (γ s) < ε ∧ edist (f t) (γ t) < ε} ∈ 𝓝 γ :=
      inter_mem h1 h2
    obtain ⟨n, hn, hN⟩ := ((hγ _ hnhds).and_eventually (eventually_ge_atTop N)).exists
    exact ⟨n, hN, hn⟩
  -- The forward Lipschitz bound passes to the limit, by the continuity of `b`.
  have hlip : ∀ s t : I, (s : ℝ) ≤ t →
      bdist (γ s) (γ t) ≤ ENNReal.ofReal (d * ((t : ℝ) - s)) := by
    intro s t hst
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set δ : ℝ := (ε : ℝ) / 3
    have hδ : 0 < δ := by positivity
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    obtain ⟨n, hnN, hs, ht⟩ := happrox s t (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ) N
    have hnN' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnN 1)
    have hts : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hst
    have hc : 1 / ((n : ℝ) + 1) * ((t : ℝ) - s) ≤ 1 / ((n : ℝ) + 1) :=
      mul_le_of_le_one_right (by positivity) (by linarith [t.2.2, s.2.1])
    calc bdist (γ s) (γ t)
        ≤ bdist (η n s) (η n t) + edist (γ s) (η n s) + edist (γ t) (η n t) :=
          bdist_le_bdist_add_edist _ _ _ _
      _ ≤ ENNReal.ofReal ((d + 1 / (n + 1)) * ((t : ℝ) - s)) + ENNReal.ofReal δ +
            ENNReal.ofReal δ := by
          gcongr
          · exact hηL n s s.2 t t.2 hst
          · rw [edist_comm]; exact hs.le
          · rw [edist_comm]; exact ht.le
      _ ≤ ENNReal.ofReal (d * ((t : ℝ) - s) + δ) + ENNReal.ofReal δ + ENNReal.ofReal δ := by
          gcongr
          rw [add_mul]
          linarith
      _ = ENNReal.ofReal (d * ((t : ℝ) - s) + ε) := by
          rw [← ENNReal.ofReal_add (by positivity) hδ.le,
            ← ENNReal.ofReal_add (by positivity) hδ.le]
          congr 1
          simp only [δ]
          ring
      _ = ENNReal.ofReal (d * ((t : ℝ) - s)) + ε := by
          rw [ENNReal.ofReal_add (by positivity) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  -- The endpoints, identified through `T2Space X`.
  have hend : ∀ (t : I) (z : X), (∀ n, η n t = z) → γ t = z := by
    intro t z hz
    have h0 : edist z (γ t) = 0 := by
      by_contra hne
      obtain ⟨n, -, hn, -⟩ := happrox t t _ (pos_iff_ne_zero.2 hne) 0
      rw [hz n] at hn
      exact lt_irrefl _ hn
    exact (EMetric.inseparable_iff.2 h0).eq.symm
  -- Bounded asymmetry makes `γ` Lipschitz for the symmetrized distance.
  set M : ℝ≥0∞ := max 1 C
  have hM : M ≠ ⊤ := (max_lt ENNReal.one_lt_top hC.lt_top).ne
  have hsym : ∀ s t : I, (s : ℝ) ≤ t →
      edist (γ s) (γ t) ≤ M * ENNReal.ofReal (d * ((t : ℝ) - s)) := by
    intro s t hst
    rw [edist_eq_max_bdist]
    refine max_le ((hlip s t hst).trans (le_mul_of_one_le_left' (le_max_left _ _))) ?_
    exact (hCB _ (hγB' s) _ (hγB' t)).trans (mul_le_mul' (le_max_right _ _) (hlip s t hst))
  set f : ℝ → X := fun t ↦ if ht : t ∈ I then γ ⟨t, ht⟩ else x
  set K : ℝ≥0 := (M * ENNReal.ofReal d).toNNReal
  have hK' : (K : ℝ≥0∞) = M * ENNReal.ofReal d :=
    ENNReal.coe_toNNReal (ENNReal.mul_ne_top hM ENNReal.ofReal_ne_top)
  have hf : LipschitzOnWith K f I := by
    intro s hs t ht
    simp only [f, hs, ht, ↓reduceDIte]
    rw [hK', edist_dist, Real.dist_eq, mul_assoc, ← ENNReal.ofReal_mul hd0]
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)]
      exact hsym ⟨s, hs⟩ ⟨t, ht⟩ hst
    · rw [abs_of_nonneg (sub_nonneg.2 hts), edist_comm]
      exact hsym ⟨t, ht⟩ ⟨s, hs⟩ hts
  let p : FwdPath x y :=
    { toFun := f
      a := 0
      b := 1
      le := zero_le_one
      continuousOn := hf.continuousOn
      source := by simp only [f, h0I, ↓reduceDIte]; exact hend ⟨0, h0I⟩ x hη0
      target := by simp only [f, h1I, ↓reduceDIte]; exact hend ⟨1, h1I⟩ y hη1 }
  refine ⟨p, le_antisymm ?_ p.bdist_le_length⟩
  -- The forward sums telescope in the forward Lipschitz bound.
  change fwdVar f I ≤ _
  refine iSup_le ?_
  rintro ⟨n, v, hv, vs⟩
  dsimp only
  have htel : ∀ m : ℕ, ∑ i ∈ Finset.range m, bdist (f (v i)) (f (v (i + 1))) ≤
      ENNReal.ofReal (d * (v m - v 0)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hstep : bdist (f (v m)) (f (v (m + 1))) ≤ ENNReal.ofReal (d * (v (m + 1) - v m)) := by
        simp only [f, vs m, vs (m + 1), ↓reduceDIte]
        exact hlip ⟨v m, vs m⟩ ⟨v (m + 1), vs (m + 1)⟩ (hv (Nat.le_succ m))
      calc _ ≤ ENNReal.ofReal (d * (v m - v 0)) + ENNReal.ofReal (d * (v (m + 1) - v m)) :=
            add_le_add ih hstep
        _ = ENNReal.ofReal (d * (v (m + 1) - v 0)) := by
            rw [← ENNReal.ofReal_add (mul_nonneg hd0 (sub_nonneg.2 (hv (Nat.zero_le m))))
              (mul_nonneg hd0 (sub_nonneg.2 (hv (Nat.le_succ m))))]
            congr 1
            ring
  refine (htel n).trans ?_
  rw [hbd]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right hd0 (by linarith [(vs n).2, (vs 0).1]))

end LCManifolds

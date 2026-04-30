import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators


-- ============================================================
-- STRUCTURES
-- ============================================================

structure STVertices (V : Type*) [Fintype V] where
  s : V
  t : V
  source_not_sink : s ≠ t

structure FlowNetwork (V : Type*) [Fintype V] extends STVertices V where
  c : V → V → ℝ
  nonneg_capacity : ∀ u v : V, c u v ≥ 0

open Classical in
noncomputable
def mk_in {V : Type*} [Fintype V]
    (f : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ Finset.univ \ S, ∑ y ∈ S, f x y

open Classical in
noncomputable
def mk_out {V : Type*} [Fintype V]
    (f : V → V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Finset.univ \ S, f x y

lemma lin_in {V : Type*} [Fintype V] (f g : V → V → ℝ) (S : Finset V) :
 mk_in f S + mk_in g S = mk_in (f + g) S := by
  simp [mk_in, sum_add_distrib];

lemma lin_out {V : Type*} [Fintype V] (f g : V → V → ℝ) (S : Finset V) :
mk_out f S + mk_out g S = mk_out (f + g) S := by
  simp [mk_out, sum_add_distrib];

structure RelaxedFlow (V : Type*) [Fintype V] (G : STVertices V) where
  f : V → V → ℝ
  nonneg_flow : ∀ u v : V, f u v ≥ 0
  conservation : ∀ v : V, v ≠ G.s → v ≠ G.t → mk_out f {v} = mk_in f {v}
  no_edges_in_source : ∀ u : V, f u G.s = 0
  no_edges_out_sink : ∀ u : V, f G.t u = 0

def ValidFlow
(V : Type*) [Fintype V] (G : FlowNetwork V) (g : RelaxedFlow V G.toSTVertices) : Prop :=
  ∀ u v : V, g.f u v ≤ G.c u v

lemma eq_conservation (V : Type*) [Fintype V] (G : STVertices V) (flow : RelaxedFlow V G) :
 ∀ v : V, v ≠ G.s → v ≠ G.t → ∑ x, (flow.f x v - flow.f v x) = 0 := by
  intro v vns vnt
  have : mk_out flow.f {v} = mk_in flow.f {v} := flow.conservation v vns vnt
  unfold mk_in mk_out at this
  simp at this
  simp [this]

instance (V : Type*) [Fintype V] (G : STVertices V) : Mul (RelaxedFlow V G) where
  mul g h := {
    f u v := max (g.f u v + h.f u v - g.f v u - h.f v u) 0
    nonneg_flow := by simp
    conservation := by
      intro v vns vnt
      simp only [mk_out, subset_univ, sum_sdiff_eq_sub, sum_singleton, sum_sub_distrib,
      add_sub_cancel_left, sub_self, max_self, sub_zero, mk_in]
      have h₁: ∑ x, (max (g.f x v + h.f x v - g.f v x - h.f v x) 0
        - max (-(g.f x v + h.f x v - g.f v x - h.f v x)) 0) = 0 := by
        simp only [max_zero_sub_max_neg_zero_eq_self (g.f _ v + h.f _ v - g.f v _ - h.f v _)]
        calc
          ∑ x, (g.f x v + h.f x v - g.f v x - h.f v x)
          = ∑ x, (g.f x v - g.f v x) + ∑ x, (h.f x v - h.f v x) := by
            simp [Finset.sum_add_distrib]; linarith
          _ = 0 := by
            simp only [add_eq_right, eq_conservation V G g v vns vnt,
              eq_conservation V G h v vns vnt];
      symm
      rw [←sub_eq_zero]
      have : ∀ x, -(g.f x v + h.f x v - g.f v x - h.f v x)
        = (g.f v x + h.f v x - g.f x v - h.f x v) := by
        intro x; ring
      simp only [this, sum_sub_distrib] at h₁
      exact h₁
    no_edges_in_source := by
      intro u;
      simp [g.no_edges_in_source, h.no_edges_in_source];
      linarith [g.nonneg_flow G.s u, h.nonneg_flow G.s u]
    no_edges_out_sink := by
      intro u; simp [g.no_edges_out_sink, h.no_edges_out_sink];
      linarith [g.nonneg_flow u G.t, h.nonneg_flow u G.t]
    }

noncomputable
def Flow_value {V : Type*} [Fintype V] (G : STVertices V)
    (flow : RelaxedFlow V G) : ℝ := mk_out flow.f {G.s}

lemma nonneg_flow_value {V : Type*} [Fintype V] (G : STVertices V) :
  ∀F : RelaxedFlow V G, Flow_value G F ≥ 0 := by
  intro F; simp [Flow_value, mk_out, F.no_edges_in_source, sum_nonneg, F.nonneg_flow]

lemma add_flow {V : Type*} [Fintype V] (G : STVertices V) (flow₁ flow₂ : RelaxedFlow V G) :
  Flow_value G (flow₁ * flow₂) = Flow_value G flow₁ + Flow_value G flow₂ := by
  have: ∀ x, (flow₁.f G.s x + flow₂.f G.s x) ≥ 0 := by
    intro x; linarith [flow₁.nonneg_flow G.s x, flow₂.nonneg_flow G.s x]
  simp [Flow_value, (· * ·), Mul.mul, mk_out,
   flow₁.no_edges_in_source, flow₂.no_edges_in_source, this, sum_add_distrib]

open Classical in
structure Cut (V : Type*) [Fintype V] (G : FlowNetwork V) where
  S : Finset V
  T : Finset V := univ \ S
  sins : G.s ∈ S
  tint : G.t ∈ T

noncomputable
def cut_cap {V : Type*} [Fintype V] {G : FlowNetwork V}
    (c : Cut V G) : ℝ := mk_out G.c c.S

def is_max_flow {V : Type*} [Fintype V] {G : FlowNetwork V}
    (fn : RelaxedFlow V G.toSTVertices) : Prop :=
  ValidFlow V G fn ∧ ∀ fn' : RelaxedFlow V G.toSTVertices, ValidFlow V G fn' →
    Flow_value G.toSTVertices fn' ≤ Flow_value G.toSTVertices fn

def is_min_cut {V : Type*} [Fintype V] (G : FlowNetwork V)
    (fn : Cut V G) : Prop :=
  ∀ fn' : Cut V G, cut_cap fn ≤ cut_cap fn'

def ResidualNetwork {V : Type*} [Fintype V] (G : FlowNetwork V) (F : RelaxedFlow V G.toSTVertices)
  (h : ValidFlow V G F) : FlowNetwork V where
  s := G.s
  t := G.t
  source_not_sink := G.source_not_sink
  c u v := G.c u v - F.f u v + F.f v u
  nonneg_capacity := by intro u v; simp; linarith [h u v, F.nonneg_flow v u]

lemma valid_augmentation {V : Type*} [Fintype V] (G : FlowNetwork V)
  (F : RelaxedFlow V G.toSTVertices) (h : ValidFlow V G F) :
  ∀F' : (RelaxedFlow V G.toSTVertices), ValidFlow V (ResidualNetwork G F h) F' →
  ∀ u v : V, (F * F').f u v ≤ G.c u v := by
  intro F' val_F' u v
  simp [(· * ·), Mul.mul]
  constructor
  · have : F'.f u v ≤ G.c u v - F.f u v + F.f v u := by exact val_F' u v
    linarith [F'.nonneg_flow v u, F.nonneg_flow u v]
  · linarith [G.nonneg_capacity u v]

lemma max_flow_no_augmenting {V : Type*} [Fintype V] (G : FlowNetwork V)
  (F : RelaxedFlow V G.toSTVertices) (h : is_max_flow F) :
  ∀F' : (RelaxedFlow V G.toSTVertices), ValidFlow V (ResidualNetwork G F h.1) F' →
  Flow_value G.toSTVertices F' = 0 := by
  intro F' g
  by_contra con
  push Not at con
  have: Flow_value G.toSTVertices F' > 0 := by
   apply lt_of_le_of_ne;
   · linarith [nonneg_flow_value G.toSTVertices F']
   · symm; exact con
  let optF := F * F'
  have optge : Flow_value G.toSTVertices optF > Flow_value G.toSTVertices F := by calc
   Flow_value G.toSTVertices optF = Flow_value G.toSTVertices F + Flow_value G.toSTVertices F' :=
   by exact add_flow G.toSTVertices F F'
   _ > Flow_value G.toSTVertices F := by linarith
  have optval : ValidFlow V G optF := by
   apply valid_augmentation G F h.1 F' g
  have: ¬is_max_flow F := by
   simp only [is_max_flow, not_and, not_forall, not_le]; intro _; use optF;
  contradiction

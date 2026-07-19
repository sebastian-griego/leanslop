import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth2

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 2. -/
axiom provided_exists_top (s : PointedCone ℝ E) (p : E →ₗ.[ℝ] ℝ)
    (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
    ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  have N_zero : N (0 : E) = 0 := by
    have h := N_hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  let c : ConvexCone ℝ (E × ℝ) :=
    { carrier := {z | z = 0 ∨ N z.1 < z.2}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro a b ha hb
        rcases ha with ha | ha
        · subst a
          simpa using hb
        rcases hb with hb | hb
        · subst b
          simpa using ha
        right
        have h := N_add a.1 b.1
        change N (a.1 + b.1) < a.2 + b.2
        linarith
      smul_mem' := by
        intro r hr z hz
        rcases eq_or_lt_of_le hr with rfl | hr
        · left
          simp
        rcases hz with hz | hz
        · subst z
          left
          simp
        right
        change N (r • z.1) < r * z.2
        rw [N_hom r hr]
        exact mul_lt_mul_of_pos_left hz hr }
  let s : PointedCone ℝ (E × ℝ) := by
    refine ⟨c, ?_⟩
    intro z hz hnz
    rcases hz with hz | hz
    · exact hz
    rcases hnz with hnz | hnz
    · simpa using congrArg Neg.neg hnz
    exfalso
    change N (-z.1) < -z.2 at hnz
    have h := N_add z.1 (-z.1)
    rw [add_neg_cancel, N_zero] at h
    linarith
  let p : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toLinearMap :=
        { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
          map_add' := by
            intro x y
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          map_smul' := by
            intro r x
            simp [mul_sub] } }
  have hp_nonneg :
      ∀ z : p.domain, (z : E × ℝ) ∈ s → 0 ≤ p z := by
    intro z hz
    change (z : E × ℝ) = 0 ∨ N z.1.1 < z.1.2 at hz
    rcases hz with hz | hz
    · have hz' : z = 0 := Subtype.ext hz
      subst z
      simp [p]
    · have hfz := hf ⟨z.1.1, z.2.1⟩
      change f ⟨z.1.1, z.2.1⟩ ≤ N z.1.1 at hfz
      change 0 ≤ z.1.2 - f ⟨z.1.1, z.2.1⟩
      linarith
  have hp_dense :
      ∀ y, ∃ x : p.domain, (x : E × ℝ) + y ∈ s := by
    intro y
    let a : E × ℝ := (0, N y.1 - y.2 + 1)
    have ha : a ∈ p.domain := by
      change (0 : E) ∈ f.domain ∧
        (N y.1 - y.2 + 1 : ℝ) ∈ (⊤ : Submodule ℝ ℝ)
      simp
    refine ⟨⟨a, ha⟩, ?_⟩
    change a + y = 0 ∨ N (a + y).1 < (a + y).2
    right
    dsimp [a]
    simp only [zero_add]
    linarith
  rcases provided_exists_top s p hp_nonneg hp_dense with
    ⟨q, hpq, hqtop, hq_nonneg⟩
  rcases hpq with ⟨hpq_dom, hpq_rest⟩
  have hpq_val (z : p.domain) :
      p z = q ⟨(z : E × ℝ), hpq_dom z.property⟩ := by
    first
    | simpa using hpq_rest z
    | simpa using (hpq_rest z).symm
    | simpa using congrArg (fun L => L z) hpq_rest
    | simpa using (congrArg (fun L => L z) hpq_rest).symm
  have hqmem (z : E × ℝ) : z ∈ q.domain := by
    rw [hqtop]
    exact Submodule.mem_top
  let Q : (E × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => q ⟨z, hqmem z⟩
      map_add' := by
        intro x y
        change q ⟨x + y, hqmem (x + y)⟩ =
          q ⟨x, hqmem x⟩ + q ⟨y, hqmem y⟩
        simpa using q.map_add ⟨x, hqmem x⟩ ⟨y, hqmem y⟩
      map_smul' := by
        intro r x
        change q ⟨r • x, hqmem (r • x)⟩ = r • q ⟨x, hqmem x⟩
        simpa using q.map_smul r ⟨x, hqmem x⟩ }
  have hQp (z : p.domain) : Q (z : E × ℝ) = p z := by
    change q ⟨(z : E × ℝ), hqmem (z : E × ℝ)⟩ = p z
    exact (hpq_val z).symm
  have Q_vertical (t : ℝ) : Q (0, t) = t := by
    have hz : ((0 : E), t) ∈ p.domain := by
      change (0 : E) ∈ f.domain ∧ t ∈ (⊤ : Submodule ℝ ℝ)
      simp
    have h := hQp ⟨((0 : E), t), hz⟩
    simpa [p] using h
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -Q (x, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hx : (((x : E), 0 : ℝ)) ∈ p.domain := by
      change (x : E) ∈ f.domain ∧ (0 : ℝ) ∈ (⊤ : Submodule ℝ ℝ)
      simp [x.property]
    have h := hQp ⟨((x : E), 0), hx⟩
    change -Q ((x : E), 0) = f x
    simpa [p] using congrArg Neg.neg h
  · intro x
    by_contra hle
    have hlt : N x < g x := lt_of_not_ge hle
    let t : ℝ := (N x + g x) / 2
    have hNt : N x < t := by
      dsimp [t]
      linarith
    have hzt : (x, t) ∈ s := by
      change (x, t) = 0 ∨ N x < t
      exact Or.inr hNt
    have hnon : 0 ≤ Q (x, t) := by
      have h := hq_nonneg ⟨(x, t), hqmem (x, t)⟩ hzt
      simpa [Q] using h
    have hdecomp : Q (x, t) = Q (x, 0) + t := by
      calc
        Q (x, t) = Q ((x, 0) + (0, t)) := by simp
        _ = Q (x, 0) + Q (0, t) := Q.map_add _ _
        _ = Q (x, 0) + t := by rw [Q_vertical]
    have hgQ : g x = -Q (x, 0) := rfl
    dsimp [t] at hNt ⊢
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth2

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
  let s : PointedCone ℝ (E × ℝ) :=
    { toAddSubmonoid :=
        { carrier := {z | N z.1 ≤ z.2}
          zero_mem' := by
            change N (0 : E) ≤ (0 : ℝ)
            rw [N_zero]
          add_mem' := by
            intro x y hx hy
            change N (x.1 + y.1) ≤ x.2 + y.2
            have h := N_add x.1 y.1
            linarith }
      smul_mem' := by
        intro r x hx
        change N x.1 ≤ x.2 at hx
        rcases eq_or_lt_of_le r.property with hr | hr
        · have hr0 : r = 0 := Subtype.ext hr.symm
          subst r
          simpa [N_zero]
        · change N ((r : ℝ) • x.1) ≤ (r : ℝ) * x.2
          rw [N_hom (r : ℝ) hr]
          exact mul_le_mul_of_nonneg_left hx r.property }
  let p : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toFun :=
        { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
          map_add' := by
            intro x y
            have h :=
              f.map_add
                ⟨x.1.1, x.2.1⟩
                ⟨y.1.1, y.2.1⟩
            change
              f ⟨x.1.1 + y.1.1, _⟩ =
                f ⟨x.1.1, _⟩ + f ⟨y.1.1, _⟩ at h
            change
              (x.1.2 + y.1.2) - f ⟨x.1.1 + y.1.1, _⟩ =
                (x.1.2 - f ⟨x.1.1, _⟩) +
                  (y.1.2 - f ⟨y.1.1, _⟩)
            rw [h]
            ring
          map_smul' := by
            intro r x
            have h := f.map_smul r ⟨x.1.1, x.2.1⟩
            change
              f ⟨r • x.1.1, _⟩ =
                r * f ⟨x.1.1, _⟩ at h
            change
              r * x.1.2 - f ⟨r • x.1.1, _⟩ =
                r * (x.1.2 - f ⟨x.1.1, _⟩)
            rw [h]
            ring } }
  have hp_nonneg :
      ∀ z : p.domain, (z : E × ℝ) ∈ s → 0 ≤ p z := by
    intro z hz
    change N z.1.1 ≤ z.1.2 at hz
    have hfz := hf ⟨z.1.1, z.2.1⟩
    change f ⟨z.1.1, z.2.1⟩ ≤ N z.1.1 at hfz
    change 0 ≤ z.1.2 - f ⟨z.1.1, z.2.1⟩
    linarith
  have hp_dense :
      ∀ y, ∃ x : p.domain, (x : E × ℝ) + y ∈ s := by
    intro y
    let a : E × ℝ := (0, N y.1 - y.2)
    have ha : a ∈ p.domain := by
      change (0 : E) ∈ f.domain ∧
        (N y.1 - y.2 : ℝ) ∈ (⊤ : Submodule ℝ ℝ)
      simp
    refine ⟨⟨a, ha⟩, ?_⟩
    change N (a + y).1 ≤ (a + y).2
    dsimp [a]
    simp only [zero_add]
    linarith
  rcases provided_exists_top s p hp_nonneg hp_dense with
    ⟨q, hpq, hqtop, hq_nonneg⟩
  rcases hpq with ⟨hpq_dom, hpq_rest⟩
  have hpq_val (z : p.domain) :
      p z = q ⟨(z : E × ℝ), hpq_dom z.property⟩ := by
    exact hpq_rest rfl
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
        change q ⟨r • x, hqmem (r • x)⟩ =
          r • q ⟨x, hqmem x⟩
        simpa using q.map_smul r ⟨x, hqmem x⟩ }
  have hQp (z : p.domain) : Q (z : E × ℝ) = p z := by
    change q ⟨(z : E × ℝ), hqmem (z : E × ℝ)⟩ = p z
    simpa using (hpq_val z).symm
  have Q_vertical (t : ℝ) : Q (0, t) = t := by
    have hz : ((0 : E), t) ∈ p.domain := by
      change (0 : E) ∈ f.domain ∧ t ∈ (⊤ : Submodule ℝ ℝ)
      simp
    have h := hQp ⟨((0 : E), t), hz⟩
    change
      Q (0, t) =
        t - f ⟨(0 : E), Submodule.zero_mem f.domain⟩ at h
    rw [f.map_zero] at h
    simpa using h
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -Q (x, 0)
      map_add' := by
        intro x y
        calc
          -Q (x + y, 0) =
              -Q (((x, 0) : E × ℝ) + ((y, 0) : E × ℝ)) := by
                simp
          _ = -(Q (x, 0) + Q (y, 0)) := by
                rw [Q.map_add]
          _ = -Q (x, 0) + -Q (y, 0) := by
                ring
      map_smul' := by
        intro r x
        calc
          -Q (r • x, 0) =
              -Q (r • ((x, 0) : E × ℝ)) := by
                simp
          _ = -(r • Q (x, 0)) := by
                rw [Q.map_smul]
          _ = r • (-Q (x, 0)) := by
                simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hx : ((x : E), (0 : ℝ)) ∈ p.domain := by
      change (x : E) ∈ f.domain ∧
        (0 : ℝ) ∈ (⊤ : Submodule ℝ ℝ)
      exact ⟨x.property, Submodule.mem_top⟩
    have h := hQp ⟨((x : E), (0 : ℝ)), hx⟩
    change -Q ((x : E), 0) = f x
    simpa [p] using congrArg Neg.neg h
  · intro x
    have hxs : ((x, N x) : E × ℝ) ∈ s := by
      change N x ≤ N x
      exact le_rfl
    have hnon : 0 ≤ Q (x, N x) := by
      have h :=
        hq_nonneg ⟨(x, N x), hqmem (x, N x)⟩ hxs
      simpa [Q] using h
    have hdecomp : Q (x, N x) = Q (x, 0) + N x := by
      calc
        Q (x, N x) =
            Q (((x, 0) : E × ℝ) + ((0, N x) : E × ℝ)) := by
              simp
        _ = Q (x, 0) + Q (0, N x) := Q.map_add _ _
        _ = Q (x, 0) + N x := by
          rw [Q_vertical]
    have hgQ : g x = -Q (x, 0) := rfl
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth2

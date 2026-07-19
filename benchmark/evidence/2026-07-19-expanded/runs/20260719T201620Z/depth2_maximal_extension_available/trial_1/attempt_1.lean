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
    have h := N_hom (2 : ℝ) (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        simpa [N_zero]
      add_mem' := by
        intro x y hx hy
        change N (x.1 + y.1) ≤ x.2 + y.2
        exact (N_add x.1 y.1).trans (add_le_add hx hy)
      smul_mem' := by
        intro c hc x hx
        rcases eq_or_lt_of_le hc with hzero | hpos
        · subst c
          simpa [N_zero]
        · change N (c • x.1) ≤ c * x.2
          rw [N_hom c hpos x.1]
          exact mul_le_mul_of_nonneg_left hx hc }
  let D : Submodule ℝ (E × ℝ) :=
    { carrier := {z | z.1 ∈ f.domain}
      zero_mem' := f.domain.zero_mem
      add_mem' := by
        intro x y hx hy
        exact f.domain.add_mem hx hy
      smul_mem' := by
        intro c x hx
        exact f.domain.smul_mem c hx }
  let fstD : D →ₗ[ℝ] f.domain :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let sndD : D →ₗ[ℝ] ℝ :=
    { toFun := fun z => z.1.2
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  let p : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := D
      toLinearMap := sndD - f.toLinearMap.comp fstD }
  obtain ⟨q, hpq, hqtop, hqpos⟩ :=
    provided_exists_top (E := E × ℝ) s p
      (by
        intro x hx
        change N x.1.1 ≤ x.1.2 at hx
        change 0 ≤ x.1.2 - f ⟨x.1.1, x.2⟩
        exact sub_nonneg.mpr ((hf _).trans hx))
      (by
        intro y
        let x : p.domain :=
          ⟨((0 : E), N y.1 - y.2), by
            change (0 : E) ∈ f.domain
            exact f.domain.zero_mem⟩
        refine ⟨x, ?_⟩
        change N ((0 : E) + y.1) ≤ (N y.1 - y.2) + y.2
        simp)
  rcases hpq with ⟨hpq_dom, hpq_eq⟩
  let Q : (E × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => q ⟨z, by simpa [hqtop]⟩
      map_add' := by
        intro x y
        simpa only using
          (q.map_add
            (⟨x, by simpa [hqtop]⟩ : q.domain)
            (⟨y, by simpa [hqtop]⟩ : q.domain))
      map_smul' := by
        intro c x
        simpa only using
          (q.map_smul c (⟨x, by simpa [hqtop]⟩ : q.domain)) }
  have Q_on_p (x : p.domain) : Q (x : E × ℝ) = p x := by
    have h := congrArg (fun L => L x) hpq_eq
    change p x = q ⟨(x : E × ℝ), hpq_dom x.2⟩ at h
    change q ⟨(x : E × ℝ), by simpa [hqtop]⟩ = p x
    simpa using h.symm
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -Q (x, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : p.domain :=
      ⟨((x : E), 0), by
        change (x : E) ∈ f.domain
        exact x.2⟩
    have hz := Q_on_p z
    change -Q ((x : E), 0) = f x
    simpa [p, sndD, fstD] using congrArg Neg.neg hz
  · intro x
    have hver : Q ((0 : E), N x) = N x := by
      let z : p.domain :=
        ⟨((0 : E), N x), by
          change (0 : E) ∈ f.domain
          exact f.domain.zero_mem⟩
      simpa [p, sndD, fstD] using Q_on_p z
    have hpos : 0 ≤ Q (x, N x) := by
      let z : q.domain :=
        ⟨(x, N x), by simpa [hqtop]⟩
      have hz := hqpos z (by
        change N x ≤ N x
        exact le_rfl)
      simpa [Q] using hz
    have hsplit : Q (x, N x) = Q (x, 0) + Q (0, N x) := by
      simpa using Q.map_add (x, 0) (0, N x)
    change -Q (x, 0) ≤ N x
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth2

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
  have hN0 : N (0 : E) = 0 := by
    have h := N_hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  have hNneg (x : E) : 0 ≤ N x + N (-x) := by
    have h := N_add x (-x)
    have h' : N 0 ≤ N x + N (-x) := by simpa using h
    simpa [hN0] using h'
  let s : PointedCone ℝ (ℝ × E) :=
    ⟨
      { carrier := {z | z = 0 ∨ N z.2 < z.1}
        zero_mem' := Or.inl rfl
        add_mem' := by
          intro x y hx hy
          rcases hx with hx | hx
          · subst x
            simpa using hy
          rcases hy with hy | hy
          · subst y
            simpa using hx
          right
          change N (x.2 + y.2) < x.1 + y.1
          have h := N_add x.2 y.2
          linarith
        smul_mem' := by
          intro c hc x hx
          by_cases hc0 : c = 0
          · subst c
            left
            simp
          have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
          rcases hx with hx | hx
          · subst x
            left
            simp
          right
          change N (c • x.2) < c * x.1
          rw [N_hom c hcpos]
          exact mul_lt_mul_of_pos_left hx hcpos },
      by
        intro x hx hnx
        rcases hx with hx | hx
        · exact hx
        rcases hnx with hnx | hnx
        · exact neg_eq_zero.mp hnx
        have h := hNneg x.2
        change N (-x.2) < -x.1 at hnx
        linarith⟩
  let D : Submodule ℝ (ℝ × E) :=
    { carrier := {z | z.2 ∈ f.domain}
      zero_mem' := f.domain.zero_mem
      add_mem' := by
        intro x y hx hy
        exact f.domain.add_mem hx hy
      smul_mem' := by
        intro c x hx
        exact f.domain.smul_mem c hx }
  let p : (ℝ × E) →ₗ.[ℝ] ℝ :=
    { domain := D
      toLinearMap :=
        { toFun := fun z => z.1.1 - f ⟨z.1.2, z.2⟩
          map_add' := by
            intro x y
            simp [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          map_smul' := by
            intro c x
            simp [map_smul] <;> ring } }
  have hp_nonneg :
      ∀ x : p.domain, (x : ℝ × E) ∈ s → 0 ≤ p x := by
    rintro ⟨⟨r, x⟩, hxdom⟩ hx
    change x ∈ f.domain at hxdom
    change (r, x) = 0 ∨ N x < r at hx
    change 0 ≤ r - f ⟨x, hxdom⟩
    rcases hx with hx | hx
    · have hr : r = 0 := by
        simpa using congrArg Prod.fst hx
      have he : x = 0 := by
        simpa using congrArg Prod.snd hx
      subst r
      subst x
      simp
    · have hfx := hf ⟨x, hxdom⟩
      linarith
  have hp_dense :
      ∀ y, ∃ x : p.domain, (x : ℝ × E) + y ∈ s := by
    intro y
    let a : ℝ := N y.2 - y.1 + 1
    let x : p.domain :=
      ⟨(a, 0), by
        change (0 : E) ∈ f.domain
        exact f.domain.zero_mem⟩
    refine ⟨x, ?_⟩
    change (a + y.1, y.2) = 0 ∨ N y.2 < a + y.1
    right
    dsimp [a]
    linarith
  obtain ⟨q, hqp, hqdom, hqpos⟩ :=
    provided_exists_top s p hp_nonneg hp_dense
  rcases hqp with ⟨hDq, hext⟩
  let incl : (ℝ × E) →ₗ[ℝ] q.domain :=
    { toFun := fun z =>
        ⟨z, by
          rw [hqdom]
          exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let Q : (ℝ × E) →ₗ[ℝ] ℝ := q.toLinearMap.comp incl
  have hQp (x : p.domain) : Q (x : ℝ × E) = p x := by
    change q (incl (x : ℝ × E)) = p x
    calc
      q (incl (x : ℝ × E)) =
          q ⟨(x : ℝ × E), hDq x.2⟩ := by
            congr 1
      _ = p x := (hext x).symm
  have hQr0 (r : ℝ) : Q (r, (0 : E)) = r := by
    let z : p.domain :=
      ⟨(r, 0), by
        change (0 : E) ∈ f.domain
        exact f.domain.zero_mem⟩
    have hz := hQp z
    simpa [p, z] using hz
  have hQ0 (x : f.domain) :
      Q (0, (x : E)) = -f x := by
    let z : p.domain :=
      ⟨(0, (x : E)), by
        change (x : E) ∈ f.domain
        exact x.2⟩
    have hz := hQp z
    simpa [p, z] using hz
  let g : E →ₗ[ℝ] ℝ :=
    { toFun := fun x => -Q (0, x)
      map_add' := by
        intro x y
        rw [show (0, x + y) = (0, x) + (0, y) by simp, map_add]
        ring
      map_smul' := by
        intro c x
        rw [show (0, c • x) = c • (0, x) by simp, map_smul]
        simp }
  refine ⟨g, ?_, ?_⟩
  · intro x
    change -Q (0, (x : E)) = f x
    rw [hQ0 x]
    simp
  · intro x
    by_contra hx
    have hlt : N x < g x := lt_of_not_ge hx
    let r : ℝ := (N x + g x) / 2
    have hNr : N x < r := by
      dsimp [r]
      linarith
    have hrg : r < g x := by
      dsimp [r]
      linarith
    have hpos : 0 ≤ Q (r, x) := by
      change 0 ≤ q (incl (r, x))
      exact hqpos (incl (r, x)) (by
        change (r, x) = 0 ∨ N x < r
        exact Or.inr hNr)
    have hdecomp : Q (r, x) = r - g x := by
      calc
        Q (r, x) = Q ((r, 0) + (0, x)) := by simp
        _ = Q (r, 0) + Q (0, x) := by rw [map_add]
        _ = r - g x := by
          rw [hQr0]
          simp [g]
    rw [hdecomp] at hpos
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth2

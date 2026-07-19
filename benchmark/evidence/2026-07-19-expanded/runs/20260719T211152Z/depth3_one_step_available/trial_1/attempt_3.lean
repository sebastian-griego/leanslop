import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth3

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Available frontier at redaction depth 3. -/
axiom provided_step (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

lemma exists_maximal_positive (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (hf : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) :
    ∃ g, f ≤ g ∧
      (∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x) ∧
      ∀ h, g < h → ¬∀ x : h.domain, (x : E) ∈ s → 0 ≤ h x := by
  classical
  let P : Set (E →ₗ.[ℝ] ℝ) :=
    {g | f ≤ g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x}
  have hfP : f ∈ P := ⟨le_rfl, hf⟩
  let Q := {g : E →ₗ.[ℝ] ℝ // g ∈ P}
  letI : Nonempty Q := ⟨⟨f, hfP⟩⟩
  obtain ⟨m, hm⟩ := zorn_le_nonempty (α := Q) (by
    intro c hchain hc
    let D : Submodule ℝ E :=
      { carrier := {x | ∃ q ∈ c, x ∈ q.1.domain}
        zero_mem' := by
          obtain ⟨q, hqc⟩ := hc
          exact ⟨q, hqc, q.1.domain.zero_mem⟩
        add_mem' := by
          rintro x y ⟨q, hqc, hx⟩ ⟨r, hrc, hy⟩
          rcases hchain.total hqc hrc with hqr | hrq
          · exact ⟨r, hrc, r.1.domain.add_mem (hqr.1 hx) hy⟩
          · exact ⟨q, hqc, q.1.domain.add_mem hx (hrq.1 hy)⟩
        smul_mem' := by
          rintro a x ⟨q, hqc, hx⟩
          exact ⟨q, hqc, q.1.domain.smul_mem a hx⟩ }
    let v : D → ℝ := fun x =>
      let q := Classical.choose x.property
      q.1 ⟨x, (Classical.choose_spec x.property).2⟩
    have v_eq (x : D) (q : Q) (hqc : q ∈ c)
        (hx : (x : E) ∈ q.1.domain) :
        v x = q.1 ⟨x, hx⟩ := by
      let p : Q := Classical.choose x.property
      have hpc : p ∈ c := (Classical.choose_spec x.property).1
      have hpx : (x : E) ∈ p.1.domain :=
        (Classical.choose_spec x.property).2
      rcases hchain.total hpc hqc with hpq | hqp
      · exact hpq.2 rfl
      · exact (hqp.2 rfl).symm
    let vlm : D →ₗ[ℝ] ℝ :=
      { toFun := v
        map_add' := by
          intro x y
          let q : Q := Classical.choose x.property
          let r : Q := Classical.choose y.property
          have hqc : q ∈ c := (Classical.choose_spec x.property).1
          have hrc : r ∈ c := (Classical.choose_spec y.property).1
          have hxq : (x : E) ∈ q.1.domain :=
            (Classical.choose_spec x.property).2
          have hyr : (y : E) ∈ r.1.domain :=
            (Classical.choose_spec y.property).2
          change v (x + y) = v x + v y
          rcases hchain.total hqc hrc with hqr | hrq
          · have hxr : (x : E) ∈ r.1.domain := hqr.1 hxq
            rw [v_eq (x + y) r hrc (r.1.domain.add_mem hxr hyr),
              v_eq x r hrc hxr, v_eq y r hrc hyr]
            exact r.1.map_add ⟨x, hxr⟩ ⟨y, hyr⟩
          · have hyq : (y : E) ∈ q.1.domain := hrq.1 hyr
            rw [v_eq (x + y) q hqc (q.1.domain.add_mem hxq hyq),
              v_eq x q hqc hxq, v_eq y q hqc hyq]
            exact q.1.map_add ⟨x, hxq⟩ ⟨y, hyq⟩
        map_smul' := by
          intro a x
          let q : Q := Classical.choose x.property
          have hqc : q ∈ c := (Classical.choose_spec x.property).1
          have hxq : (x : E) ∈ q.1.domain :=
            (Classical.choose_spec x.property).2
          change v (a • x) = a • v x
          rw [v_eq (a • x) q hqc (q.1.domain.smul_mem a hxq),
            v_eq x q hqc hxq]
          exact q.1.map_smul a ⟨x, hxq⟩ }
    let u : E →ₗ.[ℝ] ℝ :=
      { domain := D
        toFun := vlm }
    have hub : ∀ q ∈ c, q.1 ≤ u := by
      intro q hqc
      refine ⟨?_, ?_⟩
      · intro x hx
        exact ⟨q, hqc, hx⟩
      · intro x y hxy
        have hy : (y : E) ∈ q.1.domain := by
          rw [← hxy]
          exact x.property
        change q.1 x = v y
        rw [v_eq y q hqc hy]
        congr 1
        exact Subtype.ext hxy
    have huP : u ∈ P := by
      refine ⟨?_, ?_⟩
      · obtain ⟨q, hqc⟩ := hc
        exact q.property.1.trans (hub q hqc)
      · intro x hxs
        obtain ⟨q, hqc, hxq⟩ := x.property
        change 0 ≤ v x
        rw [v_eq x q hqc hxq]
        exact q.property.2 ⟨x, hxq⟩ hxs
    refine ⟨⟨u, huP⟩, ?_⟩
    intro q hqc
    exact hub q hqc)
  refine ⟨m.1, m.2.1, m.2.2, ?_⟩
  intro h hmh hh
  have hhP : h ∈ P := ⟨m.2.1.trans hmh.le, hh⟩
  exact (not_le_of_gt hmh) (hm ⟨h, hhP⟩ hmh.le)

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  have N_zero : N (0 : E) = 0 := by
    have h := N_hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at h
    linarith
  let s : PointedCone ℝ (E × ℝ) :=
    { carrier := {z | N z.1 ≤ z.2}
      zero_mem' := by
        simpa [N_zero]
      add_mem' := by
        rintro ⟨x, a⟩ ⟨y, b⟩ hx hy
        exact (N_add x y).trans (add_le_add hx hy)
      smul_mem' := by
        rintro ⟨c, hc⟩ ⟨x, a⟩ hx
        change N (c • x) ≤ c * a
        rcases hc.eq_or_lt with rfl | hc
        · simpa [N_zero]
        · rw [N_hom c hc x]
          exact mul_le_mul_of_nonneg_left hx hc.le }
  let F : (E × ℝ) →ₗ.[ℝ] ℝ :=
    { domain := f.domain.prod ⊤
      toFun :=
        { toFun := fun z => z.1.2 - f ⟨z.1.1, z.2.1⟩
          map_add' := by
            intro x y
            simp
            ring
          map_smul' := by
            intro c x
            simp
            ring } }
  have hF : ∀ z : F.domain, (z : E × ℝ) ∈ s → 0 ≤ F z := by
    rintro ⟨⟨x, a⟩, hx⟩ hz
    change N x ≤ a at hz
    change 0 ≤ a - f ⟨x, hx.1⟩
    exact sub_nonneg.mpr ((hf ⟨x, hx.1⟩).trans hz)
  obtain ⟨G, hFG, hG, hmax⟩ := exists_maximal_positive s F hF
  have hGtop : G.domain = ⊤ := by
    by_contra hne
    have hdense : ∀ y, ∃ x : G.domain, (x : E × ℝ) + y ∈ s := by
      rintro ⟨y, b⟩
      let z : F.domain :=
        ⟨(0, N y - b), by
          constructor
          · exact zero_mem f.domain
          · exact Submodule.mem_top⟩
      let x : G.domain := ⟨(z : E × ℝ), hFG.1 z.property⟩
      refine ⟨x, ?_⟩
      change N (0 + y) ≤ (N y - b) + b
      simpa using (le_rfl : N y ≤ N y)
    obtain ⟨H, hGH, hH⟩ := provided_step s G hG hdense hne
    exact (hmax H hGH) hH
  let inc : (E × ℝ) →ₗ[ℝ] G.domain :=
    { toFun := fun z =>
        ⟨z, by
          rw [hGtop]
          exact Submodule.mem_top⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl
      map_smul' := by
        intro c x
        apply Subtype.ext
        rfl }
  let L : (E × ℝ) →ₗ[ℝ] ℝ := G.toFun.comp inc
  have hLF (z : F.domain) : L (z : E × ℝ) = F z := by
    change
      G ⟨(z : E × ℝ), by
        rw [hGtop]
        exact Submodule.mem_top⟩ = F z
    exact (hFG.2 rfl).symm
  have hLone : L ((0 : E), (1 : ℝ)) = 1 := by
    let z : F.domain :=
      ⟨((0 : E), (1 : ℝ)), by
        constructor
        · exact zero_mem f.domain
        · exact Submodule.mem_top⟩
    simpa [F] using hLF z
  let emb : E →ₗ[ℝ] E × ℝ :=
    { toFun := fun x => (x, 0)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  let g : E →ₗ[ℝ] ℝ := -(L.comp emb)
  refine ⟨g, ?_, ?_⟩
  · intro x
    let z : F.domain :=
      ⟨((x : E), (0 : ℝ)), by
        constructor
        · exact x.property
        · exact Submodule.mem_top⟩
    have hz := hLF z
    change -L ((x : E), (0 : ℝ)) = f x
    simpa [F] using congrArg Neg.neg hz
  · intro x
    have hs : ((x, N x) : E × ℝ) ∈ s := by
      change N x ≤ N x
      exact le_rfl
    have hp : 0 ≤ L (x, N x) := by
      change
        0 ≤ G ⟨(x, N x), by
          rw [hGtop]
          exact Submodule.mem_top⟩
      exact hG
        ⟨(x, N x), by
          rw [hGtop]
          exact Submodule.mem_top⟩ hs
    have hpair :
        (x, N x) =
          ((x, (0 : ℝ)) + ((0 : E), N x)) := by
      ext <;> simp
    have hscalar :
        ((0 : E), N x) =
          N x • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    have hsplit : L (x, N x) = L (x, 0) + N x := by
      rw [hpair, L.map_add, hscalar, L.map_smul, hLone]
      simp
    change -L (x, 0) ≤ N x
    rw [hsplit] at hp
    linarith


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth3

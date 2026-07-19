import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.LinearAlgebra.LinearPMap

open Set LinearMap

namespace Depth4

open Submodule

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/- REQUIRED:
theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x
-/

structure HBExtension (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ) where
  domain : Submodule ℝ E
  toMap : domain →ₗ[ℝ] ℝ
  base_le : f.domain ≤ domain
  base_eq : ∀ x : f.domain, toMap ⟨x, base_le x.property⟩ = f x
  bound : ∀ x : domain, toMap x ≤ N x

instance hbExtensionLE (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ) :
    LE (HBExtension f N) :=
  ⟨fun a b =>
    ∃ h : a.domain ≤ b.domain,
      ∀ x : a.domain, b.toMap ⟨x, h x.property⟩ = a.toMap x⟩

instance hbExtensionPartialOrder (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ) :
    PartialOrder (HBExtension f N) where
  le_refl a := ⟨fun _ hx => hx, fun _ => rfl⟩
  le_trans a b c hab hbc := by
    rcases hab with ⟨hab, hab'⟩
    rcases hbc with ⟨hbc, hbc'⟩
    refine ⟨fun x hx => hbc (hab hx), ?_⟩
    intro x
    rw [hbc' ⟨x, hab x.property⟩]
    exact hab' x
  le_antisymm a b hab hba := by
    rcases hab with ⟨hab, hab'⟩
    rcases hba with ⟨hba, hba'⟩
    rcases a with ⟨ad, av, abl, abe, abd⟩
    rcases b with ⟨bd, bv, bbl, bbe, bbd⟩
    dsimp at hab hba hab' hba'
    have hd : ad = bd := le_antisymm hab hba
    cases hd
    have hv : av = bv := by
      ext x
      simpa using (hab' x).symm
    cases hv
    rfl

theorem tested_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x := by
  classical
  let initial : HBExtension f N :=
    { domain := f.domain
      toMap := f.toLinearMap
      base_le := fun _ hx => hx
      base_eq := fun _ => rfl
      bound := hf }
  obtain ⟨m, hm⟩ := zorn_le (α := HBExtension f N) (by
    intro c hc
    by_cases hcn : c.Nonempty
    · let D : Submodule ℝ E :=
        { carrier := {x | ∃ a ∈ c, x ∈ a.domain}
          zero_mem' := by
            rcases hcn with ⟨a, ha⟩
            exact ⟨a, ha, a.domain.zero_mem⟩
          add_mem' := by
            rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
            rcases hc.total ha hb with hab | hba
            · exact ⟨b, hb, b.domain.add_mem (hab.1 hxa) hyb⟩
            · exact ⟨a, ha, a.domain.add_mem hxa (hba.1 hyb)⟩
          smul_mem' := by
            rintro r x ⟨a, ha, hxa⟩
            exact ⟨a, ha, a.domain.smul_mem r hxa⟩ }
      let pick (x : D) : HBExtension f N := Classical.choose x.property
      have pick_mem (x : D) : pick x ∈ c :=
        (Classical.choose_spec x.property).1
      have pick_dom (x : D) : (x : E) ∈ (pick x).domain :=
        (Classical.choose_spec x.property).2
      have common_value {x : E} {a b : HBExtension f N}
          (ha : a ∈ c) (hb : b ∈ c)
          (hxa : x ∈ a.domain) (hxb : x ∈ b.domain) :
          a.toMap ⟨x, hxa⟩ = b.toMap ⟨x, hxb⟩ := by
        rcases hc.total ha hb with hab | hba
        · simpa using (hab.2 (⟨x, hxa⟩ : a.domain)).symm
        · simpa using hba.2 (⟨x, hxb⟩ : b.domain)
      let v (x : D) : ℝ := (pick x).toMap ⟨x, pick_dom x⟩
      have v_eq (x : D) (a : HBExtension f N) (ha : a ∈ c)
          (hxa : (x : E) ∈ a.domain) :
          v x = a.toMap ⟨x, hxa⟩ := by
        exact common_value (pick_mem x) ha (pick_dom x) hxa
      let L : D →ₗ[ℝ] ℝ :=
        { toFun := v
          map_add' := by
            intro x y
            rcases hc.total (pick_mem x) (pick_mem y) with hxy | hyx
            · have hx : (x : E) ∈ (pick y).domain := hxy.1 (pick_dom x)
              have hxy' : ((x + y : D) : E) ∈ (pick y).domain :=
                (pick y).domain.add_mem hx (pick_dom y)
              calc
                v (x + y) =
                    (pick y).toMap ⟨(x + y : D), hxy'⟩ :=
                  v_eq (x + y) (pick y) (pick_mem y) hxy'
                _ = (pick y).toMap ⟨x, hx⟩ +
                    (pick y).toMap ⟨y, pick_dom y⟩ := by
                      simpa using
                        (pick y).toMap.map_add
                          (⟨x, hx⟩ : (pick y).domain)
                          (⟨y, pick_dom y⟩ : (pick y).domain)
                _ = v x + v y := by
                  rw [v_eq x (pick y) (pick_mem y) hx,
                    v_eq y (pick y) (pick_mem y) (pick_dom y)]
          map_smul' := by
            intro r x
            have hrx : ((r • x : D) : E) ∈ (pick x).domain :=
              (pick x).domain.smul_mem r (pick_dom x)
            calc
              v (r • x) = (pick x).toMap ⟨r • x, hrx⟩ :=
                v_eq (r • x) (pick x) (pick_mem x) hrx
              _ = r • (pick x).toMap ⟨x, pick_dom x⟩ := by
                simpa using
                  (pick x).toMap.map_smul r
                    (⟨x, pick_dom x⟩ : (pick x).domain)
              _ = r • v x := by
                rw [v_eq x (pick x) (pick_mem x) (pick_dom x)] }
      let a₀ : HBExtension f N := Classical.choose hcn
      have ha₀ : a₀ ∈ c := Classical.choose_spec hcn
      let u : HBExtension f N :=
        { domain := D
          toMap := L
          base_le := by
            intro x hx
            exact ⟨a₀, ha₀, a₀.base_le hx⟩
          base_eq := by
            intro x
            have hx : (x : E) ∈ a₀.domain := a₀.base_le x.property
            calc
              L ⟨x, ⟨a₀, ha₀, hx⟩⟩ =
                  a₀.toMap ⟨x, hx⟩ :=
                v_eq ⟨x, ⟨a₀, ha₀, hx⟩⟩ a₀ ha₀ hx
              _ = f x := a₀.base_eq x
          bound := by
            intro x
            calc
              L x = (pick x).toMap ⟨x, pick_dom x⟩ :=
                v_eq x (pick x) (pick_mem x) (pick_dom x)
              _ ≤ N x := (pick x).bound ⟨x, pick_dom x⟩ }
      refine ⟨u, ?_⟩
      intro a ha
      refine ⟨?_, ?_⟩
      · intro x hx
        exact ⟨a, ha, hx⟩
      · intro x
        exact v_eq
          ⟨x, ⟨a, ha, x.property⟩⟩ a ha x.property
    · exact ⟨initial, by
        intro a ha
        exact (hcn ⟨a, ha⟩).elim⟩)
  have mtop : m.domain = ⊤ := by
    apply top_unique
    intro x _
    by_contra hxm
    let A : Set ℝ :=
      {r | ∃ y : m.domain, r = N ((y : E) + x) - m.toMap y}
    have hAne : A.Nonempty := by
      refine ⟨N x - m.toMap 0, ?_⟩
      exact ⟨0, by simp [A]⟩
    have hAbdd : BddBelow A := by
      refine ⟨-N (-x), ?_⟩
      rintro r ⟨y, rfl⟩
      have hmy := m.bound y
      have hn := N_add ((y : E) + x) (-x)
      have heq : ((y : E) + x) + -x = y := by
        module
      rw [heq] at hn
      linarith
    let c₀ : ℝ := sInf A
    have hc_upper (y : m.domain) :
        c₀ ≤ N ((y : E) + x) - m.toMap y := by
      exact csInf_le hAbdd ⟨y, rfl⟩
    have hc_lower (y : m.domain) :
        m.toMap y - N ((y : E) - x) ≤ c₀ := by
      apply le_csInf hAne
      rintro r ⟨z, rfl⟩
      have hmadd := m.bound (y + z)
      have hmap :
          m.toMap (y + z) = m.toMap y + m.toMap z := by
        exact m.toMap.map_add y z
      have hn := N_add ((y : E) - x) ((z : E) + x)
      have heq :
          ((y : E) - x) + ((z : E) + x) = (y + z : m.domain) := by
        module
      rw [heq] at hn
      rw [hmap] at hmadd
      linarith
    have general_bound (y : m.domain) (a : ℝ) :
        m.toMap y + a * c₀ ≤ N ((y : E) + a • x) := by
      rcases lt_trichotomy a 0 with ha | ha | ha
      · let b : ℝ := -a
        have hb : 0 < b := by
          dsimp [b]
          linarith
        let z : m.domain := b⁻¹ • y
        have hbne : b ≠ 0 := ne_of_gt hb
        have hby : b • z = y := by
          apply Subtype.ext
          simp [z, hbne]
        have hz := hc_lower z
        have hz' : m.toMap z - c₀ ≤ N ((z : E) - x) := by
          linarith
        have hvec :
            b • ((z : E) - x) = (y : E) + a • x := by
          dsimp [z, b]
          simp [hbne]
          module
        calc
          m.toMap y + a * c₀ =
              b * (m.toMap z - c₀) := by
                rw [← hby, m.toMap.map_smul]
                dsimp [b]
                simp
                ring
          _ ≤ b * N ((z : E) - x) :=
            mul_le_mul_of_nonneg_left hz' (le_of_lt hb)
          _ = N (b • ((z : E) - x)) := by
            rw [N_hom b hb]
          _ = N ((y : E) + a • x) := by rw [hvec]
      · subst a
        simpa using m.bound y
      · let z : m.domain := a⁻¹ • y
        have hane : a ≠ 0 := ne_of_gt ha
        have hay : a • z = y := by
          apply Subtype.ext
          simp [z, hane]
        have hz := hc_upper z
        have hz' : m.toMap z + c₀ ≤ N ((z : E) + x) := by
          linarith
        have hvec :
            a • ((z : E) + x) = (y : E) + a • x := by
          dsimp [z]
          simp [hane, smul_add]
        calc
          m.toMap y + a * c₀ =
              a * (m.toMap z + c₀) := by
                rw [← hay, m.toMap.map_smul]
                simp
                ring
          _ ≤ a * N ((z : E) + x) :=
            mul_le_mul_of_nonneg_left hz' (le_of_lt ha)
          _ = N (a • ((z : E) + x)) := by
            rw [N_hom a ha]
          _ = N ((y : E) + a • x) := by rw [hvec]
    let D : Submodule ℝ E :=
      { carrier :=
          {z | ∃ y : m.domain, ∃ a : ℝ, z = (y : E) + a • x}
        zero_mem' := by
          exact ⟨0, 0, by simp⟩
        add_mem' := by
          rintro z w ⟨y, a, rfl⟩ ⟨y', a', rfl⟩
          refine ⟨y + y', a + a', ?_⟩
          module
        smul_mem' := by
          rintro r z ⟨y, a, rfl⟩
          refine ⟨r • y, r * a, ?_⟩
          module }
    have coeff_unique {y y' : m.domain} {a a' : ℝ}
        (h : (y : E) + a • x = (y' : E) + a' • x) :
        a = a' := by
      by_contra haa
      have hd : a - a' ≠ 0 := sub_ne_zero.mpr haa
      have hs : (a - a') • x = (y' : E) - y := by
        module at h ⊢
      have hxmem : x ∈ m.domain := by
        have heq : x = (a - a')⁻¹ • ((y' : E) - y) := by
          rw [← hs]
          simp [hd]
        rw [heq]
        exact m.domain.smul_mem _ (m.domain.sub_mem y'.property y.property)
      exact hxm hxmem
    let py (z : D) : m.domain := Classical.choose z.property
    let pa (z : D) : ℝ := Classical.choose (Classical.choose_spec z.property)
    have pspec (z : D) :
        (z : E) = (py z : E) + pa z • x :=
      Classical.choose_spec (Classical.choose_spec z.property)
    let q (z : D) : ℝ := m.toMap (py z) + pa z * c₀
    have q_eq (z : D) (y : m.domain) (a : ℝ)
        (hz : (z : E) = (y : E) + a • x) :
        q z = m.toMap y + a * c₀ := by
      have hr :
          (py z : E) + pa z • x = (y : E) + a • x :=
        (pspec z).symm.trans hz
      have ha : pa z = a := coeff_unique hr
      have hy : py z = y := by
        apply Subtype.ext
        module at hr ⊢
      simp [q, ha, hy]
    let L : D →ₗ[ℝ] ℝ :=
      { toFun := q
        map_add' := by
          intro z w
          have hrep :
              ((z + w : D) : E) =
                ((py z + py w : m.domain) : E) +
                  (pa z + pa w) • x := by
            have hz := pspec z
            have hw := pspec w
            module at hz hw ⊢
          calc
            q (z + w) =
                m.toMap (py z + py w) + (pa z + pa w) * c₀ :=
              q_eq (z + w) (py z + py w) (pa z + pa w) hrep
            _ = q z + q w := by
              simp [q, m.toMap.map_add]
              ring
        map_smul' := by
          intro r z
          have hrep :
              ((r • z : D) : E) =
                ((r • py z : m.domain) : E) + (r * pa z) • x := by
            have hz := pspec z
            module at hz ⊢
          calc
            q (r • z) =
                m.toMap (r • py z) + (r * pa z) * c₀ :=
              q_eq (r • z) (r • py z) (r * pa z) hrep
            _ = r • q z := by
              simp [q, m.toMap.map_smul]
              ring }
    let u : HBExtension f N :=
      { domain := D
        toMap := L
        base_le := by
          intro z hz
          exact ⟨⟨z, m.base_le hz⟩, 0, by simp⟩
        base_eq := by
          intro z
          have hz :
              ((⟨z, ⟨⟨z, m.base_le z.property⟩, 0, by simp⟩⟩ : D) : E) =
                ((⟨z, m.base_le z.property⟩ : m.domain) : E) + 0 • x := by
            simp
          calc
            L ⟨z, ⟨⟨z, m.base_le z.property⟩, 0, by simp⟩⟩ =
                m.toMap ⟨z, m.base_le z.property⟩ :=
              by simpa using
                q_eq
                  (⟨z, ⟨⟨z, m.base_le z.property⟩, 0, by simp⟩⟩ : D)
                  (⟨z, m.base_le z.property⟩ : m.domain) 0 hz
            _ = f z := m.base_eq z
        bound := by
          intro z
          have hz := pspec z
          calc
            L z = m.toMap (py z) + pa z * c₀ := rfl
            _ ≤ N ((py z : E) + pa z • x) :=
              general_bound (py z) (pa z)
            _ = N z := by rw [← hz] }
    have hmu : m ≤ u := by
      refine ⟨?_, ?_⟩
      · intro y hy
        exact ⟨⟨y, hy⟩, 0, by simp⟩
      · intro y
        have hy :
            ((⟨y, ⟨⟨y, y.property⟩, 0, by simp⟩⟩ : D) : E) =
              (y : E) + 0 • x := by simp
        simpa using
          q_eq
            (⟨y, ⟨⟨y, y.property⟩, 0, by simp⟩⟩ : D)
            y 0 hy
    have hum : u = m := hm u hmu
    have hxD : x ∈ u.domain := by
      change x ∈ D
      exact ⟨0, 1, by simp⟩
    have : x ∈ m.domain := by
      rw [← hum]
      exact hxD
    exact hxm this
  let inclusion : E →ₗ[ℝ] m.domain :=
    { toFun := fun x => ⟨x, by rw [mtop]; exact Submodule.mem_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : E →ₗ[ℝ] ℝ := m.toMap.comp inclusion
  refine ⟨g, ?_, ?_⟩
  · intro x
    simpa [g, inclusion] using m.base_eq x
  · intro x
    simpa [g, inclusion] using m.bound (inclusion x)


theorem benchmark_check_hahn_banach (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  tested_hahn_banach f N N_hom N_add hf

#print axioms benchmark_check_hahn_banach

end Depth4

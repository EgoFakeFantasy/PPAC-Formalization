import PPAC.Migration.IterationSyntax

/-! 同一种子的零位置与同一并集递推步的输出相等，均为对象推导。 -/
namespace PPAC.Migration.IterationValues
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax InsertSyntax IterationSyntax

theorem edge_subst_input {m} {Γ : Context m} (f x y a : Fin m)
    (he : Derives Γ (.equal x y)) (hx : Derives Γ (edge f x a)) : Derives Γ (edge f y a) := by
  have hi : Derives Γ ((edge f.castSucc (Fin.last m) a.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  have h := Derives.eqSubst (edge f.castSucc (Fin.last m) a.castSucc) he hi
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem union_subst_source {m} {Γ : Context m} (u a b : Fin m)
    (he : Derives Γ (.equal a b)) (hu : Derives Γ (unionOf u a)) : Derives Γ (unionOf u b) := by
  have hi : Derives Γ ((unionOf u.castSucc (Fin.last m)).instantiate a) := by
    simpa only [Formula.instantiate, unionOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hu
  have h := Derives.eqSubst (unionOf u.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, unionOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem zero_values {m} {Γ : Context m} (f g d e z a x u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hx : Derives Γ (empty x))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hu : Derives Γ (edge f x u)) (hv : Derives Γ (edge g x v)) : Derives Γ (.equal u v) := by
  have hxz := OmegaUniversal.empty_unique x z he hx hz
  have hfa := edge_subst_input f z x a (eq_symm hxz) (.conjL (.conjR hf))
  have hga := edge_subst_input g z x a (eq_symm hxz) (.conjL (.conjR hg))
  exact eq_trans (GraphProperties.single_valued f d x u a he (.conjL hf) hu hfa)
    (eq_symm (GraphProperties.single_valued g e x v a he (.conjL hg) hv hga))

theorem step_values {m} {Γ : Context m} (f g j k a b u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (next f)) (hg : Derives Γ (next g)) (hs : Derives Γ (successor k j))
    (hab : Derives Γ (.equal a b)) (hfa : Derives Γ (edge f j a)) (hgb : Derives Γ (edge g j b))
    (hu : Derives Γ (edge f k u)) (hv : Derives Γ (edge g k v)) : Derives Γ (.equal u v) := by
  have hU := Derives.impE (Derives.impE (Derives.impE (next_at f j k a u hf) hs) hfa) hu
  have hV := Derives.impE (Derives.impE (Derives.impE (next_at g j k b v hg) hs) hgb) hv
  exact GraphDomainAlgebra.union_unique u v a he hU (union_subst_source v b a (eq_symm hab) hV)

theorem zero_agrees {m} {Γ : Context m} (f g d e z a x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hx : Derives Γ (empty x))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a)) : Derives Γ (agreesAt f g x) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hz' : Derives Δ (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz)
  have hx' : Derives Δ (empty x.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hx)
  have hf' : Derives Δ (track f.castSucc.castSucc d.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hg' : Derives Δ (track g.castSucc.castSucc e.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  apply Derives.impI
  apply Derives.impI
  exact zero_values f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc
    z.castSucc.castSucc a.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add he' _) _) (add (add hz' _) _) (add (add hx' _) _) (add (add hf' _) _) (add (add hg' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_agrees {m} {Γ : Context m} (f g j k a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (next f)) (hg : Derives Γ (next g)) (hs : Derives Γ (successor k j))
    (ha : Derives Γ (agreesAt f g j)) (hfa : Derives Γ (edge f j a)) (hgb : Derives Γ (edge g j b)) :
    Derives Γ (agreesAt f g k) := by
  have hab := Derives.impE (Derives.impE (agreesAt_at f g j a b ha) hfa) hgb
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hf' : Derives Δ (next f.castSucc.castSucc) := by
    simpa only [Formula.raise, next_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hg' : Derives Δ (next g.castSucc.castSucc) := by
    simpa only [Formula.raise, next_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hs' : Derives Δ (successor k.castSucc.castSucc j.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  have hfa' : Derives Δ (edge f.castSucc.castSucc j.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hfa)
  have hgb' : Derives Δ (edge g.castSucc.castSucc j.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hgb)
  have hab' := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hab)
  apply Derives.impI
  apply Derives.impI
  exact step_values f.castSucc.castSucc g.castSucc.castSucc j.castSucc.castSucc k.castSucc.castSucc
    a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add (add he' _) _)
    (add (add hf' _) _) (add (add hg' _) _) (add (add hs' _) _) (add (add hab' _) _)
    (add (add hfa' _) _) (add (add hgb' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.IterationValues

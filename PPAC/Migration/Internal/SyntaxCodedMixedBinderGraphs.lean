import PPAC.Migration.Internal.SyntaxCodedMixedBinderSyntax

/-! 数值码binder判断与任意实际输入/输出图的精确对应，全部等词传输使用原推导规则。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedBinderGraphs
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedBinderSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_bound_source {m} {Γ : Context m} (w r s a b c d A C k h V : Fin m)
    (he : Derives Γ (.equal r V)) (hl : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h)) :
    Derives Γ (SyntaxMixedImageBinderSyntax.lifted w V s a b c d A C k h) := by
  let P := SyntaxMixedImageBinderSyntax.lifted w.castSucc (Fin.last m) s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc h.castSucc
  have e0 : P.instantiate r = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageBinderSyntax.lifted w V s a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_free_source {m} {Γ : Context m} (w r s a b c d A C k h V : Fin m)
    (he : Derives Γ (.equal s V)) (hl : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h)) :
    Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r V a b c d A C k h) := by
  let P := SyntaxMixedImageBinderSyntax.lifted w.castSucc r.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc h.castSucc
  have e0 : P.instantiate s = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageBinderSyntax.lifted w r V a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_bound_target {m} {Γ : Context m} (w r s a b c d A C k h V : Fin m)
    (he : Derives Γ (.equal k V)) (hl : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h)) :
    Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C V h) := by
  let P := SyntaxMixedImageBinderSyntax.lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc (Fin.last m) h.castSucc
  have e0 : P.instantiate k = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C V h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_free_target {m} {Γ : Context m} (w r s a b c d A C k h V : Fin m)
    (he : Derives Γ (.equal h V)) (hl : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h)) :
    Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k V) := by
  let P := SyntaxMixedImageBinderSyntax.lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc k.castSucc (Fin.last m)
  have e0 : P.instantiate h = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k V := by
    simp only [P, Formula.instantiate, SyntaxMixedImageBinderSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H r s k h : Fin m)
    (hi : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S))
    (ho : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H))
    (hl : Derives Γ (lifted w R S a b c d A C K H)) : Derives Γ (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) := by
  let B := body w R S a b c d A C K H
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply SyntaxRenameBinders.eliminate_4 B _ hl
  have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
  have hi4 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.encodings_rename]) (SyntaxRenameBinders.under_4 hi B)
  have ho4 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.encodings_rename]) (SyntaxRenameBinders.under_4 ho B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ei := SyntaxMixedImageCodePairs.graphs_unique hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc (.conjL hB) hi4
  have eo := SyntaxMixedImageCodePairs.graphs_unique hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR hB)) ho4
  have hr := subst_bound_source w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) r.castSucc.castSucc.castSucc.castSucc (.conjL ei) (.conjL (.conjR hB))
  have hs := subst_free_source w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) s.castSucc.castSucc.castSucc.castSucc (.conjR ei) hr
  have hk := subst_bound_target w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) k.castSucc.castSucc.castSucc.castSucc (.conjL eo) hs
  have hh := subst_free_target w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) h.castSucc.castSucc.castSucc.castSucc (.conjR eo) hk
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageBinderSyntax.lifted_rename]) hh

theorem at_graphs_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d A C K H r s k h : Fin m)
    (hi : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S))
    (ho : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H)) :
    Derives Γ ((lifted w R S a b c d A C K H).iff (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graphs (ZFContext.add hZ _) w R S a b c d A C K H r s k h (add hi _) (add ho _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hb : Derives (Context.add (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h) Γ) (state w R S a b c d A C K H r s k h) :=
      .conjI (add hi _) (.conjI (.hyp (Or.inl rfl)) (add ho _))
    exact intro_lifted w R S a b c d A C K H r s k h hb

end PPAC.Migration.Internal.SyntaxCodedMixedBinderGraphs

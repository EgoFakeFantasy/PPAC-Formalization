import PPAC.Migration.Internal.IndexTermRenameTransportSyntax

/-! 任意内部纯项的实际索引图重命名传到原混合项替换和独立项程序。 -/
namespace PPAC.Migration.Internal.IndexTermRenameTransport
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermRenameTransportSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S))
    (hb : Derives Γ (SyntaxRenameTermSyntax.branch isBound w (SyntaxIndexMapSyntax.selectMap isBound r s) (SyntaxTermSyntax.limit isBound a b) n q)) :
    Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := by
  let B := SyntaxRenameTermSyntax.branchBody isBound w (SyntaxIndexMapSyntax.selectMap isBound r s) (SyntaxTermSyntax.limit isBound a b) n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameTermSyntax.eliminate_branch isBound w (SyntaxIndexMapSyntax.selectMap isBound r s) (SyntaxTermSyntax.limit isBound a b) n q _ hb
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 : Derives Δ (realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, realization_rename]) (SyntaxRenameBinders.under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := selected_mapped isBound w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc he2
  have hEdge : Derives Δ (GraphSyntax.edge (SyntaxIndexMapSyntax.selectMap isBound r.castSucc.castSucc s.castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1))) :=
    of_eq (by simp only [SyntaxIndexMapSyntax.selectMap_map]) (.conjL (.conjR hB))
  have hf := Derives.impE (.conjR (SyntaxVariableImageFields.at_index hZ2 isBound w.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap isBound r.castSucc.castSucc s.castSucc.castSucc) (SyntaxTermSyntax.limit isBound a.castSucc.castSucc b.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap isBound f.castSucc.castSucc g.castSucc.castSucc) (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc hm hEdge)) (.conjR (.conjR (.conjR hB)))
  have hField := SyntaxMixedImageCodeFields.edges w.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap isBound f.castSucc.castSucc g.castSucc.castSucc) (SyntaxTermSyntax.limit isBound a.castSucc.castSucc b.castSucc.castSucc) c.castSucc.castSucc d.castSucc.castSucc (SyntaxIndexMapSyntax.selectMap isBound R.castSucc.castSucc S.castSucc.castSucc) (Fin.last m).castSucc q.castSucc.castSucc
    (selected_encoded isBound w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc he2)
  have hNew := SyntaxCodedMixedTermFields.at_field hZ2 isBound w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc hw2
    (term_lists w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc he2) (.conjL (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, SyntaxCodedMixedTermSyntax.substituted_rename]) (Derives.impE (.conjR hNew) (.impE (.conjL hField) hf))

theorem term_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S))
    (hn : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := by
  apply Derives.disjE (.conjR hn)
  · exact branch_forward (ZFContext.add hZ _) true w r s f g a b c d R S n q (add hw _) (add he _) (.hyp (Or.inl rfl))
  · exact branch_forward (ZFContext.add hZ _) false w r s f g a b c d R S n q (add hw _) (add he _) (.hyp (Or.inl rfl))

theorem output_subst {m} {Γ : Context m} (w r s a b c d n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hq : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n v) := by
  let F := SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have h0 : F.instantiate q = SyntaxRenameTermSyntax.renamed w r s a b c d n q := by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : F.instantiate v = SyntaxRenameTermSyntax.renamed w r s a b c d n v := by simp only [F, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst F he (of_eq h0.symm hq))

theorem term_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)) : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q) := by
  have hx := SyntaxRenameTermExistence.for_term hZ w r s a b c d n hw (index_maps w r s f g a b c d R S he) (SyntaxCodedMixedTermTyping.source_type w R S a b c d n q hq)
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE hx
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have he1 : Derives Δ (realization w.castSucc r.castSucc s.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (realization_rename w r s f g a b c d R S Fin.castSucc) (under he Q)
  have hq1 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R S a b c d n q Fin.castSucc) (under hq Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hv := term_forward hZ1 w.castSucc r.castSucc s.castSucc f.castSucc g.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) hw1 he1 (.conjR hQ)
  have hEq := SyntaxCodedMixedTermUnique.unique hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 hv hq1
  have ho := output_subst w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hEq (.conjR hQ)
  exact of_eq (by simp only [Formula.raise, SyntaxRenameTermSyntax.renamed_rename]) ho

theorem term_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w r s a b c d n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact term_forward (ZFContext.add hZ _) w r s f g a b c d R S n q (add hw _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact term_reverse (ZFContext.add hZ _) w r s f g a b c d R S n q (add hw _) (add he _) (.hyp (Or.inl rfl))

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ ((TermTransformProgramSyntax.checked w R S a b c d n q).iff (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n q hw)
    (.conjI (.conjR (term_iff hZ w r s f g a b c d R S n q hw he)) (.conjL (term_iff hZ w r s f g a b c d R S n q hw he)))

end PPAC.Migration.Internal.IndexTermRenameTransport

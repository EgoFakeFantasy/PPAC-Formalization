import PPAC.Migration.Internal.IndexTermRenameTransport

/-! 两张原索引列表的实际转换对，以及指定旧解码图上的完整表对齐。 -/
namespace PPAC.Migration.Internal.IndexTermImageEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermImageCodeSyntax IndexTermRenameTransportSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J a b c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMapCodeSyntax.mapCode w a c I))
    (hj : Derives Γ (SyntaxMapCodeSyntax.mapCode w b d J)) : Derives Γ (existsEnvironment w I J a b c d) := by
  have hcd : Derives Γ (SyntaxTermSyntax.contexts w c d) := .conjI
    (.conjR (SyntaxMapCodeDecode.contexts w a c I hi)) (.conjR (SyntaxMapCodeDecode.contexts w b d J hj))
  have hr := IndexTermImageCodeExistence.exists_code hZ true w I a c d hw (.conjI hcd hi)
  let R := converted true w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE hr
  have hZ1 := ZFContext.under hZ R
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hcd1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc d.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w c d Fin.castSucc) (under hcd R)
  have hj1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w.castSucc b.castSucc d.castSucc J.castSucc) := of_eq (SyntaxMapCodeSyntax.mapCode_rename w b d J Fin.castSucc) (under hj R)
  have hs := IndexTermImageCodeExistence.exists_code hZ1 false w.castSucc J.castSucc b.castSucc c.castSucc d.castSucc hw1 (.conjI hcd1 hj1)
  let S := converted false w.castSucc.castSucc J.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE hs
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hR2 : Derives Ξ (converted true w.castSucc.castSucc I.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [R, Formula.raise, converted_rename]) (under hR S)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have ho := intro_environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (.conjI hR2 hS)
  exact of_eq (by simp only [Formula.raise, existsEnvironment_rename]) ho

theorem source_codes {m} {Γ : Context m} (w I J R S a b c d : Fin m)
    (he : Derives Γ (environment w I J R S a b c d)) :
    Derives Γ ((SyntaxMapCodeSyntax.mapCode w a c I).conj (SyntaxMapCodeSyntax.mapCode w b d J)) :=
  .conjI (.conjR (IndexTermImageCodeTyping.input_of_converted true w I R a c d (.conjL he)))
    (.conjR (IndexTermImageCodeTyping.input_of_converted false w J S b c d (.conjR he)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S U V a b c d : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (environment w I J R S a b c d))
    (hu : Derives Γ (environment w I J U V a b c d)) : Derives Γ ((Formula.equal R U).conj (.equal S V)) :=
  .conjI (IndexTermImageCodeUnique.unique hZ true w I R U a c d hw (.conjL he) (.conjL hu))
    (IndexTermImageCodeUnique.unique hZ false w J S V b c d hw (.conjR he) (.conjR hu))

theorem realization_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d r s : Fin m)
    (he : Derives Γ (environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J)) :
    Derives Γ (realizationExists w r s a b c d R S) := by
  have hf := IndexTermImageCodeTyping.at_graph hZ true w I R a c d r (.conjL he) hr
  let F := (SyntaxVariableImageSyntax.mapped true w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc R.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have hZ1 := ZFContext.under hZ F
  have he1 : Derives Δ (environment w.castSucc I.castSucc J.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (environment_rename w I J R S a b c d Fin.castSucc) (under he F)
  have hs1 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc s.castSucc b.castSucc d.castSucc J.castSucc) := of_eq (SyntaxMapCodeSyntax.encoded_rename w s b d J Fin.castSucc) (under hs F)
  have hg := IndexTermImageCodeTyping.at_graph hZ1 false w.castSucc J.castSucc S.castSucc b.castSucc c.castSucc d.castSucc s.castSucc (.conjR he1) hs1
  let G := (SyntaxVariableImageSyntax.mapped false w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Δ)
  apply Derives.exE hg
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hF2 : Derives Ξ ((SyntaxVariableImageSyntax.mapped true w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc)) :=
    of_eq (by simp only [F, Formula.raise, Formula.rename, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encoded_rename]) (under hF G)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hReal : Derives Ξ (realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
    .conjI (.conjL hF2) (.conjI (.conjL hG) (.conjI (.conjR hF2) (.conjR hG)))
  have ho := intro_realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc hReal
  exact of_eq (by simp only [Formula.raise, realizationExists_rename]) ho

theorem term_program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d r s n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J)) :
    Derives Γ ((TermTransformProgramSyntax.checked w R S a b c d n q).iff (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) := by
  let B := realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (realization_exists hZ w I J R S a b c d r s he hr hs)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ho := IndexTermRenameTransport.program_iff (SyntaxRenameBinders.zf_under_2 hZ B) w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 (.hyp (Or.inl rfl))
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, TermTransformProgramSyntax.checked_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

end PPAC.Migration.Internal.IndexTermImageEnvironment

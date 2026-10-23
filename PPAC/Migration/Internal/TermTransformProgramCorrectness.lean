import PPAC.Migration.Internal.TermTransformProgramVariable

/-! 独立受检项程序与原数值项替换在全部内部对象上等价；没有外部原生项或标准索引参数。 -/
namespace PPAC.Migration.Internal.TermTransformProgramCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax TermTransformProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_typed_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
    (ht : Derives Γ (SyntaxTermSyntax.branch isBound w (SyntaxTermSyntax.limit isBound a b) n)) :
    Derives Γ ((run termProgram w R S n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)) := by
  let B := SyntaxTermSyntax.branchWitness isBound w (SyntaxTermSyntax.limit isBound a b) n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch isBound w (SyntaxTermSyntax.limit isBound a b) n _ ht
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) (under hL B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hBN : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit isBound a.castSucc b.castSucc)).conj
      (SyntaxVariableSyntax.code isBound w.castSucc (Fin.last m) n.castSucc)) := of_eq (by simp only [B, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hB
  have hProgram := TermTransformProgramVariable.at_variable hZ1 isBound w.castSucc R.castSucc S.castSucc n.castSucc q.castSucc (Fin.last m) hw1 (.conjR hBN)
  have hOld := SyntaxCodedMixedTermFields.at_field hZ1 isBound w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hL1 (.conjR hBN)
  have hField := TermQuotationBinderFields.drop_member _ _ _ (.conjL hBN) (.conjI (.conjR hOld) (.conjL hOld))
  have ho := SyntaxTypeLocalTransfer.iff_trans hProgram hField
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, run_rename, SyntaxCodedMixedTermSyntax.substituted_rename]) ho

theorem at_typed_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((run termProgram w R S n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)) := by
  apply Derives.disjE (.conjR ht)
  · let B := SyntaxTermSyntax.branch true w a n
    exact at_typed_branch (ZFContext.add hZ B) true w R S a b c d n q (add hw B) (add hL B) (.hyp (Or.inl rfl))
  · let F := SyntaxTermSyntax.branch false w b n
    exact at_typed_branch (ZFContext.add hZ F) false w R S a b c d n q (add hw F) (add hL F) (.hyp (Or.inl rfl))

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((checked w R S a b c d n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := checked w R S a b c d n q
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have he := at_typed_term (ZFContext.add hZ P) w R S a b c d n q (add hw P) (.conjL (.conjL hP)) (.conjR (.conjL hP))
    exact .impE (.conjL he) (.conjR hP)
  · apply Derives.impI
    let P := SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q
    have hP : Derives (Context.add P Γ) P := .hyp (Or.inl rfl)
    have hi : Derives (Context.add P Γ) (inputGuard w R S a b c d n) := SyntaxCodedMixedTermTyping.input_of_substituted w R S a b c d n q hP
    have he := at_typed_term (ZFContext.add hZ P) w R S a b c d n q (add hw P) (.conjL hi) (.conjR hi)
    exact .conjI hi (.impE (.conjR he) hP)

end PPAC.Migration.Internal.TermTransformProgramCorrectness

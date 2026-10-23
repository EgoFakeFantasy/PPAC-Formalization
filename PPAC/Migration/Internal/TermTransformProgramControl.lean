import PPAC.Migration.Internal.TermTransformProgramSyntax

/-! 有序分派程序的实际命中/失败语义，分派索引见证在对象量词内取得、消去。 -/
namespace PPAC.Migration.Internal.TermTransformProgramControl
open Source SourceAlgebra SourceLogic TermTransformProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem recognized_of_code {m} {Γ : Context m} (isBound : Bool) (w i n : Fin m)
    (hc : Derives Γ (SyntaxVariableSyntax.code isBound w i n)) :
    Derives Γ (SyntaxVariableDecodeSyntax.recognized isBound w n) := by
  apply Derives.exI i
  exact of_eq (by simp only [Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc

theorem intro_arm {m} {Γ : Context m} (isBound : Bool) (action : Action) (w R S n q i : Fin m)
    (hc : Derives Γ (SyntaxVariableSyntax.code isBound w i n)) (ha : Derives Γ (actionValue action w R S n i q)) :
    Derives Γ (arm isBound action w R S n q) := by
  apply Derives.exI i
  exact of_eq (by simp only [armBody, Formula.instantiate, Formula.rename, SyntaxVariableSyntax.code_rename,
    actionValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hc ha)

theorem recognized_of_arm {m} {Γ : Context m} (isBound : Bool) (action : Action) (w R S n q : Fin m)
    (ha : Derives Γ (arm isBound action w R S n q)) : Derives Γ (SyntaxVariableDecodeSyntax.recognized isBound w n) := by
  let B := armBody isBound action w R S n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := recognized_of_code isBound w.castSucc (Fin.last m) n.castSucc (.conjL hB)
  exact of_eq (SyntaxVariableDecodeSyntax.recognized_rename isBound w n Fin.castSucc).symm ho

theorem hit {m} {Γ : Context m} (isBound : Bool) (action : Action) (otherwise : Program) (w R S n q : Fin m)
    (hm : Derives Γ (SyntaxVariableDecodeSyntax.recognized isBound w n)) :
    Derives Γ ((run (.dispatchVariable isBound action otherwise) w R S n q).iff (arm isBound action w R S n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let D := run (.dispatchVariable isBound action otherwise) w R S n q
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add D Γ) D)
    · exact .hyp (Or.inl rfl)
    · let B := (SyntaxVariableDecodeSyntax.recognized isBound w n).neg.conj (run otherwise w R S n q)
      have hB : Derives (Context.add B (Context.add D Γ)) B := .hyp (Or.inl rfl)
      exact .botE (.impE (.conjL hB) (add (add hm D) B))
  · apply Derives.impI
    exact .disjL (.hyp (Or.inl rfl))

theorem miss {m} {Γ : Context m} (isBound : Bool) (action : Action) (otherwise : Program) (w R S n q : Fin m)
    (hm : Derives Γ (SyntaxVariableDecodeSyntax.recognized isBound w n).neg) :
    Derives Γ ((run (.dispatchVariable isBound action otherwise) w R S n q).iff (run otherwise w R S n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let D := run (.dispatchVariable isBound action otherwise) w R S n q
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add D Γ) D)
    · let B := arm isBound action w R S n q
      have hB : Derives (Context.add B (Context.add D Γ)) B := .hyp (Or.inl rfl)
      exact .botE (.impE (add (add hm D) B) (recognized_of_arm isBound action w R S n q hB))
    · exact .conjR (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .disjR (.conjI (add hm _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.TermTransformProgramControl

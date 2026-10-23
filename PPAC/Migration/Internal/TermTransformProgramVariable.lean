import PPAC.Migration.Internal.TermTransformProgramControl

/-! 独立程序对所有内部变量码的完整查表语义；索引只由原对象解码唯一性对齐。 -/
namespace PPAC.Migration.Internal.TermTransformProgramVariable
open Source SourceAlgebra SourceLogic OmegaSyntax TermTransformProgramSyntax TermTransformProgramControl
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem not_opposite_match {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code isBound w i n)) :
    Derives Γ (SyntaxVariableDecodeSyntax.recognized (!isBound) w n).neg := by
  apply Derives.impI
  let M := SyntaxVariableDecodeSyntax.recognized (!isBound) w n
  let B := SyntaxVariableSyntax.code (!isBound) w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.add M Γ))
  apply Derives.exE (p := B) (.hyp (Or.inl rfl) : Derives (Context.add M Γ) M)
  have hZ1 := ZFContext.under (ZFContext.add hZ M) B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw M) B)
  have hc1 : Derives Δ (SyntaxVariableSyntax.code isBound w.castSucc i.castSucc n.castSucc) := of_eq (SyntaxVariableSyntax.code_rename isBound w i n Fin.castSucc) (under (add hc M) B)
  exact SyntaxVariableDecode.opposite_disjoint hZ1 isBound w.castSucc i.castSucc (Fin.last m) n.castSucc hw1 hc1 (.hyp (Or.inl rfl))

theorem read_arm_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound imageBound : Bool) (w R S n q i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code isBound w i n)) :
    Derives Γ ((arm isBound (.readImage imageBound) w R S n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap imageBound R S) i q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let M := arm isBound (.readImage imageBound) w R S n q
    let B := armBody isBound (.readImage imageBound) w R S n q
    let Δ := Context.add B (Context.image Formula.raise (Context.add M Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl) : Derives (Context.add M Γ) M)
    have hZ1 := ZFContext.under (ZFContext.add hZ M) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw M) B)
    have hc1 : Derives Δ (SyntaxVariableSyntax.code isBound w.castSucc i.castSucc n.castSucc) := of_eq (SyntaxVariableSyntax.code_rename isBound w i n Fin.castSucc) (under (add hc M) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have heq := SyntaxVariableDecode.index_eq hZ1 isBound w.castSucc (Fin.last m) i.castSucc n.castSucc hw1 (.conjL hB) hc1
    have ho := StructuralListFieldSyntax.index_subst w.castSucc (SyntaxIndexMapSyntax.selectMap imageBound R.castSucc S.castSucc) (Fin.last m) i.castSucc q.castSucc heq (.conjR hB)
    exact of_eq (by simp only [Formula.raise, StructuralListFieldSyntax.field_rename, SyntaxIndexMapSyntax.selectMap_map]) ho
  · apply Derives.impI
    exact intro_arm isBound (.readImage imageBound) w R S n q i (add hc _) (.hyp (Or.inl rfl))

theorem at_variable {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w R S n q i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxVariableSyntax.code isBound w i n)) :
    Derives Γ ((run termProgram w R S n q).iff
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap isBound R S) i q)) := by
  have hr := recognized_of_code isBound w i n hc
  cases isBound
  · have hmiss := miss true (.readImage true) (.dispatchVariable false (.readImage false) .copySource) w R S n q (not_opposite_match hZ false w i n hw hc)
    have hhit := hit false (.readImage false) .copySource w R S n q hr
    have hread := read_arm_iff hZ false false w R S n q i hw hc
    exact SyntaxTypeLocalTransfer.iff_trans hmiss (SyntaxTypeLocalTransfer.iff_trans hhit hread)
  · exact SyntaxTypeLocalTransfer.iff_trans (hit true (.readImage true) (.dispatchVariable false (.readImage false) .copySource) w R S n q hr) (read_arm_iff hZ true true w R S n q i hw hc)

theorem copy_default_iff {m} {Γ : Context m} (w R S n q : Fin m)
    (hb : Derives Γ (SyntaxVariableDecodeSyntax.recognized true w n).neg)
    (hf : Derives Γ (SyntaxVariableDecodeSyntax.recognized false w n).neg) :
    Derives Γ ((run termProgram w R S n q).iff (.equal q n)) :=
  SyntaxTypeLocalTransfer.iff_trans (miss true (.readImage true) (.dispatchVariable false (.readImage false) .copySource) w R S n q hb)
    (miss false (.readImage false) .copySource w R S n q hf)

end PPAC.Migration.Internal.TermTransformProgramVariable

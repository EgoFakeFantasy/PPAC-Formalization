import PPAC.Migration.Internal.IndexTermImageCodeExistence

/-! 同一实际索引码的所有转换结果唯一；不存在外部选择的表值。 -/
namespace PPAC.Migration.Internal.IndexTermImageCodeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermImageCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I T U a c d : Fin m)
    (hw : Derives Γ (omega w)) (hT : Derives Γ (converted isBound w I T a c d))
    (hU : Derives Γ (converted isBound w I U a c d)) : Derives Γ (.equal T U) := by
  let B := body isBound w I T a c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hT
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hU2 : Derives Δ (converted isBound w.castSucc.castSucc I.castSucc.castSucc U.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, converted_rename]) (SyntaxRenameBinders.under_2 hU B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hf := IndexTermImageCodeTyping.at_graph hZ2 isBound w.castSucc.castSucc I.castSucc.castSucc U.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc hU2 (.conjL hB)
  let G := (SyntaxVariableImageSyntax.mapped isBound w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+2))).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Δ)
  apply Derives.exE hf
  have hZ3 := ZFContext.under hZ2 G
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 G)
  have hB3 : Derives Ξ (data isBound w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [B, body, Formula.raise, data_rename]) (under hB G)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have he := SyntaxVariableImageGraph.unique hZ3 isBound w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc (.conjL hG) (.conjL (.conjR hB3))
  have hEnc := SyntaxMixedImageCodeUnique.subst_graph w.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc he (.conjR hG)
  exact SyntaxMixedImageCodeUnique.unique_code hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc hw3 (.conjR (.conjR hB3)) hEnc

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I T a c d : Fin m)
    (hw : Derives Γ (omega w)) (hT : Derives Γ (converted isBound w I T a c d)) : Derives Γ (uniqueCode isBound w I T a c d) := by
  apply Derives.allI
  apply Derives.impI
  let U := converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc
  let Δ := Context.add U (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hT1 : Derives Δ (converted isBound w.castSucc I.castSucc T.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (converted_rename isBound w I T a c d Fin.castSucc) (under hT U)
  exact unique (ZFContext.under hZ U) isBound w.castSucc I.castSucc (Fin.last m) T.castSucc a.castSucc c.castSucc d.castSucc hw1 (.hyp (Or.inl rfl)) hT1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I a c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input isBound w I a c d)) : Derives Γ (fiber isBound w I a c d) := by
  have he := IndexTermImageCodeExistence.exists_code hZ isBound w I a c d hw hi
  let T := converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := intro_fiber isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc hT (unique_output (ZFContext.under hZ T) isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc hw1 hT)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem input_of_exists {m} {Γ : Context m} (isBound : Bool) (w I a c d : Fin m)
    (he : Derives Γ (existsCode isBound w I a c d)) : Derives Γ (input isBound w I a c d) := by
  let T := converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hi := IndexTermImageCodeTyping.input_of_converted isBound w.castSucc I.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc (Derives.hyp (Or.inl rfl) : Derives Δ T)
  exact of_eq (input_rename isBound w I a c d Fin.castSucc).symm hi

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I a c d : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsCode isBound w I a c d).iff (input isBound w I a c d)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists isBound w I a c d (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact IndexTermImageCodeExistence.exists_code (ZFContext.add hZ _) isBound w I a c d (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.IndexTermImageCodeUnique

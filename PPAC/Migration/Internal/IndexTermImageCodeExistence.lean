import PPAC.Migration.Internal.IndexTermImageCodeTyping

/-! 合法原索引列表实际取得变量项列表码；图和码见证均在对象层消去。 -/
namespace PPAC.Migration.Internal.IndexTermImageCodeExistence
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermImageCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I a c d : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input isBound w I a c d)) : Derives Γ (existsCode isBound w I a c d) := by
  let E := SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc (SyntaxTermSyntax.limit isBound c.castSucc d.castSucc) I.castSucc
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  have he : Derives Γ (.ex E) := of_eq (by simp only [SyntaxMapCodeSyntax.mapCode, E, SyntaxTermSyntax.limit_map]) (.conjR hi)
  apply Derives.exE (p := E) he
  have hZ1 := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hi1 : Derives Ξ (input isBound w.castSucc I.castSucc a.castSucc c.castSucc d.castSucc) := of_eq (input_rename isBound w I a c d Fin.castSucc) (under hi E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hf := SyntaxVariableImageGraph.exists_map hZ1 isBound w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc hw1 (.conjI (.conjL hi1) (.conjR hE))
  let F := SyntaxVariableImageSyntax.mapped isBound w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  apply Derives.exE hf
  have hZ2 := ZFContext.under hZ1 F
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 F)
  have hE2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (SyntaxTermSyntax.limit isBound c.castSucc.castSucc d.castSucc.castSucc) I.castSucc.castSucc) :=
    of_eq (by simp only [E, Formula.raise, SyntaxMapCodeSyntax.encoded_rename, SyntaxTermSyntax.limit_map]) (under hE F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have ht := SyntaxMixedImageCodeExistence.exists_code hZ2 w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc hw2 (.conjL (.conjR hF))
  let T := SyntaxMixedImageCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ω := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE ht
  have hE3 : Derives Ω (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc (SyntaxTermSyntax.limit isBound c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) I.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename, SyntaxTermSyntax.limit_map]) (under hE2 T)
  have hF3 : Derives Ω (SyntaxVariableImageSyntax.mapped isBound w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [F, Formula.raise, SyntaxVariableImageSyntax.mapped_rename]) (under hF T)
  have hT : Derives Ω T := .hyp (Or.inl rfl)
  have hc := intro_converted isBound w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (.conjI hE3 (.conjI hF3 hT))
  have ho := intro_exists isBound w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc (Fin.last (m+2)) a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc hc
  exact of_eq (by simp only [Formula.raise, existsCode_rename]) ho

end PPAC.Migration.Internal.IndexTermImageCodeExistence

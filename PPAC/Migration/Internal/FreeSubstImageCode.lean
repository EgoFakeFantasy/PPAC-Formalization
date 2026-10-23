import PPAC.Migration.Internal.FreeSubstImageGraph

/-! 原替换参数L不变：索引解码码J转换所得自由变量项像列表恰是原L。 -/
namespace PPAC.Migration.Internal.FreeSubstImageCode
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem same_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L J : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w))
    (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a d L J)) :
    Derives Γ (IndexTermImageCodeSyntax.converted false w J L a c d) := by
  let B := SyntaxFreeSubstSyntax.codeBody w a d L J
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxFreeSubstSyntax.eliminate_code_conversion w a d L J _ hl
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hc2 : Derives Δ (.mem c.castSucc.castSucc w.castSucc.castSucc) := SyntaxRenameBinders.under_2 hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := FreeSubstImageGraph.mapped hZ2 w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc hw2 hc2 (.conjL (.conjR hB))
  have hf := FreeSubstImageGraph.image_map w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc hc2 (.conjL (.conjL (.conjR hB)))
  have ho := IndexTermImageCodeSyntax.intro_converted false w.castSucc.castSucc J.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (.conjI (.conjR (.conjR hB)) (.conjI hm (.conjI hf (.conjL hB))))
  exact of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) ho

theorem converted_unique_same_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c d L J T : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w))
    (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a d L J))
    (ht : Derives Γ (IndexTermImageCodeSyntax.converted false w J T a c d)) : Derives Γ (.equal T L) :=
  IndexTermImageCodeUnique.unique hZ false w J T L a c d hw ht (same_code hZ w a c d L J hw hc hl)

theorem identity_image_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b c I : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b I)) :
    Derives Γ (IndexTermImageCodeSyntax.existsCode true w I b b c) := by
  have hm := SyntaxIdentityCode.map_code w b I hi
  have hb := Derives.conjL (SyntaxMapCodeDecode.contexts w b b I hm)
  exact IndexTermImageCodeExistence.exists_code hZ true w I b b c hw (.conjI (.conjI hb hc) hm)

end PPAC.Migration.Internal.FreeSubstImageCode

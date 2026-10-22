import PPAC.Migration.Internal.SyntaxMixedImageLiftSyntax

/-! 原Replacement实际取得两张完整混合binder表；同时变换两类项像，再扩展源bound头槽。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageLiftExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedImageLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d A C n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxTermImageSyntax.maps w r s a b c d))
    (hm : Derives Γ (SyntaxIndexMapSyntax.maps w R S c d C d))
    (hn : Derives Γ (SyntaxTermSyntax.term w C d n)) (hA : Derives Γ (successor A a)) :
    Derives Γ (existsPair w R S r s a b c d A C n) := by
  let B := SyntaxTermImagePushBoth.both w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he : Derives Γ (.ex (.ex B)) := SyntaxTermImagePushBoth.exists_both hZ w R S c d C d r s a b hw hm hi
  apply SyntaxRenameBinders.eliminate_2 B _ he
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hn2 : Derives Ξ (SyntaxTermSyntax.term w.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 hn B)
  have hA2 : Derives Ξ (successor A.castSucc.castSucc a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hA B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have ht := SyntaxTermImagePushBoth.target_maps w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hB
  let K := SyntaxTermImagePrefixSyntax.prefixed w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add K (Context.image Formula.raise Ξ)
  apply Derives.exE (p := K) (SyntaxTermImagePrefixGraph.exists_prefix hZ2 w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc A.castSucc.castSucc hw2 (.conjL ht) hn2 hA2)
  have hb3 : Derives Δ (SyntaxTermImagePushBoth.both w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [B, Formula.raise, SyntaxTermImagePushBoth.both_rename]) (under hB K)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hl := intro_lifted w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc hb3 hK
  have ho := intro_pair w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hl
  exact of_eq (by simp only [Formula.raise, existsPair_rename]) ho

end PPAC.Migration.Internal.SyntaxMixedImageLiftExistence

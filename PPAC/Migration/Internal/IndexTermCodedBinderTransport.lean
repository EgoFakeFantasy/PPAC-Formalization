import PPAC.Migration.Internal.IndexVariableBinderTransport

/-! 从实际输入/输出图恢复原码转换，并在同一原量词提升上保留完整双表对应。 -/
namespace PPAC.Migration.Internal.IndexTermCodedBinderTransport
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermImageCodeSyntax IndexTermRenameTransportSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_realization {m} {Γ : Context m} (w I J R S a b c d r s f g : Fin m)
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J))
    (he : Derives Γ (realization w r s f g a b c d R S)) : Derives Γ (environment w I J R S a b c d) :=
  .conjI (intro_converted true w I R a c d r f (.conjI hr (.conjI (.conjL he) (.conjL (.conjR (.conjR he))))))
    (intro_converted false w J S b c d s g (.conjI hs (.conjI (.conjL (.conjR he)) (.conjR (.conjR (.conjR he))))))

theorem realization_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S A C l k h K H : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C l))
    (ho : Derives Γ (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (realization w l s k h A b C d K H) := by
  have hBinder := SyntaxCodedMixedBinderGraphs.at_graphs hZ w R S a b c d A C K H f g k h (.conjR (.conjR he)) ho hn
  have hMaps := IndexVariableBinderTransport.mapped_after_binder hZ w r s f g a b c d A C l k h hw (.conjL he) (.conjL (.conjR he)) hl hBinder
  exact .conjI (.conjL hMaps) (.conjI (.conjR hMaps) ho)

theorem at_maps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d A C L K H r s l : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J))
    (hl : Derives Γ (SyntaxIndexLiftSyntax.lifted w r a c A C l))
    (hL : Derives Γ (SyntaxMapCodeSyntax.encoded w l A C L))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (environment w L J K H A b C d) := by
  let B := realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (IndexTermImageEnvironment.realization_exists hZ w I J R S a b c d r s he hr hs)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hs2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc s.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc J.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hs B)
  have hl2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc l.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl B)
  have hL2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc l.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hL B)
  have hn2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hn B)
  have hx := SyntaxMixedImageCodePairs.exists_graphs hZ2 w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc hw2
    (SyntaxCodedMixedBinderTyping.output_lists w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc hn2)
  let E := SyntaxMixedImageCodePairs.graphBody w.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc C.castSucc.castSucc d.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc
  let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Δ))
  apply SyntaxRenameBinders.eliminate_2 E _ hx
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 E
  have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 E)
  have hs4 : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hs2 E)
  have hl4 : Derives Ξ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hl2 E)
  have hL4 : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (SyntaxRenameBinders.under_2 hL2 E)
  have hn4 : Derives Ξ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hn2 E)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hB4 : Derives Ξ (realization w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [B, Formula.raise, realization_rename]) (SyntaxRenameBinders.under_2 hB E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hReal := realization_lift hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc hw4 hB4 hl4 hE hn4
  have ho := from_realization w.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hL4 hs4 hReal
  exact of_eq (by simp only [Formula.raise, environment_rename]) ho

theorem coded_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d A C L K H : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (environment w I J R S a b c d))
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c I A C L))
    (hn : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (environment w L J K H A b C d) := by
  let B := SyntaxMapLiftSyntax.body w a c I A C L
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hl
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have he2 : Derives Δ (environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, environment_rename]) (SyntaxRenameBinders.under_2 he B)
  have hn2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_2 hn B)
  have hCodes := IndexTermImageEnvironment.source_codes w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc he2
  let F := SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last (m+2)) b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc
  let Ξ := Context.add F (Context.image Formula.raise Δ)
  apply Derives.exE (.conjR hCodes)
  have hZ3 := ZFContext.under hZ2 F
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 F)
  have he3 : Derives Ξ (environment w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := of_eq (environment_rename w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc Fin.castSucc) (under he2 F)
  have hn3 : Derives Ξ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc Fin.castSucc) (under hn2 F)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr3 : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (under (.conjL hB) F)
  have hL3 : Derives Ξ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename]) (under (.conjR (.conjR hB)) F)
  have hLift3 : Derives Ξ (SyntaxIndexLiftSyntax.lifted w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [Formula.raise, SyntaxIndexLiftSyntax.lifted_rename]) (under (.conjL (.conjR hB)) F)
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have ho := at_maps hZ3 w.castSucc.castSucc.castSucc I.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hw3 he3 hr3 hF hLift3 hL3 hn3
  exact of_eq (by simp only [Formula.raise, environment_rename]) ho

end PPAC.Migration.Internal.IndexTermCodedBinderTransport

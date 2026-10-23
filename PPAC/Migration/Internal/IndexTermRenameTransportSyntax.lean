import PPAC.Migration.Internal.IndexTermImageCodeUnique

/-! 两个真实索引图与其变量项像图及原列表码之间的完整对象对应。 -/
namespace PPAC.Migration.Internal.IndexTermRenameTransportSyntax
open Source SourceAlgebra SourceLogic

def realization {m} (w r s f g a b c d R S : Fin m) : Formula m :=
  (SyntaxVariableImageSyntax.mapped true w r a c d f).conj
    ((SyntaxVariableImageSyntax.mapped false w s b c d g).conj (SyntaxMixedImageCodeSyntax.encodings w f g a b c d R S))

theorem realization_rename {m k} (w r s f g a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (realization w r s f g a b c d R S).rename ρ = realization (ρ w) (ρ r) (ρ s) (ρ f) (ρ g) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [realization, Formula.rename, SyntaxVariableImageSyntax.mapped_rename, SyntaxMixedImageCodeSyntax.encodings_rename]

theorem index_maps {m} {Γ : Context m} (w r s f g a b c d R S : Fin m)
    (he : Derives Γ (realization w r s f g a b c d R S)) : Derives Γ (SyntaxIndexMapSyntax.maps w r s a b c d) :=
  .conjI (.conjR (.conjL (.conjL he))) (.conjR (.conjL (.conjL (.conjR he))))

theorem term_lists {m} {Γ : Context m} (w r s f g a b c d R S : Fin m)
    (he : Derives Γ (realization w r s f g a b c d R S)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) :=
  SyntaxMixedImageCodePairs.term_lists w f g a b c d R S (.conjR (.conjR he))

theorem selected_mapped {m} {Γ : Context m} (isBound : Bool) (w r s f g a b c d R S : Fin m)
    (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ (SyntaxVariableImageSyntax.mapped isBound w (SyntaxIndexMapSyntax.selectMap isBound r s) (SyntaxTermSyntax.limit isBound a b) c d (SyntaxIndexMapSyntax.selectMap isBound f g)) := by
  cases isBound
  · exact .conjL (.conjR he)
  · exact .conjL he

theorem selected_encoded {m} {Γ : Context m} (isBound : Bool) (w r s f g a b c d R S : Fin m)
    (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.encoded w (SyntaxIndexMapSyntax.selectMap isBound f g) (SyntaxTermSyntax.limit isBound a b) c d (SyntaxIndexMapSyntax.selectMap isBound R S)) :=
  SyntaxCodedMixedTermFields.selected_encoded isBound w f g a b c d R S (.conjR (.conjR he))

def realizationExists {m} (w r s a b c d R S : Fin m) : Formula m := .ex (.ex
  (realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc))

theorem realizationExists_rename {m k} (w r s a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (realizationExists w r s a b c d R S).rename ρ = realizationExists (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [realizationExists, Formula.rename, realization_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_realization {m} {Γ : Context m} (w r s f g a b c d R S : Fin m)
    (he : Derives Γ (realization w r s f g a b c d R S)) : Derives Γ (realizationExists w r s a b c d R S) := by
  apply Derives.exI f
  apply Derives.exI g
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, realization_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

end PPAC.Migration.Internal.IndexTermRenameTransportSyntax

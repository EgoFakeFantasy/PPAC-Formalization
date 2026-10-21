import PPAC.Migration.GraphFamilyExistence

/-! 原空集合谓词下的图族条件，明确覆盖空族而不假设非空。 -/
namespace PPAC.Migration.GraphFamilyEmpty
open Source SourceAlgebra SourceLogic GraphFamilySyntax

theorem empty_core {m} (f : Fin m) : Source.SetLanguage.empty f =
    .all ((Formula.mem (Fin.last m) f.castSucc).neg) := rfl

theorem empty_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (Source.SetLanguage.empty f).rename r = Source.SetLanguage.empty (r f) := by
  simp only [empty_core, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem empty_at {m} {Γ : Context m} (f x : Fin m) (he : Derives Γ (Source.SetLanguage.empty f)) :
    Derives Γ (Formula.mem x f).neg := by
  rw [empty_core] at he
  have hi := Derives.allE x he
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem graphs_of_empty {m} {Γ : Context m} (f : Fin m) (he : Derives Γ (Source.SetLanguage.empty f)) :
    Derives Γ (graphs f) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.empty f.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc he
  apply Derives.impI
  exact .botE (.impE (add (empty_at f.castSucc (Fin.last m) he') _) (.hyp (Or.inl rfl)))

theorem compatible_of_empty {m} {Γ : Context m} (f : Fin m) (he : Derives Γ (Source.SetLanguage.empty f)) :
    Derives Γ (compatible f) := by
  apply Derives.allI
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (Source.SetLanguage.empty f.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  apply Derives.impI
  apply Derives.impI
  exact .botE (.impE (add (add (empty_at f.castSucc.castSucc (Fin.last m).castSucc he') _) _)
    (.hyp (Or.inr (Or.inl rfl))))
end PPAC.Migration.GraphFamilyEmpty

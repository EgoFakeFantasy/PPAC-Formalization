import PPAC.Migration.Internal.OriginalMemberExistingAtom

/-! 原kind1项运行与既有受检独立项程序的全内部比较公式及守卫对齐。 -/
namespace PPAC.Migration.Internal.AtomicTermAgreementSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def agreement {m} (w mode depth parameter R S a b c d : Fin m) : Formula m := .all (.all
  ((SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).imp
    ((OriginalTransformRowSyntax.run 1 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (TermTransformProgramSyntax.checked w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem agreement_rename {m j} (w mode depth parameter R S a b c d : Fin m) (ρ : Fin m → Fin j) :
    (agreement w mode depth parameter R S a b c d).rename ρ = agreement (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [agreement, Formula.rename, Formula.iff, SyntaxTermSyntax.term_rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.checked_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem agreement_at {m} {Γ : Context m} (w mode depth parameter R S a b c d x y : Fin m)
    (ha : Derives Γ (agreement w mode depth parameter R S a b c d))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b x)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth parameter x y).iff (TermTransformProgramSyntax.checked w R S a b c d x y)) := by
  have hh := Derives.allE y (Derives.allE x ha)
  have he : Derives Γ ((SyntaxTermSyntax.term w a b x).imp ((OriginalTransformRowSyntax.run 1 w mode depth parameter x y).iff (TermTransformProgramSyntax.checked w R S a b c d x y))) := by
    simpa only [agreement, Formula.instantiate, Formula.rename, Formula.iff, SyntaxTermSyntax.term_rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.checked_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hh
  exact .impE he ht

theorem checked_iff_run {m} {Γ : Context m} (w R S a b c d n q : Fin m)
    (hMaps : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((TermTransformProgramSyntax.checked w R S a b c d n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) :=
  .conjI (.impI (.conjR (.hyp (Or.inl rfl)))) (.impI (.conjI (.conjI (add hMaps _) (add ht _)) (.hyp (Or.inl rfl))))

theorem checked_input_subst {m} {Γ : Context m} (w R S a b c d x X y : Fin m)
    (he : Derives Γ (.equal x X)) (hp : Derives Γ (TermTransformProgramSyntax.checked w R S a b c d x y)) :
    Derives Γ (TermTransformProgramSyntax.checked w R S a b c d X y) := by
  let P := TermTransformProgramSyntax.checked w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) y.castSucc
  have h0 : P.instantiate x = TermTransformProgramSyntax.checked w R S a b c d x y := by simp only [P, Formula.instantiate, TermTransformProgramSyntax.checked_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate X = TermTransformProgramSyntax.checked w R S a b c d X y := by simp only [P, Formula.instantiate, TermTransformProgramSyntax.checked_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

end PPAC.Migration.Internal.AtomicTermAgreementSyntax

import PPAC.Migration.Internal.ProofTreeInduction

/-! 任意显式对象公式的原六分支递归方程；对全部对象码量化而不遗漏ω外值。 -/
namespace PPAC.Migration.Internal.ProofTreeEquationSyntax
open Source SourceAlgebra SourceLogic ProofTreeInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def equation {m} (test : Formula 1) (P : Formula 2) (w : Fin m) : Formula m := .all
  ((property P w.castSucc (Fin.last m)).iff (normalized test P w.castSucc (Fin.last m)))

def reverseCorrect {m} (test : Formula 1) (P : Formula 2) (w code : Fin m) : Formula m :=
  (property P w code).imp (ProofTreeEntrySyntax.node test w code)

def reverseIH {m} (test : Formula 1) (P : Formula 2) (w code : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) code.castSucc).imp (reverseCorrect test P w.castSucc (Fin.last m)))

theorem equation_rename {m l} (test : Formula 1) (P : Formula 2) (w : Fin m) (ρ : Fin m → Fin l) :
    (equation test P w).rename ρ = equation test P (ρ w) := by
  simp only [equation, Formula.rename, Formula.iff, property_rename, normalized_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem reverseCorrect_rename {m l} (test : Formula 1) (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (reverseCorrect test P w code).rename ρ = reverseCorrect test P (ρ w) (ρ code) := by
  simp only [reverseCorrect, Formula.rename, property_rename, ProofTreeEntryFacts.node_rename]

theorem reverseIH_rename {m l} (test : Formula 1) (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (reverseIH test P w code).rename ρ = reverseIH test P (ρ w) (ρ code) := by
  simp only [reverseIH, Formula.rename, reverseCorrect_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equation_at {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (w code : Fin m)
    (he : Derives Γ (equation test P w)) :
    Derives Γ ((property P w code).iff (normalized test P w code)) := of_eq
  (by simp only [Formula.instantiate, Formula.iff, Formula.rename, property_rename, normalized_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE code he)

theorem closure_from_equation {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (w : Fin m)
    (he : Derives Γ (equation test P w)) : Derives Γ (closure test P w) := by
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let N := Formula.mem (Fin.last m) w.castSucc
  let E := normalized test P w.castSucc (Fin.last m)
  have he1 := of_eq (equation_rename test P w Fin.castSucc) (under he N)
  exact .impE (.conjR (equation_at test P w.castSucc (Fin.last m) (add he1 E))) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProofTreeEquationSyntax

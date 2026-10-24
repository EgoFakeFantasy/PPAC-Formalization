import PPAC.Migration.Internal.ProofTreeRootLocal

/-! 原入口的变量重命名及候选载荷相等传输。 -/
namespace PPAC.Migration.Internal.ProofTreeEntryFacts
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem args2_map {α β : Type} (f : α → β) (a b : α) :
    (fun i => f (SetLanguage.args2 a b i)) = SetLanguage.args2 (f a) (f b) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun t => Fin.elim0 t) j

theorem node_rename {m l} (test : Formula 1) (w code : Fin m) (ρ : Fin m → Fin l) :
    (ProofTreeEntrySyntax.node test w code).rename ρ = ProofTreeEntrySyntax.node test (ρ w) (ρ code) := by
  simp only [ProofTreeEntrySyntax.node, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    ProofTreeTraceSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem root_rename {m l} (test : Formula 1) (w code conclusion : Fin m) (ρ : Fin m → Fin l) :
    (ProofTreeEntrySyntax.root test w code conclusion).rename ρ = ProofTreeEntrySyntax.root test (ρ w) (ρ code) (ρ conclusion) := by
  simp only [ProofTreeEntrySyntax.root, Formula.rename, SyntaxNodeSyntax.constructor_rename,
    ProofTreeTraceSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
  congr 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [SetLanguage.args2]
  · refine Fin.cases ?_ (fun t => Fin.elim0 t) j
    change Fin.lastCases (Fin.last l) (fun i => (ρ i).castSucc) conclusion.castSucc = (ρ conclusion).castSucc
    exact Fin.lastCases_castSucc conclusion

theorem node_subst {m} {Γ : Context m} (test : Formula 1) (w x y : Fin m)
    (he : Derives Γ (.equal x y)) (hx : Derives Γ (ProofTreeEntrySyntax.node test w x)) :
    Derives Γ (ProofTreeEntrySyntax.node test w y) := by
  let P := ProofTreeEntrySyntax.node test w.castSucc (Fin.last m)
  have h0 : P.instantiate x = ProofTreeEntrySyntax.node test w x := by
    simp only [P, Formula.instantiate, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate y = ProofTreeEntrySyntax.node test w y := by
    simp only [P, Formula.instantiate, node_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

end PPAC.Migration.Internal.ProofTreeEntryFacts

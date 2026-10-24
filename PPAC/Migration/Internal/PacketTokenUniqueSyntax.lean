import PPAC.Migration.Internal.PacketTokenValueTransport

/-! Output uniqueness quantifies every internal tail and both output candidates. -/
namespace PPAC.Migration.Internal.PacketTokenUniqueSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3
  ((accepted (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp
    ((accepted (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)).imp (.equal (slot 3 1) (slot 3 2))))

def matrix : Formula 2 := property 0 1

theorem property_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,Formula.rename,accepted_rename,lift_old,lift_slot]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem property_at {m} {Γ : Context m} (w n t a b : Fin m) (hp : Derives Γ (property w n))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w n t b)) : Derives Γ (.equal a b) := by
  have hi := OriginalUniversalBlock.at_many 3 _ (SyntaxAtomSyntax.three t a b) hp
  have he : Derives Γ ((accepted w n t a).imp ((accepted w n t b).imp (.equal a b))) :=
    of_eq (by simp only [Formula.rename,accepted_rename,assign_old,assign_slot]; rfl) hi
  exact .impE (.impE he ha) hb

theorem input_subst {m} {Γ : Context m} (w n q : Fin m) (he : Derives Γ (.equal n q))
    (hp : Derives Γ (property w n)) : Derives Γ (property w q) := by
  let P := property w.castSucc (Fin.last m)
  have h0 : P.instantiate n = property w n := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = property w q := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

end PPAC.Migration.Internal.PacketTokenUniqueSyntax

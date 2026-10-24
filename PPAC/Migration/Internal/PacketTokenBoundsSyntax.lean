import PPAC.Migration.Internal.PacketTokenBoundComparison

/-! Both quantitative bounds quantify all internal actual token candidates. -/
namespace PPAC.Migration.Internal.PacketTokenBoundsSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

def bounds {m} (n t a : Fin m) : Formula m := (below n a).conj (below t a)

def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2
  ((accepted (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)).imp (bounds (old 2 n) (slot 2 0) (slot 2 1)))

def matrix : Formula 2 := property 0 1

theorem bounds_rename {m j} (n t a : Fin m) (ρ : Fin m → Fin j) :
    (bounds n t a).rename ρ = bounds (ρ n) (ρ t) (ρ a) := rfl

theorem property_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,Formula.rename,accepted_rename,bounds_rename,lift_old,lift_slot]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem property_at {m} {Γ : Context m} (w n t a : Fin m) (hp : Derives Γ (property w n))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (bounds n t a) := by
  have hi := OriginalUniversalBlock.at_many 2 _ (SyntaxAtomSyntax.two t a) hp
  have he : Derives Γ ((accepted w n t a).imp (bounds n t a)) :=
    of_eq (by simp only [Formula.rename,accepted_rename,bounds_rename,assign_old,assign_slot]; rfl) hi
  exact .impE he ha

theorem input_subst {m} {Γ : Context m} (w n q : Fin m) (he : Derives Γ (.equal n q))
    (hp : Derives Γ (property w n)) : Derives Γ (property w q) := by
  let P := property w.castSucc (Fin.last m)
  have h0 : P.instantiate n = property w n := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = property w q := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

end PPAC.Migration.Internal.PacketTokenBoundsSyntax

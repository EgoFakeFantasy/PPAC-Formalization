import PPAC.Migration.Internal.PacketTokenPrefixTransport

/-! Prefix inversion jointly quantifies the numeric input and every remaining tail candidate. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 4
  ((accepted (old 4 w) (old 4 n) (slot 4 0) (slot 4 1)).imp
    ((accepted (old 4 w) (slot 4 2) (slot 4 3) (slot 4 1)).imp
      ((Formula.equal (old 4 n) (slot 4 2)).conj (.equal (slot 4 0) (slot 4 3)))))

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

theorem property_at {m} {Γ : Context m} (w n t a q s : Fin m) (hp : Derives Γ (property w n))
    (ha : Derives Γ (accepted w n t a)) (hb : Derives Γ (accepted w q s a)) :
    Derives Γ ((Formula.equal n q).conj (.equal t s)) := by
  have hi := OriginalUniversalBlock.at_many 4 _ (PacketTokenArithmeticSyntax.four t a q s) hp
  have he : Derives Γ ((accepted w n t a).imp ((accepted w q s a).imp ((Formula.equal n q).conj (.equal t s)))) :=
    of_eq (by simp only [Formula.rename,accepted_rename,assign_old,assign_slot]; rfl) hi
  exact .impE (.impE he ha) hb

theorem input_subst {m} {Γ : Context m} (w n q : Fin m) (he : Derives Γ (.equal n q))
    (hp : Derives Γ (property w n)) : Derives Γ (property w q) := by
  let P := property w.castSucc (Fin.last m)
  have h0 : P.instantiate n = property w n := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = property w q := by simp only [P,Formula.instantiate,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

end PPAC.Migration.Internal.PacketTokenPrefixSyntax

import PPAC.Migration.Internal.PacketVarintPrefixEquation

/-! A fixed object Formula2 compares original Tok with independently defined canonical Prefix for every tail and output. -/
namespace PPAC.Migration.Internal.PacketTokenCanonicalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintPrefixSyntax
open SyntaxRenameQuerySyntax (of_eq)

def agreement {m} (w n t a : Fin m) : Formula m := (PacketTokenAcceptedSyntax.accepted w n t a).iff (prefixCode w n t a)

def propertyBody {m} (w n : Fin m) : Formula (m+2) := agreement (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)

def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (propertyBody w n)

def matrix : Formula 2 := property 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def allProperties {m} (w : Fin m) : Formula m := .all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))

def lawBody {m} (w : Fin m) : Formula (m+3) := agreement (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w)

theorem agreement_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) : (agreement w n t a).rename ρ = agreement (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [agreement,Formula.iff,Formula.rename,PacketTokenAcceptedSyntax.accepted_rename,prefixCode_rename]

theorem propertyBody_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (propertyBody w n).rename (lift 2 ρ) = propertyBody (ρ w) (ρ n) := by
  simp only [propertyBody,agreement_rename,lift_old,lift_slot]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,propertyBody_lift]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allProperties_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allProperties w).rename ρ = allProperties (ρ w) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lawBody_lift {m k} (w : Fin m) (ρ : Fin m → Fin k) : (lawBody w).rename (lift 3 ρ) = lawBody (ρ w) := by
  simp only [lawBody,agreement_rename,lift_old,lift_slot]

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem property_at {m} {Γ : Context m} (w n t a : Fin m) (hp : Derives Γ (property w n)) : Derives Γ (agreement w n t a) := by
  have hi := OriginalUniversalBlock.at_many 2 (propertyBody w n) (SyntaxAtomSyntax.two t a) hp
  exact of_eq (by simp only [propertyBody,agreement_rename,assign_old,assign_slot]; rfl) hi

theorem earlier_at {m} {Γ : Context m} (w n q : Fin m) (hi : Derives Γ (earlier w n)) (hq : Derives Γ (.mem q w))
    (hqn : Derives Γ (.mem q n)) : Derives Γ (property w q) := by
  have he : Derives Γ ((Formula.mem q w).imp ((Formula.mem q n).imp (property w q))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE q hi)
  exact .impE (.impE he hq) hqn

end PPAC.Migration.Internal.PacketTokenCanonicalSyntax

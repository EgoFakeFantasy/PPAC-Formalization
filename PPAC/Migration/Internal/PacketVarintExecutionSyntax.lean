import PPAC.Migration.Internal.PacketVarintCanonicalRecursionLaws

/-! One fixed object Formula2 jointly states list existence, every-candidate byte validity and list uniqueness. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketVarintSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def existsList {m} (w n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (canonical w.castSucc n.castSucc (Fin.last m)))

def domain {m} (w n : Fin m) : Formula m := .all
  ((canonical w.castSucc n.castSucc (Fin.last m)).imp (byteList w.castSucc (Fin.last m)))

def unique {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2
  ((canonical (old 2 w) (old 2 n) (slot 2 0)).imp
    ((canonical (old 2 w) (old 2 n) (slot 2 1)).imp (.equal (slot 2 0) (slot 2 1))))

def property {m} (w n : Fin m) : Formula m := (existsList w n).conj ((domain w n).conj (unique w n))

def matrix : Formula 2 := property 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

theorem existsList_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (existsList w n).rename ρ = existsList (ρ w) (ρ n) := by
  simp only [existsList,Formula.rename,canonical_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem domain_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (domain w n).rename ρ = domain (ρ w) (ρ n) := by
  simp only [domain,Formula.rename,canonical_rename,byteList_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem unique_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (unique w n).rename ρ = unique (ρ w) (ρ n) := by
  simp only [unique,OriginalUniversalBlock.allMany_rename,Formula.rename,canonical_rename,lift_old,lift_slot]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,existsList_rename,domain_rename,unique_rename]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem intro_list {m} {Γ : Context m} (w n s : Fin m) (hs : Derives Γ (.mem s w))
    (hc : Derives Γ (canonical w n s)) : Derives Γ (existsList w n) := by
  apply Derives.exI s
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,canonical_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hs hc)

theorem domain_at {m} {Γ : Context m} (w n s : Fin m) (hp : Derives Γ (property w n)) (hc : Derives Γ (canonical w n s)) : Derives Γ (byteList w s) := by
  have he : Derives Γ ((canonical w n s).imp (byteList w s)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,canonical_rename,byteList_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE s (.conjL (.conjR hp)))
  exact .impE he hc

theorem unique_at {m} {Γ : Context m} (w n s t : Fin m) (hp : Derives Γ (property w n))
    (hs : Derives Γ (canonical w n s)) (ht : Derives Γ (canonical w n t)) : Derives Γ (.equal s t) := by
  have h := OriginalUniversalBlock.at_many 2 _ (SyntaxAtomSyntax.two s t) (.conjR (.conjR hp))
  have he : Derives Γ ((canonical w n s).imp ((canonical w n t).imp (.equal s t))) :=
    of_eq (by simp only [Formula.rename,canonical_rename,assign_old,assign_slot]; rfl) h
  exact .impE (.impE he hs) ht

theorem earlier_at {m} {Γ : Context m} (w n q : Fin m) (hi : Derives Γ (earlier w n)) (hq : Derives Γ (.mem q w))
    (hqn : Derives Γ (.mem q n)) : Derives Γ (property w q) := by
  have he : Derives Γ ((Formula.mem q w).imp ((Formula.mem q n).imp (property w q))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE q hi)
  exact .impE (.impE he hq) hqn

end PPAC.Migration.Internal.PacketVarintExecutionSyntax

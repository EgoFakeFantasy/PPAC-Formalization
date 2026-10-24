import PPAC.Migration.Internal.PacketByteInputLaws

/-! A fixed Formula2 jointly states totality, exact input domain and scalar uniqueness on all internal candidates. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketBytesTraceSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def existsOutput {m} (w n t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (bytes w.castSucc n.castSucc t.castSucc (Fin.last m)))

def total {m} (w n : Fin m) : Formula m := (byteList w n).imp (.all
  ((Formula.mem (Fin.last m) w.castSucc).imp (existsOutput w.castSucc n.castSucc (Fin.last m))))

def domain {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2
  ((bytes (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)).imp (byteList (old 2 w) (old 2 n)))

def unique {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3
  ((bytes (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp
    ((bytes (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)).imp (.equal (slot 3 1) (slot 3 2))))

def property {m} (w n : Fin m) : Formula m := (total w n).conj ((domain w n).conj (unique w n))

def matrix : Formula 2 := property 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

theorem existsOutput_rename {m k} (w n t : Fin m) (ρ : Fin m → Fin k) :
    (existsOutput w n t).rename ρ = existsOutput (ρ w) (ρ n) (ρ t) := by
  simp only [existsOutput,Formula.rename,bytes_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem total_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (total w n).rename ρ = total (ρ w) (ρ n) := by
  simp only [total,Formula.rename,byteList_rename,existsOutput_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem domain_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (domain w n).rename ρ = domain (ρ w) (ρ n) := by
  simp only [domain,OriginalUniversalBlock.allMany_rename,Formula.rename,bytes_rename,byteList_rename,lift_old,lift_slot]

theorem unique_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (unique w n).rename ρ = unique (ρ w) (ρ n) := by
  simp only [unique,OriginalUniversalBlock.allMany_rename,Formula.rename,bytes_rename,lift_old,lift_slot]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,total_rename,domain_rename,unique_rename]

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

theorem intro_output {m} {Γ : Context m} (w n t a : Fin m) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (bytes w n t a)) :
    Derives Γ (existsOutput w n t) := by
  apply Derives.exI a
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI ha hb)

theorem total_at {m} {Γ : Context m} (w n t : Fin m) (hp : Derives Γ (property w n))
    (hn : Derives Γ (byteList w n)) (ht : Derives Γ (.mem t w)) : Derives Γ (existsOutput w n t) := by
  have h := Derives.allE t (Derives.impE (.conjL hp) hn)
  have he : Derives Γ ((Formula.mem t w).imp (existsOutput w n t)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,existsOutput_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) h
  exact .impE he ht

theorem domain_at {m} {Γ : Context m} (w n t a : Fin m) (hp : Derives Γ (property w n)) (hb : Derives Γ (bytes w n t a)) :
    Derives Γ (byteList w n) := by
  have h := OriginalUniversalBlock.at_many 2 _ (SyntaxAtomSyntax.two t a) (.conjL (.conjR hp))
  have he : Derives Γ ((bytes w n t a).imp (byteList w n)) :=
    of_eq (by simp only [Formula.rename,bytes_rename,byteList_rename,assign_old,assign_slot]; rfl) h
  exact .impE he hb

theorem unique_at {m} {Γ : Context m} (w n t a b : Fin m) (hp : Derives Γ (property w n))
    (ha : Derives Γ (bytes w n t a)) (hb : Derives Γ (bytes w n t b)) : Derives Γ (.equal a b) := by
  have h := OriginalUniversalBlock.at_many 3 _ (SyntaxAtomSyntax.three t a b) (.conjR (.conjR hp))
  have he : Derives Γ ((bytes w n t a).imp ((bytes w n t b).imp (.equal a b))) :=
    of_eq (by simp only [Formula.rename,bytes_rename,assign_old,assign_slot]; rfl) h
  exact .impE (.impE he ha) hb

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (hi : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hxn : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have h := Derives.allE x hi
  have he : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property w x))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) h
  exact .impE (.impE he hx) hxn

end PPAC.Migration.Internal.PacketBytesExecutionSyntax

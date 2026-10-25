import PPAC.Migration.Internal.StructuralListSpliceTotal

/-! One fixed object property jointly states right-Nil identity and all-candidate associativity of actual splice. -/
namespace PPAC.Migration.Internal.StructuralListSpliceAlgebraSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax StructuralListSpliceSyntax
open SyntaxRenameQuerySyntax (of_eq)

def rightNil {m} (w n : Fin m) : Formula m := .all
  ((StructuralListSyntax.nilCode w.castSucc (Fin.last m)).imp (splice w.castSucc n.castSucc (Fin.last m) n.castSucc))

def associativeCase {m} (w n B C AB BC O : Fin m) : Formula m :=
  (splice w n B AB).imp ((splice w B C BC).imp ((splice w AB C O).iff (splice w n BC O)))

def associativeBody {m} (w n : Fin m) : Formula (m+5) :=
  associativeCase (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)

def associative {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 5 (associativeBody w n)

def property {m} (w n : Fin m) : Formula m := (StructuralListTraceSyntax.valid w n).imp ((rightNil w n).conj (associative w n))

def matrix : Formula 2 := property 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def five {m} (B C AB BC O : Fin m) : Fin 5 → Fin m := Fin.cases B (Fin.cases C (Fin.cases AB (Fin.cases BC (Fin.cases O Fin.elim0))))

theorem rightNil_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (rightNil w n).rename ρ = rightNil (ρ w) (ρ n) := by
  simp only [rightNil,Formula.rename,StructuralListSyntax.nilCode_rename,splice_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem associativeCase_rename {m k} (w n B C AB BC O : Fin m) (ρ : Fin m → Fin k) :
    (associativeCase w n B C AB BC O).rename ρ = associativeCase (ρ w) (ρ n) (ρ B) (ρ C) (ρ AB) (ρ BC) (ρ O) := by
  simp only [associativeCase,Formula.iff,Formula.rename,splice_rename]

theorem associativeBody_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (associativeBody w n).rename (lift 5 ρ) = associativeBody (ρ w) (ρ n) := by
  simp only [associativeBody,associativeCase_rename,lift_old,lift_slot]

theorem associative_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (associative w n).rename ρ = associative (ρ w) (ρ n) := by
  simp only [associative,OriginalUniversalBlock.allMany_rename,associativeBody_lift]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,StructuralListTraceSyntax.valid_rename,rightNil_rename,associative_rename]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by change Fin.lastCases n ρ (Fin.last 1) = n; exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,property_rename,h0,h1]

theorem right_at {m} {Γ : Context m} (w n e : Fin m) (hr : Derives Γ (rightNil w n))
    (he : Derives Γ (StructuralListSyntax.nilCode w e)) : Derives Γ (splice w n e n) := by
  have h : Derives Γ ((StructuralListSyntax.nilCode w e).imp (splice w n e n)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListSyntax.nilCode_rename,splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE e hr)
  exact .impE h he

theorem associate_at {m} {Γ : Context m} (w n B C AB BC O : Fin m) (ha : Derives Γ (associative w n))
    (hAB : Derives Γ (splice w n B AB)) (hBC : Derives Γ (splice w B C BC)) :
    Derives Γ ((splice w AB C O).iff (splice w n BC O)) := by
  have h : Derives Γ (associativeCase w n B C AB BC O) :=
    of_eq (by simp only [associativeBody,associativeCase_rename,assign_old,assign_slot,five]; rfl)
      (OriginalUniversalBlock.at_many 5 (associativeBody w n) (five B C AB BC O) ha)
  exact .impE (.impE h hAB) hBC

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (hi : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hb : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have h : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property w x))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE x hi)
  exact .impE (.impE h hx) hb

end PPAC.Migration.Internal.StructuralListSpliceAlgebraSyntax

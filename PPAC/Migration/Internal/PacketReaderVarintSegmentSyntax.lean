import PPAC.Migration.Internal.PacketReaderVarintBranches
import PPAC.Migration.Internal.PacketReaderAffineCompose
import PPAC.Migration.Internal.StructuralListSplice

/-! One fixed object formula universally quantifies actual canonical lists, arbitrary trailing input, value/scale/accumulator and all return candidates. -/
namespace PPAC.Migration.Internal.PacketReaderVarintSegmentSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderEvalSyntax
open SyntaxRenameQuerySyntax (of_eq)

def nine {m} (C T L v s a u c p : Fin m) : Fin 9 → Fin m :=
  Fin.cases C (Fin.cases T (Fin.cases L (Fin.cases v (Fin.cases s (Fin.cases a (Fin.cases u (Fin.cases c (Fin.cases p Fin.elim0))))))))

def guard {m} (o n s : Fin m) : Formula m := (Formula.equal s o).disj (empty n).neg

def agreement {m} (w B z o L T v s a c p : Fin m) : Formula m :=
  (eval w B z o L v s a p).iff (eval w B z o T z o c p)

def caseFormula {m} (w B z o n C T L v s a u c p : Fin m) : Formula m :=
  (PacketVarintSyntax.canonical w n C).imp ((StructuralListSpliceSyntax.splice w C T L).imp
    ((PacketReaderStepSyntax.state w T v s a).imp ((guard o n s).imp
      ((PacketAffineSyntax.equation w n v s u).imp ((StructuralListSyntax.consCode w u a c).imp (agreement w B z o L T v s a c p))))))

def body {m} (w B z o n : Fin m) : Formula (m+9) :=
  caseFormula (old 9 w) (old 9 B) (old 9 z) (old 9 o) (old 9 n)
    (slot 9 0) (slot 9 1) (slot 9 2) (slot 9 3) (slot 9 4) (slot 9 5) (slot 9 6) (slot 9 7) (slot 9 8)

def property {m} (w B z o n : Fin m) : Formula m := OriginalUniversalBlock.allMany 9 (body w B z o n)

def matrix : Formula 5 := property 0 1 2 3 4

def earlier {m} (w B z o n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m))))

def allProperties {m} (w B z o : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)))

theorem guard_rename {m k} (o n s : Fin m) (ρ : Fin m → Fin k) : (guard o n s).rename ρ = guard (ρ o) (ρ n) (ρ s) := by
  simp only [guard,Formula.rename,Formula.neg,empty_rename]

theorem agreement_rename {m k} (w B z o L T v s a c p : Fin m) (ρ : Fin m → Fin k) :
    (agreement w B z o L T v s a c p).rename ρ = agreement (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ T) (ρ v) (ρ s) (ρ a) (ρ c) (ρ p) := by
  simp only [agreement,Formula.iff,Formula.rename,eval_rename]

theorem caseFormula_rename {m k} (w B z o n C T L v s a u c p : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w B z o n C T L v s a u c p).rename ρ = caseFormula (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ C) (ρ T) (ρ L) (ρ v) (ρ s) (ρ a) (ρ u) (ρ c) (ρ p) := by
  simp only [caseFormula,Formula.rename,PacketVarintSyntax.canonical_rename,StructuralListSpliceSyntax.splice_rename,PacketReaderStepSyntax.state_rename,guard_rename,PacketAffineSyntax.equation_rename,StructuralListSyntax.consCode_rename,agreement_rename]

theorem body_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (body w B z o n).rename (lift 9 ρ) = body (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [body,caseFormula_rename,lift_old,lift_slot]

theorem property_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (property w B z o n).rename ρ = property (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,body_lift]

theorem earlier_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w B z o n).rename ρ = earlier (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allProperties_rename {m k} (w B z o : Fin m) (ρ : Fin m → Fin k) :
    (allProperties w B z o).rename ρ = allProperties (ρ w) (ρ B) (ρ z) (ρ o) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = property (ρ 0) (ρ 1) (ρ 2) (ρ 3) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 5) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 4).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 5) = ρ 1 := by change Fin.lastCases n ρ (1 : Fin 4).castSucc = ρ 1; exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases n ρ (2 : Fin 5) = ρ 2 := by change Fin.lastCases n ρ (2 : Fin 4).castSucc = ρ 2; exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases n ρ (3 : Fin 5) = ρ 3 := by change Fin.lastCases n ρ (3 : Fin 4).castSucc = ρ 3; exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases n ρ (4 : Fin 5) = n := by change Fin.lastCases n ρ (Fin.last 4) = n; exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1,h2,h3,h4]

theorem at_fields {m} {Γ : Context m} (w B z o n C T L v s a u c p : Fin m)
    (hp : Derives Γ (property w B z o n)) : Derives Γ (caseFormula w B z o n C T L v s a u c p) := by
  exact of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot,nine]; rfl)
    (OriginalUniversalBlock.at_many 9 (body w B z o n) (nine C T L v s a u c p) hp)

theorem earlier_at {m} {Γ : Context m} (w B z o n k : Fin m) (hi : Derives Γ (earlier w B z o n))
    (hk : Derives Γ (.mem k w)) (hkn : Derives Γ (.mem k n)) : Derives Γ (property w B z o k) := by
  have h : Derives Γ ((Formula.mem k w).imp ((Formula.mem k n).imp (property w B z o k))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE k hi)
  exact .impE (.impE h hk) hkn

end PPAC.Migration.Internal.PacketReaderVarintSegmentSyntax

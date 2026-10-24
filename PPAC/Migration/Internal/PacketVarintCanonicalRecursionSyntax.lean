import PPAC.Migration.Internal.PacketVarintRecursionEquation

/-! Independent exact canonical recursion has a singleton terminal or a nonzero smaller canonical suffix. -/
namespace PPAC.Migration.Internal.PacketVarintCanonicalRecursionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintSyntax
open SyntaxRenameQuerySyntax (of_eq)

def four {m} (d q h x : Fin m) : Fin 4 → Fin m := Fin.cases d (Fin.cases q (Fin.cases h (Fin.cases x Fin.elim0)))

def singleton {m} (w n s : Fin m) : Formula m := .ex
  ((StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj (StructuralListSyntax.consCode w.castSucc n.castSucc (Fin.last m) s.castSucc))

def smallCase {m} (w B n s : Fin m) : Formula m := (Formula.mem n B).conj (singleton w n s)

def recursiveInput (actual : Bool) {m} (w B q x : Fin m) : Formula m := match actual with
  | false => canonicalAt w B q x
  | true => canonical w q x

theorem recursiveInput_rename (actual : Bool) {m k} (w B q x : Fin m) (ρ : Fin m → Fin k) :
    (recursiveInput actual w B q x).rename ρ = recursiveInput actual (ρ w) (ρ B) (ρ q) (ρ x) := by
  cases actual
  · exact canonicalAt_rename w B q x ρ
  · exact canonical_rename w q x ρ

def largeBody (actual : Bool) {m} (w B n s : Fin m) : Formula (m+4) :=
  (PacketAffineSyntax.affine (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (old 4 n)).conj
    ((empty (slot 4 1)).neg.conj ((NaturalAdditionSyntax.sum (old 4 w) (slot 4 0) (old 4 B) (slot 4 2)).conj
      ((recursiveInput actual (old 4 w) (old 4 B) (slot 4 1) (slot 4 3)).conj
        (StructuralListSyntax.consCode (old 4 w) (slot 4 2) (slot 4 3) (old 4 s)))))

def largeCase (actual : Bool) {m} (w B n s : Fin m) : Formula m := existsMany 4 (largeBody actual w B n s)

def atCriterion (actual : Bool) {m} (w B n s : Fin m) : Formula m := (smallCase w B n s).disj (largeCase actual w B n s)

def actualBody {m} (w n s : Fin m) : Formula (m+1) :=
  (SyntaxNumeralSyntax.numeral 128 (Fin.last m)).conj (atCriterion true w.castSucc (Fin.last m) n.castSucc s.castSucc)

def criterion {m} (w n s : Fin m) : Formula m := .ex (actualBody w n s)

def lawBody {m} (w : Fin m) : Formula (m+2) :=
  (canonical (old 2 w) (slot 2 0) (slot 2 1)).iff (criterion (old 2 w) (slot 2 0) (slot 2 1))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (lawBody w)

theorem singleton_rename {m k} (w n s : Fin m) (ρ : Fin m → Fin k) :
    (singleton w n s).rename ρ = singleton (ρ w) (ρ n) (ρ s) := by
  simp only [singleton,Formula.rename,StructuralListSyntax.nilCode_rename,StructuralListSyntax.consCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem smallCase_rename {m k} (w B n s : Fin m) (ρ : Fin m → Fin k) :
    (smallCase w B n s).rename ρ = smallCase (ρ w) (ρ B) (ρ n) (ρ s) := by simp only [smallCase,Formula.rename,singleton_rename]

theorem largeBody_lift (actual : Bool) {m k} (w B n s : Fin m) (ρ : Fin m → Fin k) :
    (largeBody actual w B n s).rename (lift 4 ρ) = largeBody actual (ρ w) (ρ B) (ρ n) (ρ s) := by
  simp only [largeBody,Formula.neg,Formula.rename,PacketAffineSyntax.affine_rename,empty_rename,NaturalAdditionSyntax.sum_rename,recursiveInput_rename,StructuralListSyntax.consCode_rename,lift_old,lift_slot]

theorem largeCase_rename (actual : Bool) {m k} (w B n s : Fin m) (ρ : Fin m → Fin k) :
    (largeCase actual w B n s).rename ρ = largeCase actual (ρ w) (ρ B) (ρ n) (ρ s) := by simp only [largeCase,existsMany_rename,largeBody_lift]

theorem atCriterion_rename (actual : Bool) {m k} (w B n s : Fin m) (ρ : Fin m → Fin k) :
    (atCriterion actual w B n s).rename ρ = atCriterion actual (ρ w) (ρ B) (ρ n) (ρ s) := by simp only [atCriterion,Formula.rename,smallCase_rename,largeCase_rename]

theorem criterion_rename {m k} (w n s : Fin m) (ρ : Fin m → Fin k) :
    (criterion w n s).rename ρ = criterion (ρ w) (ρ n) (ρ s) := by
  simp only [criterion,actualBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,atCriterion_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lawBody_lift {m k} (w : Fin m) (ρ : Fin m → Fin k) : (lawBody w).rename (lift 2 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.iff,Formula.rename,canonical_rename,criterion_rename,lift_old,lift_slot]

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem intro_singleton {m} {Γ : Context m} (w n s e : Fin m) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hc : Derives Γ (StructuralListSyntax.consCode w n e s)) : Derives Γ (singleton w n s) := by
  apply Derives.exI e
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListSyntax.nilCode_rename,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI he hc)

theorem intro_large (actual : Bool) {m} {Γ : Context m} (w B n s d q h x : Fin m)
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hq : Derives Γ (empty q).neg)
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h))
    (hp : Derives Γ (recursiveInput actual w B q x))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) : Derives Γ (largeCase actual w B n s) := by
  apply HornBinderRules.intro_many 4 (largeBody actual w B n s) (four d q h x)
  exact of_eq (by simp only [largeBody,Formula.neg,Formula.rename,PacketAffineSyntax.affine_rename,empty_rename,NaturalAdditionSyntax.sum_rename,recursiveInput_rename,StructuralListSyntax.consCode_rename,assign_old,assign_slot]; rfl)
    (.conjI ha (.conjI hq (.conjI hs (.conjI hp hc))))

theorem intro_criterion {m} {Γ : Context m} (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hc : Derives Γ (atCriterion true w B n s)) : Derives Γ (criterion w n s) := by
  apply Derives.exI B
  exact of_eq (by simp only [actualBody,Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,atCriterion_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hB hc)

end PPAC.Migration.Internal.PacketVarintCanonicalRecursionSyntax

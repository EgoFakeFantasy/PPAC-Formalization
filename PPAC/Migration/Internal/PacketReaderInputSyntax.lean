import PPAC.Migration.Internal.PacketReaderStepExistence
import PPAC.Migration.Internal.StructuralListTraceInvert

/-! Full reader input binding: actual Cons head/rest and the raw source state are part of the transition graph. -/
namespace PPAC.Migration.Internal.PacketReaderInputSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open PacketReaderStepSyntax (state state_rename)
open SyntaxRenameQuerySyntax (of_eq)

def headRest {m} (w l b x : Fin m) : Formula m :=
  (Formula.mem b w).conj ((StructuralListTraceSyntax.valid w x).conj (StructuralListSyntax.consCode w b x l))
def headBody {m} (w l : Fin m) : Formula (m+2) := headRest (old 2 w) (old 2 l) (slot 2 0) (slot 2 1)
def hasHead {m} (w l : Fin m) : Formula m := existsMany 2 (headBody w l)
def blockedBody {m} (w B z o l s : Fin m) : Formula (m+2) :=
  (headBody w l).conj (PacketReaderStepSyntax.reject (old 2 B) (old 2 z) (old 2 o) (slot 2 0) (old 2 s))
def blocked {m} (w B z o l s : Fin m) : Formula m := existsMany 2 (blockedBody w B z o l s)
def advanceBody {m} (w B z o l v s a r y q c : Fin m) : Formula (m+2) :=
  (headBody w l).conj (PacketReaderStepSyntax.step (old 2 w) (old 2 B) (old 2 z) (old 2 o) (slot 2 0) (slot 2 1)
    (old 2 v) (old 2 s) (old 2 a) (old 2 r) (old 2 y) (old 2 q) (old 2 c))
def advance {m} (w B z o l v s a r y q c : Fin m) : Formula m :=
  (state w l v s a).conj (existsMany 2 (advanceBody w B z o l v s a r y q c))
def resultBody {m} (w B z o l v s a : Fin m) : Formula (m+4) :=
  (state (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).conj
    (advance (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 v) (old 4 s) (old 4 a)
      (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))
def existsResult {m} (w B z o l v s a : Fin m) : Formula m := existsMany 4 (resultBody w B z o l v s a)
def eofSuccess {m} (w z o l v s a : Fin m) : Formula m :=
  (state w l v s a).conj ((StructuralListSyntax.nilCode w l).conj (PacketReaderStepSyntax.eof z o v s))
def eofFailure {m} (w z o l v s a : Fin m) : Formula m :=
  (state w l v s a).conj ((StructuralListSyntax.nilCode w l).conj (PacketReaderStepSyntax.eof z o v s).neg)

theorem headRest_rename {m k} (w l b x : Fin m) (ρ : Fin m → Fin k) :
    (headRest w l b x).rename ρ = headRest (ρ w) (ρ l) (ρ b) (ρ x) := by
  simp only [headRest,Formula.rename,StructuralListTraceSyntax.valid_rename,StructuralListSyntax.consCode_rename]

theorem headBody_lift {m k} (w l : Fin m) (ρ : Fin m → Fin k) :
    (headBody w l).rename (lift 2 ρ) = headBody (ρ w) (ρ l) := by
  simp only [headBody,headRest_rename,lift_old,lift_slot]

theorem hasHead_rename {m k} (w l : Fin m) (ρ : Fin m → Fin k) :
    (hasHead w l).rename ρ = hasHead (ρ w) (ρ l) := by
  simp only [hasHead,existsMany_rename,headBody_lift]

theorem blockedBody_lift {m k} (w B z o l s : Fin m) (ρ : Fin m → Fin k) :
    (blockedBody w B z o l s).rename (lift 2 ρ) = blockedBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ s) := by
  simp only [blockedBody,Formula.rename,headBody_lift,PacketReaderStepSyntax.reject_rename,lift_old,lift_slot]

theorem blocked_rename {m k} (w B z o l s : Fin m) (ρ : Fin m → Fin k) :
    (blocked w B z o l s).rename ρ = blocked (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ s) := by
  simp only [blocked,existsMany_rename,blockedBody_lift]

theorem advanceBody_lift {m k} (w B z o l v s a r y q c : Fin m) (ρ : Fin m → Fin k) :
    (advanceBody w B z o l v s a r y q c).rename (lift 2 ρ) = advanceBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) (ρ r) (ρ y) (ρ q) (ρ c) := by
  simp only [advanceBody,Formula.rename,headBody_lift,PacketReaderStepSyntax.step_rename,lift_old,lift_slot]

theorem advance_rename {m k} (w B z o l v s a r y q c : Fin m) (ρ : Fin m → Fin k) :
    (advance w B z o l v s a r y q c).rename ρ = advance (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) (ρ r) (ρ y) (ρ q) (ρ c) := by
  simp only [advance,Formula.rename,state_rename,existsMany_rename,advanceBody_lift]

theorem resultBody_lift {m k} (w B z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (resultBody w B z o l v s a).rename (lift 4 ρ) = resultBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [resultBody,Formula.rename,state_rename,advance_rename,lift_old,lift_slot]

theorem existsResult_rename {m k} (w B z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (existsResult w B z o l v s a).rename ρ = existsResult (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [existsResult,existsMany_rename,resultBody_lift]

theorem eofSuccess_rename {m k} (w z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (eofSuccess w z o l v s a).rename ρ = eofSuccess (ρ w) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [eofSuccess,Formula.rename,state_rename,StructuralListSyntax.nilCode_rename,PacketReaderStepSyntax.eof_rename]

theorem eofFailure_rename {m k} (w z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (eofFailure w z o l v s a).rename ρ = eofFailure (ρ w) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [eofFailure,Formula.rename,state_rename,StructuralListSyntax.nilCode_rename,PacketReaderStepSyntax.eof_rename,Formula.neg]

theorem intro_head {m} {Γ : Context m} (w l b x : Fin m) (hh : Derives Γ (headRest w l b x)) : Derives Γ (hasHead w l) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two b x)
  exact of_eq (by simp only [headBody,headRest_rename,assign_old,assign_slot]; rfl) hh

theorem intro_blocked {m} {Γ : Context m} (w B z o l s b x : Fin m) (hh : Derives Γ (headRest w l b x))
    (hr : Derives Γ (PacketReaderStepSyntax.reject B z o b s)) : Derives Γ (blocked w B z o l s) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two b x)
  exact of_eq (by simp only [blockedBody,headBody,Formula.rename,headRest_rename,PacketReaderStepSyntax.reject_rename,assign_old,assign_slot]; rfl) (.conjI hh hr)

theorem intro_advance {m} {Γ : Context m} (w B z o l v s a r y q c b x : Fin m)
    (hi : Derives Γ (state w l v s a)) (hh : Derives Γ (headRest w l b x))
    (ht : Derives Γ (PacketReaderStepSyntax.step w B z o b x v s a r y q c)) : Derives Γ (advance w B z o l v s a r y q c) := by
  apply Derives.conjI hi
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two b x)
  exact of_eq (by simp only [advanceBody,headBody,Formula.rename,headRest_rename,PacketReaderStepSyntax.step_rename,assign_old,assign_slot]; rfl) (.conjI hh ht)

theorem intro_result {m} {Γ : Context m} (w B z o l v s a r y q c : Fin m)
    (hi : Derives Γ (state w r y q c)) (hh : Derives Γ (advance w B z o l v s a r y q c)) :
    Derives Γ (existsResult w B z o l v s a) := by
  apply HornBinderRules.intro_many 4 _ (PacketVarintPrefixRecursionSyntax.four r y q c)
  exact of_eq (by simp only [resultBody,Formula.rename,state_rename,advance_rename,assign_old,assign_slot]; rfl) (.conjI hi hh)

end PPAC.Migration.Internal.PacketReaderInputSyntax

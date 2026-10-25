import PPAC.Migration.Internal.PacketReaderStateCode

/-! Independent coded one-step relation uses the actual four-field source and target codes plus the full raw reader step. -/
namespace PPAC.Migration.Internal.PacketReaderCodedSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStateSyntax
open SyntaxRenameQuerySyntax (of_eq)

def eight {m} (l v s a x y q c : Fin m) : Fin 8 → Fin m := Fin.cases l (Fin.cases v (Fin.cases s (Fin.cases a (Fin.cases x (Fin.cases y (Fin.cases q (Fin.cases c Fin.elim0)))))))
def nextBody {m} (w B z o l v s a r : Fin m) : Formula (m+4) :=
  (code (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 r)).conj
    (PacketReaderInputSyntax.advance (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 v) (old 4 s) (old 4 a)
      (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))
def nextAt {m} (w B z o l v s a r : Fin m) : Formula m := existsMany 4 (nextBody w B z o l v s a r)
def stepBody {m} (w B z o n r : Fin m) : Formula (m+8) :=
  (code (old 8 w) (slot 8 0) (slot 8 1) (slot 8 2) (slot 8 3) (old 8 n)).conj
    ((code (old 8 w) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7) (old 8 r)).conj
      (PacketReaderInputSyntax.advance (old 8 w) (old 8 B) (old 8 z) (old 8 o)
        (slot 8 0) (slot 8 1) (slot 8 2) (slot 8 3) (slot 8 4) (slot 8 5) (slot 8 6) (slot 8 7)))
def step {m} (w B z o n r : Fin m) : Formula m := existsMany 8 (stepBody w B z o n r)
def existsNext {m} (w B z o n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (step w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)))

theorem nextBody_lift {m k} (w B z o l v s a r : Fin m) (ρ : Fin m → Fin k) :
    (nextBody w B z o l v s a r).rename (lift 4 ρ) = nextBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) (ρ r) := by
  simp only [nextBody,Formula.rename,code_rename,PacketReaderInputSyntax.advance_rename,lift_old,lift_slot]

theorem nextAt_rename {m k} (w B z o l v s a r : Fin m) (ρ : Fin m → Fin k) :
    (nextAt w B z o l v s a r).rename ρ = nextAt (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) (ρ r) := by
  simp only [nextAt,existsMany_rename,nextBody_lift]

theorem stepBody_lift {m k} (w B z o n r : Fin m) (ρ : Fin m → Fin k) :
    (stepBody w B z o n r).rename (lift 8 ρ) = stepBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) := by
  simp only [stepBody,Formula.rename,code_rename,PacketReaderInputSyntax.advance_rename,lift_old,lift_slot]

theorem step_rename {m k} (w B z o n r : Fin m) (ρ : Fin m → Fin k) :
    (step w B z o n r).rename ρ = step (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) := by
  simp only [step,existsMany_rename,stepBody_lift]

theorem existsNext_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (existsNext w B z o n).rename ρ = existsNext (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [existsNext,Formula.rename,step_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_next {m} {Γ : Context m} (w B z o l v s a r x y q c : Fin m)
    (hc : Derives Γ (code w x y q c r)) (ha : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) :
    Derives Γ (nextAt w B z o l v s a r) := by
  apply HornBinderRules.intro_many 4 _ (fields x y q c)
  exact of_eq (by simp only [nextBody,Formula.rename,code_rename,PacketReaderInputSyntax.advance_rename,assign_old,assign_slot]; rfl) (.conjI hc ha)

theorem intro_step {m} {Γ : Context m} (w B z o n r l v s a x y q c : Fin m)
    (hn : Derives Γ (code w l v s a n)) (hr : Derives Γ (code w x y q c r))
    (ha : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) : Derives Γ (step w B z o n r) := by
  apply HornBinderRules.intro_many 8 _ (eight l v s a x y q c)
  exact of_eq (by simp only [stepBody,Formula.rename,code_rename,PacketReaderInputSyntax.advance_rename,assign_old,assign_slot]; rfl) (.conjI hn (.conjI hr ha))

end PPAC.Migration.Internal.PacketReaderCodedSyntax

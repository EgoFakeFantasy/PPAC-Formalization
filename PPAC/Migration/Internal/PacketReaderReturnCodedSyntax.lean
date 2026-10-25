import PPAC.Migration.Internal.PacketReaderReturnUnique

/-! Actual coded return and actual run retain original decoded source fields and original complete history graphs. -/
namespace PPAC.Migration.Internal.PacketReaderReturnCodedSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

def codedBody {m} (w B z o n q : Fin m) : Formula (m+4) :=
  (PacketReaderStateSyntax.carrierBody w n).conj
    (result (old 4 w) (old 4 B) (old 4 z) (old 4 o) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 q))

def coded {m} (w B z o n q : Fin m) : Formula m := existsMany 4 (codedBody w B z o n q)

def existsCoded {m} (w B z o n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (coded w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)))

def runBody {m} (w B z o n q : Fin m) : Formula (m+4) :=
  (PacketReaderHistorySyntax.history (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).conj
    (coded (old 4 w) (old 4 B) (old 4 z) (old 4 o) (slot 4 0) (old 4 q))

def run {m} (w B z o n q : Fin m) : Formula m := existsMany 4 (runBody w B z o n q)

def existsRun {m} (w B z o n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (run w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)))

def runFiber {m} (w B z o n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (run w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m))).conj (.all
    ((run w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem codedBody_lift {m k} (w B z o n q : Fin m) (ρ : Fin m → Fin k) :
    (codedBody w B z o n q).rename (lift 4 ρ) = codedBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ q) := by
  simp only [codedBody,Formula.rename,PacketReaderStateSyntax.carrierBody_lift,result_rename,lift_old,lift_slot]

theorem coded_rename {m k} (w B z o n q : Fin m) (ρ : Fin m → Fin k) :
    (coded w B z o n q).rename ρ = coded (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ q) := by
  simp only [coded,existsMany_rename,codedBody_lift]

theorem existsCoded_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (existsCoded w B z o n).rename ρ = existsCoded (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [existsCoded,Formula.rename,coded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem runBody_lift {m k} (w B z o n q : Fin m) (ρ : Fin m → Fin k) :
    (runBody w B z o n q).rename (lift 4 ρ) = runBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ q) := by
  simp only [runBody,Formula.rename,PacketReaderHistorySyntax.history_rename,coded_rename,lift_old,lift_slot]

theorem run_rename {m k} (w B z o n q : Fin m) (ρ : Fin m → Fin k) :
    (run w B z o n q).rename ρ = run (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ q) := by
  simp only [run,existsMany_rename,runBody_lift]

theorem existsRun_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (existsRun w B z o n).rename ρ = existsRun (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [existsRun,Formula.rename,run_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem runFiber_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (runFiber w B z o n).rename ρ = runFiber (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [runFiber,Formula.rename,run_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_coded {m} {Γ : Context m} (w B z o n q L v s a : Fin m)
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (hr : Derives Γ (result w B z o L v s a q)) :
    Derives Γ (coded w B z o n q) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields L v s a)
  exact of_eq (by simp only [codedBody,PacketReaderStateSyntax.carrierBody,Formula.rename,PacketReaderStateSyntax.code_rename,result_rename,assign_old,assign_slot]; rfl) (.conjI hc hr)

theorem intro_run {m} {Γ : Context m} (w B z o n q r l d f : Fin m)
    (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f)) (hr : Derives Γ (coded w B z o r q)) :
    Derives Γ (run w B z o n q) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields r l d f)
  exact of_eq (by simp only [runBody,Formula.rename,PacketReaderHistorySyntax.history_rename,coded_rename,assign_old,assign_slot]; rfl) (.conjI hh hr)

end PPAC.Migration.Internal.PacketReaderReturnCodedSyntax

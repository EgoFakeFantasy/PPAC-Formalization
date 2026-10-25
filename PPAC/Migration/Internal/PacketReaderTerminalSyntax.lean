import PPAC.Migration.Internal.PacketReaderStoppingContract

/-! Original three stopping observations and actual endpoint field witnesses, independent of stopped histories. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def raw {m} (w B z o L v s a : Fin m) : Formula m :=
  (eofSuccess w z o L v s a).disj ((eofFailure w z o L v s a).disj
    ((PacketReaderStepSyntax.state w L v s a).conj (blocked w B z o L s)))

def observationBody {m} (w B z o n : Fin m) : Formula (m+4) :=
  (PacketReaderStateSyntax.carrierBody w n).conj
    (raw (old 4 w) (old 4 B) (old 4 z) (old 4 o) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))

def observation {m} (w B z o n : Fin m) : Formula m := existsMany 4 (observationBody w B z o n)

def classifiedHistory {m} (w B z o n r l d f : Fin m) : Formula m :=
  (PacketReaderHistorySyntax.history w B z o n r l d f).conj (observation w B z o r)

def classifiedBody {m} (w B z o n : Fin m) : Formula (m+4) :=
  classifiedHistory (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def classifiedComplete {m} (w B z o n : Fin m) : Formula m := existsMany 4 (classifiedBody w B z o n)

theorem raw_rename {m k} (w B z o L v s a : Fin m) (ρ : Fin m → Fin k) :
    (raw w B z o L v s a).rename ρ = raw (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) := by
  simp only [raw,Formula.rename,eofSuccess_rename,eofFailure_rename,PacketReaderStepSyntax.state_rename,blocked_rename]

theorem observationBody_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (observationBody w B z o n).rename (lift 4 ρ) = observationBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [observationBody,Formula.rename,PacketReaderStateSyntax.carrierBody_lift,raw_rename,lift_old,lift_slot]

theorem observation_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (observation w B z o n).rename ρ = observation (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [observation,existsMany_rename,observationBody_lift]

theorem classifiedHistory_rename {m k} (w B z o n r l d f : Fin m) (ρ : Fin m → Fin k) :
    (classifiedHistory w B z o n r l d f).rename ρ = classifiedHistory (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) (ρ f) := by
  simp only [classifiedHistory,Formula.rename,PacketReaderHistorySyntax.history_rename,observation_rename]

theorem classifiedBody_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (classifiedBody w B z o n).rename (lift 4 ρ) = classifiedBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [classifiedBody,classifiedHistory_rename,lift_old,lift_slot]

theorem classifiedComplete_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (classifiedComplete w B z o n).rename ρ = classifiedComplete (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [classifiedComplete,existsMany_rename,classifiedBody_lift]

theorem intro_observation {m} {Γ : Context m} (w B z o n L v s a : Fin m)
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (hr : Derives Γ (raw w B z o L v s a)) :
    Derives Γ (observation w B z o n) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields L v s a)
  exact of_eq (by simp only [observationBody,PacketReaderStateSyntax.carrierBody,Formula.rename,PacketReaderStateSyntax.code_rename,raw_rename,assign_old,assign_slot]; rfl) (.conjI hc hr)

theorem intro_classified {m} {Γ : Context m} (w B z o n r l d f : Fin m)
    (hh : Derives Γ (classifiedHistory w B z o n r l d f)) : Derives Γ (classifiedComplete w B z o n) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields r l d f)
  exact of_eq (by simp only [classifiedBody,classifiedHistory_rename,assign_old,assign_slot]; rfl) hh

end PPAC.Migration.Internal.PacketReaderTerminalSyntax

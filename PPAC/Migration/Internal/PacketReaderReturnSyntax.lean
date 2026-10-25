import PPAC.Migration.Internal.ObjectStructuralListReverse

/-! Option results are original zero/one-cell forest codes; successful EOF carries the actual reversed accumulator code. -/
namespace PPAC.Migration.Internal.PacketReaderReturnSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def none {m} (w q : Fin m) : Formula m := StructuralListSyntax.nilCode w q

def some {m} (w r q : Fin m) : Formula m := SyntaxForestSyntax.forest 1 w (fun _ => r) q

def success {m} (w z o L v s a q : Fin m) : Formula m :=
  (PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (.ex
    ((StructuralListReverseSyntax.reverses w.castSucc a.castSucc (Fin.last m)).conj (some w.castSucc (Fin.last m) q.castSucc)))

def rejection {m} (w B z o L v s a : Fin m) : Formula m :=
  (PacketReaderInputSyntax.eofFailure w z o L v s a).disj
    ((PacketReaderStepSyntax.state w L v s a).conj (PacketReaderInputSyntax.blocked w B z o L s))

def failure {m} (w B z o L v s a q : Fin m) : Formula m := (rejection w B z o L v s a).conj (none w q)

def result {m} (w B z o L v s a q : Fin m) : Formula m := (success w z o L v s a q).disj (failure w B z o L v s a q)

def existsResult {m} (w B z o L v s a : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (result w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)))

theorem none_rename {m k} (w q : Fin m) (ρ : Fin m → Fin k) : (none w q).rename ρ = none (ρ w) (ρ q) := StructuralListSyntax.nilCode_rename _ _ _

theorem some_rename {m k} (w r q : Fin m) (ρ : Fin m → Fin k) : (some w r q).rename ρ = some (ρ w) (ρ r) (ρ q) := by
  simp only [some,SyntaxForestSyntax.forest_rename]

theorem success_rename {m k} (w z o L v s a q : Fin m) (ρ : Fin m → Fin k) :
    (success w z o L v s a q).rename ρ = success (ρ w) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) (ρ q) := by
  simp only [success,Formula.rename,PacketReaderInputSyntax.eofSuccess_rename,StructuralListReverseSyntax.reverses_rename,some_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem rejection_rename {m k} (w B z o L v s a : Fin m) (ρ : Fin m → Fin k) :
    (rejection w B z o L v s a).rename ρ = rejection (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) := by
  simp only [rejection,Formula.rename,PacketReaderInputSyntax.eofFailure_rename,PacketReaderStepSyntax.state_rename,PacketReaderInputSyntax.blocked_rename]

theorem failure_rename {m k} (w B z o L v s a q : Fin m) (ρ : Fin m → Fin k) :
    (failure w B z o L v s a q).rename ρ = failure (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) (ρ q) := by
  simp only [failure,Formula.rename,rejection_rename,none_rename]

theorem result_rename {m k} (w B z o L v s a q : Fin m) (ρ : Fin m → Fin k) :
    (result w B z o L v s a q).rename ρ = result (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) (ρ q) := by
  simp only [result,Formula.rename,success_rename,failure_rename]

theorem existsResult_rename {m k} (w B z o L v s a : Fin m) (ρ : Fin m → Fin k) :
    (existsResult w B z o L v s a).rename ρ = existsResult (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) := by
  simp only [existsResult,Formula.rename,result_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_success {m} {Γ : Context m} (w z o L v s a r q : Fin m)
    (he : Derives Γ (PacketReaderInputSyntax.eofSuccess w z o L v s a))
    (hr : Derives Γ (StructuralListReverseSyntax.reverses w a r)) (hq : Derives Γ (some w r q)) :
    Derives Γ (success w z o L v s a q) := by
  apply Derives.conjI he
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListReverseSyntax.reverses_rename,some_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hr hq)

end PPAC.Migration.Internal.PacketReaderReturnSyntax

import PPAC.Migration.Internal.PacketReaderRunStep

/-! Actual four-field reader evaluation existentially eliminates its genuine original state code. -/
namespace PPAC.Migration.Internal.PacketReaderEvalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def eval {m} (w B z o L v s a q : Fin m) : Formula m := .ex
  ((PacketReaderStateSyntax.code w.castSucc L.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)).conj
    (PacketReaderReturnCodedSyntax.run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc))

theorem eval_rename {m k} (w B z o L v s a q : Fin m) (ρ : Fin m → Fin k) :
    (eval w B z o L v s a q).rename ρ = eval (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ a) (ρ q) := by
  simp only [eval,Formula.rename,PacketReaderStateSyntax.code_rename,PacketReaderReturnCodedSyntax.run_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_eval {m} {Γ : Context m} (w B z o L v s a q n : Fin m)
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (hr : Derives Γ (PacketReaderReturnCodedSyntax.run w B z o n q)) :
    Derives Γ (eval w B z o L v s a q) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,PacketReaderStateSyntax.code_rename,PacketReaderReturnCodedSyntax.run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hc hr)

end PPAC.Migration.Internal.PacketReaderEvalSyntax

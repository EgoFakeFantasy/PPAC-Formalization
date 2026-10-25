import PPAC.Migration.Internal.PacketReaderHistoryUnique

/-! Actual single-cell input consumption and state-input projections, all witnesses internal. -/
namespace PPAC.Migration.Internal.PacketReaderConsumptionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def tail {m} (w l r : Fin m) : Formula m := .ex (PacketReaderInputSyntax.headRest w.castSucc l.castSucc (Fin.last m) r.castSucc)
def inputBody {m} (w n l : Fin m) : Formula (m+3) :=
  PacketReaderStateSyntax.code (old 3 w) (old 3 l) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n)
def input {m} (w n l : Fin m) : Formula m := existsMany 3 (inputBody w n l)
def existsInput {m} (w n : Fin m) : Formula m := .ex
  ((StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (input w.castSucc n.castSucc (Fin.last m)))
def inputAt {m} (w f i l : Fin m) : Formula m := .ex
  ((edge f.castSucc i.castSucc (Fin.last m)).conj (input w.castSucc (Fin.last m) l.castSucc))
def existsAt {m} (w f i : Fin m) : Formula m := .ex
  ((StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)))

theorem tail_rename {m k} (w l r : Fin m) (ρ : Fin m → Fin k) :
    (tail w l r).rename ρ = tail (ρ w) (ρ l) (ρ r) := by
  simp only [tail,Formula.rename,PacketReaderInputSyntax.headRest_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem inputBody_lift {m k} (w n l : Fin m) (ρ : Fin m → Fin k) :
    (inputBody w n l).rename (lift 3 ρ) = inputBody (ρ w) (ρ n) (ρ l) := by
  simp only [inputBody,PacketReaderStateSyntax.code_rename,lift_old,lift_slot]
theorem input_rename {m k} (w n l : Fin m) (ρ : Fin m → Fin k) :
    (input w n l).rename ρ = input (ρ w) (ρ n) (ρ l) := by
  simp only [input,existsMany_rename,inputBody_lift]
theorem existsInput_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (existsInput w n).rename ρ = existsInput (ρ w) (ρ n) := by
  simp only [existsInput,Formula.rename,StructuralListTraceSyntax.valid_rename,input_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem inputAt_rename {m k} (w f i l : Fin m) (ρ : Fin m → Fin k) :
    (inputAt w f i l).rename ρ = inputAt (ρ w) (ρ f) (ρ i) (ρ l) := by
  simp only [inputAt,Formula.rename,edge_rename,input_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem existsAt_rename {m k} (w f i : Fin m) (ρ : Fin m → Fin k) :
    (existsAt w f i).rename ρ = existsAt (ρ w) (ρ f) (ρ i) := by
  simp only [existsAt,Formula.rename,StructuralListTraceSyntax.valid_rename,inputAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_tail {m} {Γ : Context m} (w l r h : Fin m) (hh : Derives Γ (PacketReaderInputSyntax.headRest w l h r)) : Derives Γ (tail w l r) := by
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate,PacketReaderInputSyntax.headRest_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hh

theorem intro_input {m} {Γ : Context m} (w n l v s a : Fin m) (hc : Derives Γ (PacketReaderStateSyntax.code w l v s a n)) : Derives Γ (input w n l) := by
  apply HornBinderRules.intro_many 3 _ (SyntaxAtomSyntax.three v s a)
  exact of_eq (by simp only [inputBody,PacketReaderStateSyntax.code_rename,assign_old,assign_slot]; rfl) hc

theorem intro_at {m} {Γ : Context m} (w f i l n : Fin m) (he : Derives Γ (edge f i n)) (hi : Derives Γ (input w n l)) : Derives Γ (inputAt w f i l) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,edge_rename,input_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI he hi)

end PPAC.Migration.Internal.PacketReaderConsumptionSyntax

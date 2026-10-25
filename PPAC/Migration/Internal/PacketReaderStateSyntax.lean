import PPAC.Migration.Internal.PacketReaderInputOutcomes
import PPAC.Migration.Internal.SyntaxForestInjective

/-! Reader states use the original exact four-cell list encoding; no answer-defined program predicate or new proof kernel. -/
namespace PPAC.Migration.Internal.PacketReaderStateSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def fields {m} (l v s a : Fin m) : Fin 4 → Fin m := PacketVarintPrefixRecursionSyntax.four l v s a

theorem fields_map {m k} (l v s a : Fin m) (ρ : Fin m → Fin k) :
    (fun i => ρ (fields l v s a i)) = fields (ρ l) (ρ v) (ρ s) (ρ a) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun i => Fin.elim0 i) j) j) j) i

def code {m} (w l v s a n : Fin m) : Formula m :=
  (PacketReaderStepSyntax.state w l v s a).conj (SyntaxForestSyntax.forest 4 w (fields l v s a) n)
def existsCode {m} (w l v s a : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc l.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)))
def carrierBody {m} (w n : Fin m) : Formula (m+4) := code (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 n)
def carrier {m} (w n : Fin m) : Formula m := existsMany 4 (carrierBody w n)

theorem code_rename {m k} (w l v s a n : Fin m) (ρ : Fin m → Fin k) :
    (code w l v s a n).rename ρ = code (ρ w) (ρ l) (ρ v) (ρ s) (ρ a) (ρ n) := by
  simp only [code,Formula.rename,PacketReaderStepSyntax.state_rename,SyntaxForestSyntax.forest_rename,fields_map]
theorem existsCode_rename {m k} (w l v s a : Fin m) (ρ : Fin m → Fin k) :
    (existsCode w l v s a).rename ρ = existsCode (ρ w) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [existsCode,Formula.rename,code_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem carrierBody_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (carrierBody w n).rename (lift 4 ρ) = carrierBody (ρ w) (ρ n) := by
  simp only [carrierBody,code_rename,lift_old,lift_slot]
theorem carrier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (carrier w n).rename ρ = carrier (ρ w) (ρ n) := by
  simp only [carrier,existsMany_rename,carrierBody_lift]

theorem intro_carrier {m} {Γ : Context m} (w l v s a n : Fin m) (hc : Derives Γ (code w l v s a n)) : Derives Γ (carrier w n) := by
  apply HornBinderRules.intro_many 4 _ (fields l v s a)
  exact of_eq (by simp only [carrierBody,code_rename,assign_old,assign_slot]; rfl) hc

end PPAC.Migration.Internal.PacketReaderStateSyntax

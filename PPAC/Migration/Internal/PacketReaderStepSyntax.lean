import PPAC.Migration.Internal.PacketTokenCanonicalLaws
import PPAC.Migration.Internal.NaturalDifference

/-! Raw readTokens state and one-step formulas. No byte upper bound or positive-scale restriction is imposed. EOF is only a guard here; reversal and the complete run are separate obligations. -/
namespace PPAC.Migration.Internal.PacketReaderStepSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open PacketAffineSyntax (equation equation_rename)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open StructuralListSyntax (consCode consCode_rename)

def state {m} (w l v s a : Fin m) : Formula m :=
  (StructuralListTraceSyntax.valid w l).conj ((Formula.mem v w).conj ((Formula.mem s w).conj (StructuralListTraceSyntax.valid w a)))
def finish {m} (B z o b s : Fin m) : Formula m :=
  (Formula.mem b B).conj ((Formula.equal s o).disj (Formula.equal b z).neg)
def reject {m} (B z o b s : Fin m) : Formula m :=
  (Formula.mem b B).conj ((Formula.equal s o).neg.conj (.equal b z))
def more {m} (B b : Fin m) : Formula m := NaturalAdditionBounds.below B b
def eof {m} (z o v s : Fin m) : Formula m := (Formula.equal s o).conj (.equal v z)
def emission {m} (w b v s a c : Fin m) : Formula m := .ex
  ((equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m)).conj
    (consCode w.castSucc (Fin.last m) a.castSucc c.castSucc))
def continuation {m} (w B b v s y q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj
    ((sum w.castSucc B.castSucc (Fin.last m) b.castSucc).conj
      ((equation w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc).conj
        (product w.castSucc s.castSucc B.castSucc q.castSucc))))
def emitCase {m} (w B z o b x v s a r y q c : Fin m) : Formula m :=
  (finish B z o b s).conj ((Formula.equal r x).conj ((Formula.equal y z).conj
    ((Formula.equal q o).conj (emission w b v s a c))))
def continueCase {m} (w B b x v s a r y q c : Fin m) : Formula m :=
  (more B b).conj ((Formula.equal r x).conj ((Formula.equal c a).conj (continuation w B b v s y q)))
def step {m} (w B z o b x v s a r y q c : Fin m) : Formula m :=
  (emitCase w B z o b x v s a r y q c).disj (continueCase w B b x v s a r y q c)

theorem state_rename {m k} (w l v s a : Fin m) (ρ : Fin m → Fin k) :
    (state w l v s a).rename ρ = state (ρ w) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [state,Formula.rename,StructuralListTraceSyntax.valid_rename]

theorem finish_rename {m k} (B z o b s : Fin m) (ρ : Fin m → Fin k) :
    (finish B z o b s).rename ρ = finish (ρ B) (ρ z) (ρ o) (ρ b) (ρ s) := by
  simp only [finish,Formula.rename,Formula.neg]

theorem reject_rename {m k} (B z o b s : Fin m) (ρ : Fin m → Fin k) :
    (reject B z o b s).rename ρ = reject (ρ B) (ρ z) (ρ o) (ρ b) (ρ s) := by
  simp only [reject,Formula.rename,Formula.neg]

theorem more_rename {m k} (B b : Fin m) (ρ : Fin m → Fin k) :
    (more B b).rename ρ = more (ρ B) (ρ b) := by
  simp only [more,NaturalAdditionBounds.below_rename]

theorem eof_rename {m k} (z o v s : Fin m) (ρ : Fin m → Fin k) :
    (eof z o v s).rename ρ = eof (ρ z) (ρ o) (ρ v) (ρ s) := by
  simp only [eof,Formula.rename]

theorem emission_rename {m k} (w b v s a c : Fin m) (ρ : Fin m → Fin k) :
    (emission w b v s a c).rename ρ = emission (ρ w) (ρ b) (ρ v) (ρ s) (ρ a) (ρ c) := by
  simp only [emission,Formula.rename,equation_rename,consCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem continuation_rename {m k} (w B b v s y q : Fin m) (ρ : Fin m → Fin k) :
    (continuation w B b v s y q).rename ρ = continuation (ρ w) (ρ B) (ρ b) (ρ v) (ρ s) (ρ y) (ρ q) := by
  simp only [continuation,Formula.rename,sum_rename,equation_rename,product_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem emitCase_rename {m k} (w B z o b x v s a r y q c : Fin m) (ρ : Fin m → Fin k) :
    (emitCase w B z o b x v s a r y q c).rename ρ = emitCase (ρ w) (ρ B) (ρ z) (ρ o) (ρ b) (ρ x) (ρ v) (ρ s) (ρ a) (ρ r) (ρ y) (ρ q) (ρ c) := by
  simp only [emitCase,Formula.rename,finish_rename,emission_rename]

theorem continueCase_rename {m k} (w B b x v s a r y q c : Fin m) (ρ : Fin m → Fin k) :
    (continueCase w B b x v s a r y q c).rename ρ = continueCase (ρ w) (ρ B) (ρ b) (ρ x) (ρ v) (ρ s) (ρ a) (ρ r) (ρ y) (ρ q) (ρ c) := by
  simp only [continueCase,Formula.rename,more_rename,continuation_rename]

theorem step_rename {m k} (w B z o b x v s a r y q c : Fin m) (ρ : Fin m → Fin k) :
    (step w B z o b x v s a r y q c).rename ρ = step (ρ w) (ρ B) (ρ z) (ρ o) (ρ b) (ρ x) (ρ v) (ρ s) (ρ a) (ρ r) (ρ y) (ρ q) (ρ c) := by
  simp only [step,Formula.rename,emitCase_rename,continueCase_rename]

end PPAC.Migration.Internal.PacketReaderStepSyntax

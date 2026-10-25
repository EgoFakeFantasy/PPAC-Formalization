import PPAC.Migration.Internal.PacketReaderCodedExistence

/-! An independent internally finite history graph checks every adjacent coded state. It does not define a history by its final answer or assume a complete run. -/
namespace PPAC.Migration.Internal.PacketReaderHistorySyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def rowAt {m} (w B z o f i j n r : Fin m) : Formula m :=
  (successor j i).conj ((edge f i n).conj ((edge f j r).conj (PacketReaderCodedSyntax.step w B z o n r)))
def rowBody {m} (w B z o f i : Fin m) : Formula (m+3) :=
  rowAt (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 f) (old 3 i) (slot 3 0) (slot 3 1) (slot 3 2)
def row {m} (w B z o f i : Fin m) : Formula m := existsMany 3 (rowBody w B z o f i)
def links {m} (w B z o l f : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (row w.castSucc B.castSucc z.castSucc o.castSucc f.castSucc (Fin.last m)))
def history {m} (w B z o n r l d f : Fin m) : Formula m :=
  (PacketReaderStateSyntax.carrier w n).conj ((empty z).conj ((Formula.mem l w).conj ((successor d l).conj
    ((SequenceSyntax.sequence f d w).conj ((edge f z n).conj ((edge f l r).conj (links w B z o l f)))))))
def existsHistory {m} (w B z o n r l d : Fin m) : Formula m := .ex
  (history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc r.castSucc l.castSucc d.castSucc (Fin.last m))

theorem rowAt_rename {m k} (w B z o f i j n r : Fin m) (ρ : Fin m → Fin k) :
    (rowAt w B z o f i j n r).rename ρ = rowAt (ρ w) (ρ B) (ρ z) (ρ o) (ρ f) (ρ i) (ρ j) (ρ n) (ρ r) := by
  simp only [rowAt,Formula.rename,successor_rename,edge_rename,PacketReaderCodedSyntax.step_rename]

theorem rowBody_lift {m k} (w B z o f i : Fin m) (ρ : Fin m → Fin k) :
    (rowBody w B z o f i).rename (lift 3 ρ) = rowBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ f) (ρ i) := by
  simp only [rowBody,rowAt_rename,lift_old,lift_slot]

theorem row_rename {m k} (w B z o f i : Fin m) (ρ : Fin m → Fin k) :
    (row w B z o f i).rename ρ = row (ρ w) (ρ B) (ρ z) (ρ o) (ρ f) (ρ i) := by
  simp only [row,existsMany_rename,rowBody_lift]

theorem links_rename {m k} (w B z o l f : Fin m) (ρ : Fin m → Fin k) :
    (links w B z o l f).rename ρ = links (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ f) := by
  simp only [links,Formula.rename,row_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem history_rename {m k} (w B z o n r l d f : Fin m) (ρ : Fin m → Fin k) :
    (history w B z o n r l d f).rename ρ = history (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) (ρ f) := by
  simp only [history,Formula.rename,PacketReaderStateSyntax.carrier_rename,empty_rename,successor_rename,SequenceSyntax.sequence_rename,edge_rename,links_rename]

theorem existsHistory_rename {m k} (w B z o n r l d : Fin m) (ρ : Fin m → Fin k) :
    (existsHistory w B z o n r l d).rename ρ = existsHistory (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) := by
  simp only [existsHistory,Formula.rename,history_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_row {m} {Γ : Context m} (w B z o f i j n r : Fin m)
    (hs : Derives Γ (successor j i)) (hn : Derives Γ (edge f i n)) (hr : Derives Γ (edge f j r))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (row w B z o f i) := by
  apply HornBinderRules.intro_many 3 _ (SyntaxAtomSyntax.three j n r)
  exact of_eq (by simp only [rowBody,rowAt_rename,assign_old,assign_slot]; rfl) (.conjI hs (.conjI hn (.conjI hr ht)))

theorem links_at {m} {Γ : Context m} (w B z o l f i : Fin m) (hl : Derives Γ (links w B z o l f))
    (hi : Derives Γ (.mem i l)) : Derives Γ (row w B z o f i) := by
  have hp : Derives Γ ((Formula.mem i l).imp (row w B z o f i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hl)
  exact .impE hp hi

theorem empty_links {m} {Γ : Context m} (w B z o l f : Fin m) (hl : Derives Γ (empty l)) : Derives Γ (links w B z o l f) := by
  apply Derives.allI
  apply Derives.impI
  have hl1 := of_eq (empty_rename l Fin.castSucc) (under hl (Formula.mem (Fin.last m) l.castSucc))
  exact .botE (.impE (empty_at l.castSucc (Fin.last m) hl1) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketReaderHistorySyntax

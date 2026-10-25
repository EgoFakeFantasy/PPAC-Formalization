import PPAC.Migration.Internal.PacketReaderLengthBounds
import PPAC.Migration.Internal.PacketReaderHistoryAppend

/-! Independent actual stopping histories and exact-length prefixes; all witnesses stay in object quantifiers. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

def halted {m} (w B z o n r l d f : Fin m) : Formula m :=
  (history w B z o n r l d f).conj (PacketReaderCodedSyntax.existsNext w B z o r).neg

def stopBody {m} (w B z o n : Fin m) : Formula (m+4) :=
  halted (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def complete {m} (w B z o n : Fin m) : Formula m := existsMany 4 (stopBody w B z o n)

def prefixBody {m} (w B z o n i : Fin m) : Formula (m+3) :=
  history (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (slot 3 0) (old 3 i) (slot 3 1) (slot 3 2)

def prefixAt {m} (w B z o n i : Fin m) : Formula m := existsMany 3 (prefixBody w B z o n i)

def progress {m} (w B z o n i : Fin m) : Formula m := (complete w B z o n).disj (prefixAt w B z o n i)

def matrix : Formula 6 := progress 0 1 2 3 4 5

def params5 {m} (w B z o n : Fin m) : Fin 5 → Fin m := Fin.cases w (Fin.cases B (Fin.cases z (Fin.cases o (Fin.cases n (fun i => Fin.elim0 i)))))

def allProgress {m} (w B z o n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (progress w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)))

theorem halted_rename {m k} (w B z o n r l d f : Fin m) (ρ : Fin m → Fin k) :
    (halted w B z o n r l d f).rename ρ = halted (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ r) (ρ l) (ρ d) (ρ f) := by
  simp only [halted,Formula.rename,Formula.neg,history_rename,PacketReaderCodedSyntax.existsNext_rename]

theorem stopBody_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (stopBody w B z o n).rename (lift 4 ρ) = stopBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [stopBody,halted_rename,lift_old,lift_slot]

theorem complete_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (complete w B z o n).rename ρ = complete (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [complete,existsMany_rename,stopBody_lift]

theorem prefixBody_lift {m k} (w B z o n i : Fin m) (ρ : Fin m → Fin k) :
    (prefixBody w B z o n i).rename (lift 3 ρ) = prefixBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ i) := by
  simp only [prefixBody,history_rename,lift_old,lift_slot]

theorem prefixAt_rename {m k} (w B z o n i : Fin m) (ρ : Fin m → Fin k) :
    (prefixAt w B z o n i).rename ρ = prefixAt (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ i) := by
  simp only [prefixAt,existsMany_rename,prefixBody_lift]

theorem progress_rename {m k} (w B z o n i : Fin m) (ρ : Fin m → Fin k) :
    (progress w B z o n i).rename ρ = progress (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ i) := by
  simp only [progress,Formula.rename,complete_rename,prefixAt_rename]

theorem allProgress_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (allProgress w B z o n).rename ρ = allProgress (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [allProgress,Formula.rename,progress_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem params5_0 {m} (w B z o n : Fin m) : params5 w B z o n 0 = w := rfl

theorem params5_1 {m} (w B z o n : Fin m) : params5 w B z o n 1 = B := rfl

theorem params5_2 {m} (w B z o n : Fin m) : params5 w B z o n 2 = z := rfl

theorem params5_3 {m} (w B z o n : Fin m) : params5 w B z o n 3 = o := rfl

theorem params5_4 {m} (w B z o n : Fin m) : params5 w B z o n 4 = n := rfl

theorem matrix_pred {m} (ρ : Fin 5 → Fin m) (i : Fin m) :
    MinimalPredicates.pred matrix ρ i = progress (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) i := by
  have h0 : Fin.lastCases i ρ (0 : Fin 6) = ρ 0 := by
    change Fin.lastCases i ρ (0 : Fin 5).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases i ρ (1 : Fin 6) = ρ 1 := by
    change Fin.lastCases i ρ (1 : Fin 5).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases i ρ (2 : Fin 6) = ρ 2 := by
    change Fin.lastCases i ρ (2 : Fin 5).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases i ρ (3 : Fin 6) = ρ 3 := by
    change Fin.lastCases i ρ (3 : Fin 5).castSucc = ρ 3
    exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases i ρ (4 : Fin 6) = ρ 4 := by
    change Fin.lastCases i ρ (4 : Fin 5).castSucc = ρ 4
    exact Fin.lastCases_castSucc _
  have h5 : Fin.lastCases i ρ (5 : Fin 6) = i := by
    change Fin.lastCases i ρ (Fin.last 5) = i
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,progress_rename,h0,h1,h2,h3,h4,h5]

theorem intro_prefix {m} {Γ : Context m} (w B z o n r i d f : Fin m)
    (hh : Derives Γ (history w B z o n r i d f)) : Derives Γ (prefixAt w B z o n i) := by
  apply HornBinderRules.intro_many 3 _ (SyntaxAtomSyntax.three r d f)
  exact of_eq (by simp only [prefixBody,history_rename,assign_old,assign_slot]; rfl) hh

theorem intro_complete {m} {Γ : Context m} (w B z o n r l d f : Fin m)
    (hh : Derives Γ (halted w B z o n r l d f)) : Derives Γ (complete w B z o n) := by
  apply HornBinderRules.intro_many 4 _ (PacketReaderStateSyntax.fields r l d f)
  exact of_eq (by simp only [stopBody,halted_rename,assign_old,assign_slot]; rfl) hh

theorem prefix_index {m} {Γ : Context m} (w B z o n i j : Fin m) (he : Derives Γ (.equal i j))
    (hp : Derives Γ (prefixAt w B z o n i)) : Derives Γ (prefixAt w B z o n j) := by
  let P := prefixAt w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate i = prefixAt w B z o n i := by simp only [P,Formula.instantiate,prefixAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate j = prefixAt w B z o n j := by simp only [P,Formula.instantiate,prefixAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem all_at {m} {Γ : Context m} (w B z o n i : Fin m)
    (hh : Derives Γ (allProgress w B z o n)) (hi : Derives Γ (.mem i w)) : Derives Γ (progress w B z o n i) := by
  have hp : Derives Γ ((Formula.mem i w).imp (progress w B z o n i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,progress_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hh)
  exact .impE hp hi

end PPAC.Migration.Internal.PacketReaderStoppingSyntax

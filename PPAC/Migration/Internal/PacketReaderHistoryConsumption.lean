import PPAC.Migration.Internal.PacketReaderHistoryInput

/-! Every real internal step index consumes one actual original Cons cell between the unique projected inputs. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryConsumption
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def consumptionBody {m} (w f i : Fin m) : Formula (m+3) :=
  (successor (slot 3 0) (old 3 i)).conj ((inputAt (old 3 w) (old 3 f) (old 3 i) (slot 3 1)).conj
    ((inputAt (old 3 w) (old 3 f) (slot 3 0) (slot 3 2)).conj (tail (old 3 w) (slot 3 1) (slot 3 2))))
def consumesAt {m} (w f i : Fin m) : Formula m := existsMany 3 (consumptionBody w f i)
def allSteps {m} (w f l : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (consumesAt w.castSucc f.castSucc (Fin.last m)))
theorem consumptionBody_lift {m k} (w f i : Fin m) (ρ : Fin m → Fin k) :
    (consumptionBody w f i).rename (lift 3 ρ) = consumptionBody (ρ w) (ρ f) (ρ i) := by
  simp only [consumptionBody,Formula.rename,successor_rename,inputAt_rename,tail_rename,lift_old,lift_slot]
theorem consumesAt_rename {m k} (w f i : Fin m) (ρ : Fin m → Fin k) :
    (consumesAt w f i).rename ρ = consumesAt (ρ w) (ρ f) (ρ i) := by
  simp only [consumesAt,existsMany_rename,consumptionBody_lift]
theorem allSteps_rename {m k} (w f l : Fin m) (ρ : Fin m → Fin k) :
    (allSteps w f l).rename ρ = allSteps (ρ w) (ρ f) (ρ l) := by
  simp only [allSteps,Formula.rename,consumesAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_consumption {m} {Γ : Context m} (w f i j L K : Fin m) (hs : Derives Γ (successor j i))
    (hL : Derives Γ (inputAt w f i L)) (hK : Derives Γ (inputAt w f j K)) (ht : Derives Γ (tail w L K)) :
    Derives Γ (consumesAt w f i) := by
  apply HornBinderRules.intro_many 3 _ (SyntaxAtomSyntax.three j L K)
  exact of_eq (by simp only [consumptionBody,Formula.rename,successor_rename,inputAt_rename,tail_rename,assign_old,assign_slot]; rfl) (.conjI hs (.conjI hL (.conjI hK ht)))

theorem row_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o f d i j L K : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SequenceSyntax.sequence f d w))
    (hs : Derives Γ (successor j i)) (hr : Derives Γ (row w B z o f i))
    (hL : Derives Γ (inputAt w f i L)) (hK : Derives Γ (inputAt w f j K)) : Derives Γ (tail w L K) := by
  let R := rowBody w B z o f i
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hf3 := of_eq (SequenceSyntax.sequence_rename f d w (old 3)) (HornBinderRules.under_body 3 hf R)
  have hs3 := of_eq (successor_rename j i (old 3)) (HornBinderRules.under_body 3 hs R)
  have hL3 := of_eq (inputAt_rename w f i L (old 3)) (HornBinderRules.under_body 3 hL R)
  have hK3 := of_eq (inputAt_rename w f j K (old 3)) (HornBinderRules.under_body 3 hK R)
  have hj := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hR) hs3
  have hedge := StructuralListTraceOrder.edge_input_subst _ _ _ _ hj (.conjL (.conjR (.conjR hR)))
  have hiL := Derives.impE (.conjL (PacketReaderHistoryInput.at_edge hZ3 _ _ _ _ _ _ hf3 (.conjL (.conjR hR)))) hL3
  have hiK := Derives.impE (.conjL (PacketReaderHistoryInput.at_edge hZ3 _ _ _ _ _ _ hf3 hedge)) hK3
  exact of_eq (tail_rename w L K (old 3)).symm
    (PacketReaderCodedConsumption.at_inputs hZ3 _ _ _ _ _ _ _ _ hw3 hiL hiK (.conjR (.conjR (.conjR hR))))

theorem adjacent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i j L K : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) (hi : Derives Γ (.mem i l))
    (hs : Derives Γ (successor j i)) (hL : Derives Γ (inputAt w f i L)) (hK : Derives Γ (inputAt w f j K)) : Derives Γ (tail w L K) :=
  row_tail hZ w B z o f d i j L K hw (PacketReaderHistoryLaws.sequence_at _ _ _ _ _ _ _ _ _ hh) hs
    (PacketReaderHistoryLaws.row_at _ _ _ _ _ _ _ _ _ _ hh hi) hL hK

theorem adjacent_strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i j L K : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) (hi : Derives Γ (.mem i l))
    (hs : Derives Γ (successor j i)) (hL : Derives Γ (inputAt w f i L)) (hK : Derives Γ (inputAt w f j K)) : Derives Γ (.mem K L) :=
  PacketReaderRawConsumption.tail_strict hZ w L K hw (adjacent hZ w B z o n r l d f i j L K hw hh hi hs hL hK)

theorem every_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) (hi : Derives Γ (.mem i l)) :
    Derives Γ (consumesAt w f i) := by
  let R := rowBody w B z o f i
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ (PacketReaderHistoryLaws.row_at _ _ _ _ _ _ _ _ _ _ hh hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hh3 := of_eq (history_rename w B z o n r l d f (old 3)) (HornBinderRules.under_body 3 hh R)
  have hs3 := Derives.conjL hR
  have hE0 := Derives.conjL (.conjR hR)
  have hE1 := Derives.conjL (.conjR (.conjR hR))
  have hStep := Derives.conjR (.conjR (.conjR hR))
  have hL := PacketReaderHistoryInput.exists_on_edge hZ3 _ _ _ _ _ _ _ _ _ _ _ hw3 hh3 hE0
  let X := (StructuralListTraceSyntax.valid (old 3 w).castSucc (Fin.last (m+3))).conj
    (inputAt (old 3 w).castSucc (old 3 f).castSucc (old 3 i).castSucc (Fin.last (m+3)))
  let Ξ := Context.add X (Context.image Formula.raise Δ)
  apply Derives.exE (p := X) hL
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 X
  have hw4 := of_eq (omega_rename (old 3 w) Fin.castSucc) (under hw3 X)
  have hh4 := of_eq (history_rename (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (old 3 r) (old 3 l) (old 3 d) (old 3 f) Fin.castSucc) (under hh3 X)
  have hE14 := of_eq (edge_rename (old 3 f) (slot 3 0) (slot 3 2) Fin.castSucc) (under hE1 X)
  have hK := PacketReaderHistoryInput.exists_on_edge hZ4 _ _ _ _ _ _ _ _ _ _ _ hw4 hh4 hE14
  let Y := (StructuralListTraceSyntax.valid (old 3 w).castSucc.castSucc (Fin.last (m+4))).conj
    (inputAt (old 3 w).castSucc.castSucc (old 3 f).castSucc.castSucc (slot 3 0).castSucc.castSucc (Fin.last (m+4)))
  let Θ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) hK
  have hY : Derives Θ Y := .hyp (Or.inl rfl)
  have hZ5 := ZFContext.under hZ4 Y
  have hw5 := of_eq (omega_rename (old 3 w).castSucc Fin.castSucc) (under hw4 Y)
  have hs4 := of_eq (successor_rename (slot 3 0) (old 3 i) Fin.castSucc) (under hs3 X)
  have hs5 := of_eq (successor_rename (slot 3 0).castSucc (old 3 i).castSucc Fin.castSucc) (under hs4 Y)
  have hE04 := of_eq (edge_rename (old 3 f) (old 3 i) (slot 3 1) Fin.castSucc) (under hE0 X)
  have hE05 := of_eq (edge_rename (old 3 f).castSucc (old 3 i).castSucc (slot 3 1).castSucc Fin.castSucc) (under hE04 Y)
  have hE15 := of_eq (edge_rename (old 3 f).castSucc (slot 3 0).castSucc (slot 3 2).castSucc Fin.castSucc) (under hE14 Y)
  have hL5 := of_eq (inputAt_rename (old 3 w).castSucc (old 3 f).castSucc (old 3 i).castSucc (Fin.last (m+3)) Fin.castSucc) (under (.conjR hX) Y)
  have hSt4 := of_eq (PacketReaderCodedSyntax.step_rename (old 3 w) (old 3 B) (old 3 z) (old 3 o) (slot 3 1) (slot 3 2) Fin.castSucc) (under hStep X)
  have hSt5 := of_eq (PacketReaderCodedSyntax.step_rename (old 3 w).castSucc (old 3 B).castSucc (old 3 z).castSucc (old 3 o).castSucc (slot 3 1).castSucc (slot 3 2).castSucc Fin.castSucc) (under hSt4 Y)
  have hsq3 := PacketReaderHistoryLaws.sequence_at _ _ _ _ _ _ _ _ _ hh3
  have hsq4 := of_eq (SequenceSyntax.sequence_rename (old 3 f) (old 3 d) (old 3 w) Fin.castSucc) (under hsq3 X)
  have hsq5 := of_eq (SequenceSyntax.sequence_rename (old 3 f).castSucc (old 3 d).castSucc (old 3 w).castSucc Fin.castSucc) (under hsq4 Y)
  have hin0 := Derives.impE (.conjL (PacketReaderHistoryInput.at_edge hZ5 _ _ _ _ _ _ hsq5 hE05)) hL5
  have hin1 := Derives.impE (.conjL (PacketReaderHistoryInput.at_edge hZ5 _ _ _ _ _ _ hsq5 hE15)) (.conjR hY)
  have htail := PacketReaderCodedConsumption.at_inputs hZ5 _ _ _ _ _ _ _ _ hw5 hin0 hin1 hSt5
  have hout := intro_consumption _ _ _ _ _ _ hs5 hL5 (.conjR hY) htail
  simpa only [Formula.raise,consumesAt_rename] using hout

theorem all_steps {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) : Derives Γ (allSteps w f l) := by
  apply Derives.allI
  apply Derives.impI
  let H := Formula.mem (Fin.last m) l.castSucc
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh H)
  exact every_step hZ1 _ _ _ _ _ _ _ _ _ _ hw1 hh1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderHistoryConsumption

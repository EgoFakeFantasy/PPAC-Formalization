import PPAC.Migration.Internal.HornClosedTraceProperties

/-! Actual ten-rule Packet closure, uniform unfolding, exact affine dispatch, and positive transitions. -/
namespace PPAC.Migration.Internal.PacketTraceCore
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation

def value {m} (w V : Fin m) : Formula m := HornClosedTraceValueSyntax.value ObjectPacket.rules w V

theorem value_rename {m j} (w V : Fin m) (ρ : Fin m → Fin j) :
    (value w V).rename ρ = value (ρ w) (ρ V) := HornClosedTraceValueSyntax.value_rename ObjectPacket.rules w V ρ

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) :
    Derives Γ (HornClosedTraceValueSyntax.existsValue ObjectPacket.rules w) := HornClosedTraceValue.exists_value ObjectPacket.rules hZ w

theorem member_iff {m} {Γ : Context m} (w V r : Fin m) (hv : Derives Γ (value w V)) :
    Derives Γ ((Formula.mem r V).iff (PacketTraceSyntax.condition w r)) := HornClosedTraceValue.member_iff ObjectPacket.rules w V r hv

theorem closed {m} {Γ : Context m} (w V : Fin m) (hv : Derives Γ (value w V)) :
    Derives Γ (PacketTraceSyntax.closed w V) := HornClosedTraceValueClosed.closed ObjectPacket.rules w V hv

theorem unfold_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w V)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (PacketTraceSyntax.step w r V)) :=
  HornClosedTraceProperties.unfold_iff ObjectPacket.rules hZ w V r hw hv

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (HornClosedTraceSystemSyntax.existsSystem ObjectPacket.rules w) :=
  HornClosedTraceProperties.exists_system ObjectPacket.rules hZ w hw

theorem affine_condition_iff_outcomes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (value w V)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff
      ((PacketAffineApplicationSyntax.baseOutcome wide w B r).disj (PacketAffineApplicationSyntax.stepOutcome wide w B V r))) :=
  SyntaxTypeLocalTransfer.iff_trans (unfold_iff hZ w V r hw hv) (PacketAffineDispatch.step_iff_outcomes hZ wide w B d t n r V hw hB hr)

theorem intro_entry {m} {Γ : Context m} (wide : Bool) (w V d t n r : Fin m)
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) (hm : Derives Γ (.mem r V)) :
    Derives Γ (PacketHornAffineSyntax.entry wide w V d t n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PacketHornAffineSyntax.row_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hm)

theorem base_accept {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hb : Derives Γ (PacketAffineApplicationSyntax.baseOutcome wide w B r)) : Derives Γ (PacketTraceSyntax.condition w r) := by
  let P := value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (exists_value hZ w)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have hb1 := of_eq (PacketAffineApplicationSyntax.baseOutcome_rename wide w B r Fin.castSucc) (under hb P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ha := PacketAffineApplication.base_backward hZ1 wide w.castSucc B.castSucc r.castSucc (Fin.last m) hw1 hB1 hb1
  have hs := HornStepSyntax.rule_intro ObjectPacket.rules (PacketAffineRuleData.baseRule wide)
    (PacketAffineDispatchData.base_member wide) w.castSucc r.castSucc (Fin.last m) ha
  exact of_eq (PacketTraceSyntax.condition_rename w r Fin.castSucc).symm
    (.impE (.conjR (unfold_iff hZ1 w.castSucc (Fin.last m) r.castSucc hw1 hP)) hs)

theorem step_accept {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t a s n q r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hq : Derives Γ (PacketHornAffineSyntax.row wide w d t a q)) (hc : Derives Γ (PacketTraceSyntax.condition w q))
    (hs : Derives Γ (successor s t)) (hn : Derives Γ (NaturalAdditionSyntax.sum w a B n))
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d s n r)) : Derives Γ (PacketTraceSyntax.condition w r) := by
  let P := value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (exists_value hZ w)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have hq1 := of_eq (PacketHornAffineSyntax.row_rename wide w d t a q Fin.castSucc) (under hq P)
  have hc1 := of_eq (PacketTraceSyntax.condition_rename w q Fin.castSucc) (under hc P)
  have hs1 := of_eq (successor_rename s t Fin.castSucc) (under hs P)
  have hn1 := of_eq (NaturalAdditionSyntax.sum_rename w a B n Fin.castSucc) (under hn P)
  have hr1 := of_eq (PacketHornAffineSyntax.row_rename wide w d s n r Fin.castSucc) (under hr P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hm := Derives.impE (.conjR (member_iff w.castSucc (Fin.last m) q.castSucc hP)) hc1
  have he := intro_entry wide w.castSucc (Fin.last m) d.castSucc t.castSucc a.castSucc q.castSucc hq1 hm
  have hS := PacketHornAffineSyntax.intro_step wide w.castSucc B.castSucc (Fin.last m) d.castSucc t.castSucc a.castSucc r.castSucc
    s.castSucc n.castSucc hs1 hn1 hr1 he
  have ho := PacketAffineApplicationSyntax.intro_step wide w.castSucc B.castSucc (Fin.last m) r.castSucc d.castSucc t.castSucc a.castSucc hS
  have ha := PacketAffineApplication.step_backward hZ1 wide w.castSucc B.castSucc r.castSucc (Fin.last m) hw1 hB1 ho
  have hStep := HornStepSyntax.rule_intro ObjectPacket.rules (PacketAffineRuleData.stepRule wide)
    (PacketAffineDispatchData.step_member wide) w.castSucc r.castSucc (Fin.last m) ha
  exact of_eq (PacketTraceSyntax.condition_rename w r Fin.castSucc).symm
    (.impE (.conjR (unfold_iff hZ1 w.castSucc (Fin.last m) r.castSucc hw1 hP)) hStep)

end PPAC.Migration.Internal.PacketTraceCore

import PPAC.Migration.Internal.PacketAffineAcceptedSyntax

/-! Exact relational Packet affine arithmetic after discharging the internal IH and all trace witnesses. -/
namespace PPAC.Migration.Internal.PacketAffineAccepted
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketAffineAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (PacketAffineSyntax.affine w B d t n)) := by
  let P := PacketTraceCore.value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketTraceCore.exists_value hZ w)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have hr1 := of_eq (PacketHornAffineSyntax.row_rename wide w d t n r Fin.castSucc) (under hr P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hM := PacketTraceCore.member_iff w.castSucc (Fin.last m) r.castSucc hP
  have hA := PacketAffineInduction.membership_iff (ZFContext.under hZ P) wide w.castSucc B.castSucc (Fin.last m)
    d.castSucc t.castSucc n.castSucc r.castSucc hw1 hB1 hP hr1
  have hC := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hM) (.conjL hM)) hA
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, PacketTraceSyntax.condition_rename,
    PacketAffineSyntax.affine_rename]) hC

theorem accepted_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ ((accepted wide w d t n).iff (PacketAffineSyntax.affine w B d t n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := accepted wide w d t n
    let P := (PacketHornAffineSyntax.row wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m)).conj
      (PacketTraceSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := P) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ H) P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) P)
    have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under (add hB H) P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    exact of_eq (PacketAffineSyntax.affine_rename w B d t n Fin.castSucc).symm
      (.impE (.conjL (condition_iff hZ1 wide w.castSucc B.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hB1 (.conjL hP))) (.conjR hP))
  · apply Derives.impI
    let H := PacketAffineSyntax.affine w B d t n
    let ΓA := Context.add H Γ
    have hA : Derives ΓA H := .hyp (Or.inl rfl)
    have hZA := ZFContext.add hZ H
    have hwA := add hw H
    have hd := PacketAffineCore.digit_natural hZA w B d t n hwA hA
    have ht := PacketAffineCore.tail_guard w B d t n hA
    have hn := PacketAffineCore.output_guard w B d t n hA
    have hi := SyntaxForestSyntax.intro_inputs 3 w (SyntaxAtomSyntax.three d t n)
      (Fin.cases hd (Fin.cases ht (Fin.cases hn (fun i => Fin.elim0 i))))
    have he := SyntaxConstructors.exists_constructor hZA 3 (PacketAffineRuleData.relation wide) w (SyntaxAtomSyntax.three d t n) hwA hi
    let P := (Formula.mem (Fin.last m) w.castSucc).conj (PacketHornAffineSyntax.row wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise ΓA)
    apply Derives.exE (p := P) he
    have hZ1 := ZFContext.under hZA P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under hwA P)
    have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under (add hB H) P)
    have hA1 := of_eq (PacketAffineSyntax.affine_rename w B d t n Fin.castSucc) (under hA P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hC := Derives.impE (.conjR (condition_iff hZ1 wide w.castSucc B.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hB1 (.conjR hP))) hA1
    exact of_eq (accepted_rename wide w d t n Fin.castSucc).symm
      (intro_accepted wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m) (.conjR hP) hC)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 3)) (HornBinderRules.under_many 3 hB)
  exact accepted_iff (HornBinderRules.zf_many 3 hZ) wide (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3

theorem all_root_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allRootLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let R := PacketHornAffineSyntax.row wide (old 4 w : Fin (m+4)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 4)) (HornBinderRules.under_body 4 hB R)
  exact condition_iff (HornBinderRules.zf_body 4 hZ R) wide (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
    hw4 hB4 (.hyp (Or.inl rfl))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let P := PacketAffineLiteralSyntax.frame wide w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hZ1 := ZFContext.under hZ P
  have hL := all_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP)
  have hR := all_root_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hP)
  have hSys : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hP (.conjI hL hR)
  have ho : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hSys
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm ho

end PPAC.Migration.Internal.PacketAffineAccepted

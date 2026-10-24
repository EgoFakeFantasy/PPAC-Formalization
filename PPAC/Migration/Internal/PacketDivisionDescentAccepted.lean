import PPAC.Migration.Internal.PacketDivisionDescentSyntax

/-! Actual relational Packet acceptance inherits precise descent and stopping laws. -/
namespace PPAC.Migration.Internal.PacketDivisionDescentAccepted
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketDivisionDescentSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem affine_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) : Derives Γ (properties w B d q n) := by
  apply Derives.conjI
  · exact PacketDivisionDescentCore.quotient_below hZ wide w B d q n hw hB ha
  · apply Derives.conjI
    · apply Derives.impI
      exact PacketDivisionDescentCore.quotient_strict (ZFContext.add hZ _) wide w B d q n
        (add hw _) (add hB _) (add ha _) (.hyp (Or.inl rfl))
    · exact .conjI (PacketDivisionDescentCore.terminal_iff hZ w B d q n hw ha)
        (PacketDivisionDescentCore.zero_output hZ wide w B d q n hw hB ha)

theorem affine_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) : Derives Γ (branch B d q n) := by
  have ht := PacketDivisionDescentCore.terminal_iff hZ w B d q n hw ha
  apply SourcePropositional.by_cases (empty q) (branch B d q n)
  · have hz : Derives (Context.add (empty q) Γ) (empty q) := .hyp (Or.inl rfl)
    exact .disjL (.conjI hz (.conjI (.impE (add (.conjL ht) _) hz)
      (PacketDivisionDescentCore.terminal_digit w B d q n (add ha _) hz)))
  · have hz : Derives (Context.add (empty q).neg Γ) (empty q).neg := .hyp (Or.inl rfl)
    have hb := add (.conjR (PacketDivisionDescentCore.quotient_bounds hZ wide w B d q n hw hB ha)) (empty q).neg
    have hn : Derives (Context.add (empty q).neg Γ) (Formula.mem n B).neg := by
      apply Derives.impI
      exact .impE (add hz _) (.impE (add (add (.conjR ht) _) _) (.hyp (Or.inl rfl)))
    exact .disjR (.conjI (.impE hb hz) (.conjI hz hn))

theorem accepted_properties {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted wide w d q n)) : Derives Γ ((properties w B d q n).conj (branch B d q n)) := by
  have hA := Derives.impE (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d q n hw hB)) ha
  exact .conjI (affine_properties hZ wide w B d q n hw hB hA) (affine_branch hZ wide w B d q n hw hB hA)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)) :
    Derives Γ (allLaw wide w B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := PacketAffineAcceptedSyntax.accepted wide (old 3 w : Fin (m+3)) (slot 3 0) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw H)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B (old 3)) (HornBinderRules.under_body 3 hB H)
  exact accepted_properties (HornBinderRules.zf_body 3 hZ H) wide (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 (.hyp (Or.inl rfl))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem wide w) := by
  let F := PacketAffineLiteralSyntax.frame wide w.castSucc (Fin.last m)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (SyntaxNumerals.exists_numeral hZ (PacketAffineRuleData.radix wide) w hw)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ F
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have hV : Derives Δ (PacketDivisionValueSyntax.system wide w.castSucc (Fin.last m)) := .conjI hF
    (.conjI (PacketDivisionValue.all_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hF))
      (PacketDivisionValue.all_accepted_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hF)))
  have hs : Derives Δ (system wide w.castSucc (Fin.last m)) := .conjI hV
    (all_law hZ1 wide w.castSucc (Fin.last m) hw1 (.conjR hF))
  have he : Derives Δ (existsSystem wide w.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, system_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hs
  exact of_eq (existsSystem_rename wide w Fin.castSucc).symm he

end PPAC.Migration.Internal.PacketDivisionDescentAccepted

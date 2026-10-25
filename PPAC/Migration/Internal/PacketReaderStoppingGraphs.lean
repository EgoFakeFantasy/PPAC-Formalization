import PPAC.Migration.Internal.PacketReaderStoppingUnique

/-! Stopped histories have identical original domains, edges, and actual graph sets. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingGraphs
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax GraphPointwiseSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem member_domain {m} {Γ : Context m} (i d e : Fin m) (he : Derives Γ (.equal d e))
    (hi : Derives Γ (.mem i d)) : Derives Γ (.mem i e) := by
  let P := Formula.mem i.castSucc (Fin.last m)
  have h0 : P.instantiate d = Formula.mem i d := by simp only [P,Formula.instantiate,Formula.rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate e = Formula.mem i e := by simp only [P,Formula.instantiate,Formula.rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hi))

theorem edge_transfer {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g i a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g))
    (hd : Derives Γ (.equal d e)) (ha : Derives Γ (edge f i a)) : Derives Γ (edge g i a) := by
  have hiD := GraphProperties.domain_of_edge f d i a (ZFContext.arithmetic hZ).base.extensionality (.conjL (sequence_at _ _ _ _ _ _ _ _ _ (.conjL hf))) ha
  have hiE := member_domain i d e hd hiD
  have hex := GraphProperties.output_exists g e i (.conjL (sequence_at _ _ _ _ _ _ _ _ _ (.conjL hg))) hiE
  let R := edge g.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 : Derives Δ (.mem B.castSucc w.castSucc) := under hB R
  have hf1 := of_eq (halted_rename w B z o n r l d f Fin.castSucc) (under hf R)
  have hg1 := of_eq (halted_rename w B z o n t k e g Fin.castSucc) (under hg R)
  have ha1 := of_eq (edge_rename f i a Fin.castSucc) (under ha R)
  have he := PacketReaderHistoryUnique.common_values hZ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw1 hB1 (.conjL hf1) (.conjL hg1) ha1 hR
  simpa only [Formula.raise,edge_rename] using edge_subst_output _ _ _ _ (eq_symm he) hR

theorem included {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g))
    (hd : Derives Γ (.equal d e)) : Derives Γ (edgeIncluded f g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := edge (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add H (raisedContext 2 Γ)
  have lift2 {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := add (HornBinderRules.under_many 2 hp) H
  have hZ2 := ZFContext.add (HornBinderRules.zf_many 2 hZ) H
  have hw2 := of_eq (omega_rename w (old 2)) (lift2 hw)
  have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := lift2 hB
  have hf2 := of_eq (halted_rename w B z o n r l d f (old 2)) (lift2 hf)
  have hg2 := of_eq (halted_rename w B z o n t k e g (old 2)) (lift2 hg)
  have hd2 : Derives Δ (.equal (old 2 d) (old 2 e)) := lift2 hd
  exact edge_transfer hZ2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw2 hB2 hf2 hg2 hd2 (.hyp (Or.inl rfl))

theorem graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g)) : Derives Γ (.equal f g) := by
  have hd := PacketReaderStoppingUnique.domains hZ w B z o n r t l d k e f g hw hB hf hg
  have hfg := included hZ w B z o n r t l d k e f g hw hB hf hg hd
  have hgf := included hZ w B z o n t r k e l d g f hw hB hg hf (eq_symm hd)
  exact GraphPointwiseEntries.equal_of_edges f g d e (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (.conjL (sequence_at _ _ _ _ _ _ _ _ _ (.conjL hf)))) (.conjL (.conjL (sequence_at _ _ _ _ _ _ _ _ _ (.conjL hg)))) (.conjI hfg hgf)

end PPAC.Migration.Internal.PacketReaderStoppingGraphs

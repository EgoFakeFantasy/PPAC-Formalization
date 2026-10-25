import PPAC.Migration.Internal.PacketReaderStoppingExistence
import PPAC.Migration.Internal.PacketReaderHistoryUnique

/-! Original common-index agreement forbids any genuine history from continuing beyond a stopped one. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem next_source {m} {Γ : Context m} (w B z o n r : Fin m) (he : Derives Γ (.equal n r))
    (hn : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o n)) : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o r) := by
  let P := PacketReaderCodedSyntax.existsNext w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)
  have h0 : P.instantiate n = PacketReaderCodedSyntax.existsNext w B z o n := by simp only [P,Formula.instantiate,PacketReaderCodedSyntax.existsNext_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate r = PacketReaderCodedSyntax.existsNext w B z o r := by simp only [P,Formula.instantiate,PacketReaderCodedSyntax.existsNext_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hn))

theorem intro_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) :
    Derives Γ (PacketReaderCodedSyntax.existsNext w B z o n) := by
  have hr := Derives.conjR (PacketReaderCodedNormalize.domain hZ w B z o n r hw ht)
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,PacketReaderCodedSyntax.step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hr ht)

theorem no_longer_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (history w B z o n t k e g))
    (hl : Derives Γ (.mem l k)) : Derives Γ .bot := by
  have hRow := row_at _ _ _ _ _ _ _ _ _ _ hg hl
  let R := rowBody w B z o g l
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hRow
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 : Derives Δ (.mem (old 3 B) (old 3 w)) := HornBinderRules.under_body 3 hB R
  have hf3 := of_eq (halted_rename w B z o n r l d f (old 3)) (HornBinderRules.under_body 3 hf R)
  have hg3 := of_eq (history_rename w B z o n t k e g (old 3)) (HornBinderRules.under_body 3 hg R)
  have he := PacketReaderHistoryUnique.common_values hZ3 (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (old 3 r) (old 3 t) (old 3 l) (old 3 d) (old 3 k) (old 3 e) (old 3 f) (old 3 g) (old 3 l) (old 3 r) (slot 3 1) hw3 hB3 (.conjL hf3) hg3 (last_at _ _ _ _ _ _ _ _ _ (.conjL hf3)) (.conjL (.conjR hR))
  have hn := intro_next hZ3 _ _ _ _ _ _ hw3 (.conjR (.conjR (.conjR hR)))
  exact .impE (.conjR hf3) (next_source _ _ _ _ _ _ (eq_symm he) hn)

theorem lengths {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g)) : Derives Γ (.equal l k) := by
  have hc := NaturalOrderBasic.compare hZ w l k hw (length_at _ _ _ _ _ _ _ _ _ (.conjL hf)) (length_at _ _ _ _ _ _ _ _ _ (.conjL hg))
  apply Derives.disjE hc
  · exact .hyp (Or.inl rfl)
  · let C := (Formula.mem l k).disj (.mem k l)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · let H := Formula.mem l k
      exact .botE (no_longer_history (ZFContext.add (ZFContext.add hZ C) H) w B z o n r t l d k e f g (add (add hw C) H) (add (add hB C) H) (add (add hf C) H) (add (add (.conjL hg) C) H) (.hyp (Or.inl rfl)))
    · let H := Formula.mem k l
      exact .botE (no_longer_history (ZFContext.add (ZFContext.add hZ C) H) w B z o n t r k e l d g f (add (add hw C) H) (add (add hB C) H) (add (add hg C) H) (add (add (.conjL hf) C) H) (.hyp (Or.inl rfl)))

theorem endpoints {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g)) : Derives Γ (.equal r t) := by
  have he := lengths hZ w B z o n r t l d k e f g hw hB hf hg
  have ht := StructuralListTraceOrder.edge_input_subst g k l t (eq_symm he) (last_at _ _ _ _ _ _ _ _ _ (.conjL hg))
  exact PacketReaderHistoryUnique.common_values hZ w B z o n r t l d k e f g l r t hw hB (.conjL hf) (.conjL hg) (last_at _ _ _ _ _ _ _ _ _ (.conjL hf)) ht

theorem domains {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d k e f g : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (halted w B z o n r l d f)) (hg : Derives Γ (halted w B z o n t k e g)) : Derives Γ (.equal d e) := by
  have he := lengths hZ w B z o n r t l d k e f g hw hB hf hg
  have hd := NaturalAdditionTransport.successor_input_subst d l k he (successor_at _ _ _ _ _ _ _ _ _ (.conjL hf))
  exact OmegaUniversal.successor_unique d e k (ZFContext.arithmetic hZ).base.extensionality hd (successor_at _ _ _ _ _ _ _ _ _ (.conjL hg))

end PPAC.Migration.Internal.PacketReaderStoppingUnique

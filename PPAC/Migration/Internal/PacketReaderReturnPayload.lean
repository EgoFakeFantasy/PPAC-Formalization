import PPAC.Migration.Internal.PacketReaderReturnSyntax

/-! Original zero/one-cell encodings construct actual None/Some codes, with naturality, uniqueness and disjointness. -/
namespace PPAC.Migration.Internal.PacketReaderReturnPayload
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem none_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.ex ((Formula.mem (Fin.last m) w.castSucc).conj (none w.castSucc (Fin.last m)))) := by
  exact SyntaxForests.exists_forest hZ 0 w (fun i => Fin.elim0 i) hw (.eqRefl w)

theorem some_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) :
    Derives Γ (.ex ((Formula.mem (Fin.last m) w.castSucc).conj (some w.castSucc r.castSucc (Fin.last m)))) := by
  exact SyntaxForests.exists_forest hZ 1 w (fun _ => r) hw (.conjI hr (.eqRefl w))

theorem none_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (none w p)) (hq : Derives Γ (none w q)) : Derives Γ (.equal p q) :=
  StructuralNil.unique hZ w p q hw hp hq

theorem some_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r p q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (some w r p)) (hq : Derives Γ (some w r q)) : Derives Γ (.equal p q) :=
  SyntaxForests.unique hZ 1 w (fun _ => r) p q hw hp hq

theorem some_payload_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (some w r q)) (hs : Derives Γ (some w s q)) : Derives Γ (.equal r s) :=
  SyntaxForestInjective.input_eq hZ 1 w (fun _ => r) (fun _ => s) q 0 hw hr hs

theorem none_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (none w q)) : Derives Γ (.mem q w) :=
  SyntaxForests.range hZ 0 w (fun i => Fin.elim0 i) q hw hq

theorem some_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (some w r q)) : Derives Γ (.mem q w) :=
  SyntaxForests.range hZ 1 w (fun _ => r) q hw hq

theorem payload_subst {m} {Γ : Context m} (w r s q : Fin m) (he : Derives Γ (.equal r s))
    (hr : Derives Γ (some w r q)) : Derives Γ (some w s q) := by
  let P := some w.castSucc (Fin.last m) q.castSucc
  have h0 : P.instantiate r = some w r q := by simp only [P,Formula.instantiate,some_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate s = some w s q := by simp only [P,Formula.instantiate,some_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (none w q)) (hs : Derives Γ (some w r q)) : Derives Γ .bot := by
  let R := (Formula.mem r.castSucc w.castSucc).conj ((StructuralListSyntax.nilCode w.castSucc (Fin.last m)).conj
    (StructuralListSyntax.consCode w.castSucc r.castSucc (Fin.last m) q.castSucc))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hs
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hn1 := of_eq (none_rename w q Fin.castSucc) (under hn R)
  exact StructuralConsUnique.disjoint (ZFContext.under hZ R) _ _ _ _ hw1 hn1 (.conjR (.conjR hR))

end PPAC.Migration.Internal.PacketReaderReturnPayload

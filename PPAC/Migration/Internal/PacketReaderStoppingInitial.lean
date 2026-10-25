import PPAC.Migration.Internal.PacketReaderStoppingSyntax
import PPAC.Migration.Internal.PacketReaderHistoryBase

/-! Original zero-history construction supplies the genuine empty-index progress base. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingInitial
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem carrier_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) : Derives Γ (.mem n w) := by
  let R := PacketReaderStateSyntax.carrierBody w n
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  exact PacketReaderStateCode.range hZ4 _ _ _ _ _ _ hw4 hR

theorem prefix_of_exists_history {m} {Γ : Context m} (w B z o n r i d : Fin m)
    (hh : Derives Γ (existsHistory w B z o n r i d)) : Derives Γ (prefixAt w B z o n i) := by
  let R := history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc r.castSucc i.castSucc d.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hh
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,prefixAt_rename] using intro_prefix _ _ _ _ _ _ _ _ _ hR

theorem zero_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n)) :
    Derives Γ (prefixAt w B z o n z) := by
  have hn := carrier_natural hZ w n hw hc
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hex := Derives.impE (OmegaSyntax.step_at w z (.conjL hw)) hzN
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) z.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have hc1 := of_eq (PacketReaderStateSyntax.carrier_rename w n Fin.castSucc) (under hc R)
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn R
  have hzero := PacketReaderHistoryBase.exists_zero hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m) hw1 hz1 (.conjR hR) hn1 hc1
  simpa only [Formula.raise,prefixAt_rename] using prefix_of_exists_history _ _ _ _ _ _ _ _ hzero

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n i : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (PacketReaderStateSyntax.carrier w n))
    (hi : Derives Γ (empty i)) : Derives Γ (progress w B z o n i) := by
  have he := OmegaUniversal.empty_unique z i (ZFContext.arithmetic hZ).base.extensionality hz hi
  exact .disjR (prefix_index w B z o n z i he (zero_prefix hZ w B z o n hw hz hc))

end PPAC.Migration.Internal.PacketReaderStoppingInitial

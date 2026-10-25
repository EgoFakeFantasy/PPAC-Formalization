import PPAC.Migration.Internal.PacketReaderTerminalZero

/-! The original initialized empty-input equation is proved on every actual output candidate through a real zero-step history. -/
namespace PPAC.Migration.Internal.PacketReaderInitEmpty
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInitSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem seeded_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hL : Derives Γ (StructuralListSyntax.nilCode w L)) :
    Derives Γ ((seeded w B z o L q).iff (PacketReaderReturnSyntax.some w o q)) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderInitSeed.exists_seed hZ w z o L hw hz ho (StructuralListTraceBase.valid_nil hZ w L hw hL))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho R)
  have hL1 := of_eq (StructuralListSyntax.nilCode_rename w L Fin.castSucc) (under hL R)
  have he : Derives Δ (PacketReaderInputSyntax.eofSuccess w.castSucc z.castSucc o.castSucc L.castSucc z.castSucc o.castSucc o.castSucc) :=
    .conjI (.conjL (.conjR hR)) (.conjI hL1 (.conjI (.eqRefl o.castSucc) (.eqRefl z.castSucc)))
  have hNorm := PacketReaderInitSeeded.at_seed hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m) q.castSucc hw1 (.conjR hR)
  have hBase := PacketReaderTerminalZero.at_terminal hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc z.castSucc o.castSucc o.castSucc (Fin.last m) q.castSucc hw1 (under hB R) hz1 ho1 (.conjR hR) (.disjL he)
  have hNil := StructuralNil.at_unit hZ1 _ _ _ hw1 hz1 ho1
  have hRev := StructuralListReverseNil.nil_pair hZ1 _ _ _ hw1 hNil hNil
  have hVal := PacketReaderFixedReturn.at_success hZ1 w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc z.castSucc o.castSucc o.castSucc o.castSucc q.castSucc hw1 he hRev
  simpa only [Formula.raise,Formula.rename,seeded_rename,PacketReaderReturnSyntax.some_rename] using
    StructuralListSuffixArithmetic.iff_trans (StructuralListSuffixArithmetic.iff_trans hNorm hBase) hVal

theorem output_subst {m} {Γ : Context m} (w L p q : Fin m) (he : Derives Γ (.equal p q))
    (hp : Derives Γ (parse w L p)) : Derives Γ (parse w L q) := by
  let P := parse w.castSucc L.castSucc (Fin.last m)
  have h0 : P.instantiate p = parse w L p := by simp only [P,Formula.instantiate,parse_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = parse w L q := by simp only [P,Formula.instantiate,parse_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem empty_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L u q : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (StructuralListSyntax.nilCode w L))
    (hu : Derives Γ (StructuralListSyntax.nilCode w u)) (hp : Derives Γ (parse w L q)) : Derives Γ (PacketReaderReturnSyntax.some w u q) := by
  let R := parseBody w L q
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hL3 := of_eq (StructuralListSyntax.nilCode_rename w L (old 3)) (HornBinderRules.under_body 3 hL R)
  have hu3 := of_eq (StructuralListSyntax.nilCode_rename w u (old 3)) (HornBinderRules.under_body 3 hu R)
  have hB := SyntaxNumerals.range hZ3 128 (old 3 w) (slot 3 0) hw3 (.conjL hR)
  have hz := Derives.conjL (.conjR hR)
  have ho := Derives.conjL (.conjR (.conjR hR))
  have hNorm := seeded_empty hZ3 (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 L) (old 3 q) hw3 hB hz ho hL3
  have hSome := Derives.impE (.conjL hNorm) (.conjR (.conjR (.conjR hR)))
  have hNil := StructuralNil.at_unit hZ3 _ _ _ hw3 hz ho
  have heq := StructuralNil.unique hZ3 _ _ _ hw3 hNil hu3
  exact of_eq (PacketReaderReturnSyntax.some_rename w u q (old 3)).symm (PacketReaderReturnPayload.payload_subst _ _ _ _ heq hSome)

theorem at_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L u q : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (StructuralListSyntax.nilCode w L)) (hu : Derives Γ (StructuralListSyntax.nilCode w u)) :
    Derives Γ ((parse w L q).iff (PacketReaderReturnSyntax.some w u q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact empty_forward (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hL _) (add hu _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let H := PacketReaderReturnSyntax.some w u q
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (parse w.castSucc L.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    have hv := StructuralListTraceBase.valid_nil hZ w L hw hL
    apply Derives.exE (p := R) (PacketReaderInitParser.exists_return (ZFContext.add hZ H) _ _ (add hw H) (add hv H))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hL1 := of_eq (StructuralListSyntax.nilCode_rename w L Fin.castSucc) (under (add hL H) R)
    have hu1 := of_eq (StructuralListSyntax.nilCode_rename w u Fin.castSucc) (under (add hu H) R)
    have hs1 := of_eq (PacketReaderReturnSyntax.some_rename w u q Fin.castSucc) (under (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H) R)
    have hSome := empty_forward hZ1 _ _ _ _ hw1 hL1 hu1 (.conjR hR)
    have heq := PacketReaderReturnPayload.some_unique hZ1 _ _ _ _ hw1 hSome hs1
    simpa only [Formula.raise,parse_rename] using output_subst _ _ _ _ heq (.conjR hR)

end PPAC.Migration.Internal.PacketReaderInitEmpty

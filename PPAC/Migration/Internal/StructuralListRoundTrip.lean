import PPAC.Migration.Internal.StructuralListRoundTripSyntax

/-! 任意内部序列的实际唯一编码，以及任意有效原码的解码再编码原码恢复。 -/
namespace PPAC.Migration.Internal.StructuralListRoundTrip
open Source SourceAlgebra SourceLogic OmegaSyntax SequenceSyntax StructuralListEncodeSyntax StructuralListFieldGraphSyntax StructuralListRoundTripSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListTraceSyntax (valid)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_unique_encoding {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f r : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f r w)) (hr : Derives Γ (.mem r w)) :
    Derives Γ (encodingFiber w f r) := by
  have he := StructuralListEncodeExistence.exists_encoding hZ w f r hw hf hr
  let E := encoding w.castSucc f.castSucc r.castSucc (Fin.last m)
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((encoding w.castSucc.castSucc f.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let C := encoding w.castSucc.castSucc f.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 C
    have hOld : Derives Δ (encoding w.castSucc.castSucc f.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [E, Formula.raise, encoding_rename] using under hE C
    exact StructuralListCodeGraph.encoded_unique (ZFContext.under hZ1 C) _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout := intro_fiber _ _ _ _ hE hu
  simpa only [Formula.raise, encodingFiber_rename] using hout

theorem decode_then_encode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l f a : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hf : Derives Γ (fields w n l f))
    (ha : Derives Γ (encoding w f l a)) : Derives Γ (.equal a n) :=
  StructuralListCodeGraph.same_fields_unique hZ w l a n f hw (.conjR (.conjL ha)) hl (.conjR ha) hf

theorem reencode_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (roundTrip w n) := by
  have hd := StructuralListFieldDecode.exists_decoded hZ w n hw hv
  let D := decodedBody w n
  let Ξ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListFieldDecode.eliminate_decoded w n _ hd
  have hZ2 : ZFContext.Evidence Ξ := ZFContext.under_two hZ D
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have ha := StructuralListEncodeExistence.exists_encoding hZ2 _ _ _ hw2 (.conjL (.conjR hD)) (.conjL (.conjL hD))
  let A := encoding w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add A (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex A) at ha
  apply Derives.exE (p := A) ha
  have hZ3 : ZFContext.Evidence Δ := ZFContext.under hZ2 A
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw2 A
  have hD3 : Derives Δ (((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj
      (hasLength w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc)).conj
      (fields w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)) := by
    simpa only [D, decodedBody, Formula.raise, Formula.rename, hasLength_rename, fields_rename] using under hD A
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have heq := decode_then_encode hZ3 _ _ _ _ _ hw3 (.conjR (.conjL hD3)) (.conjR hD3) hA
  have hout := intro_roundTrip _ _ _ _ _ (.conjR (.conjL hD3)) (.conjR hD3) hA heq
  simpa only [Formula.raise, roundTrip_rename] using hout
end PPAC.Migration.Internal.StructuralListRoundTrip

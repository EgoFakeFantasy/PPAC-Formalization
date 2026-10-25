import PPAC.Migration.Internal.PacketReaderLengthSyntax

/-! Actual remaining lengths are natural, unique, and exist at every internal history-domain index. -/
namespace PPAC.Migration.Internal.PacketReaderLengthAt
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketReaderLengthSyntax PacketReaderConsumptionSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem natural {m} {Γ : Context m} (w f i a : Fin m) (ha : Derives Γ (lengthAt w f i a)) : Derives Γ (.mem a w) := by
  let R := (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).conj (hasLength w.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ha
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact StructuralListLengthBasic.length_member _ _ _ (.conjR hR)

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d i a : Fin m)
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (ha : Derives Γ (lengthAt w f i a)) : Derives Γ (.mem i d) := by
  let R := (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).conj (hasLength w.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ha
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  let K := (edge f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (input w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add K (Context.image Formula.raise Δ)
  apply Derives.exE (p := K) (.conjL hR)
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) K
  have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under hf R)
  have hf2 := of_eq (SequenceSyntax.sequence_rename f.castSucc d.castSucc w.castSucc Fin.castSucc) (under hf1 K)
  exact GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjL hf2) (.conjL hK)

theorem exists_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (hi : Derives Γ (.mem i d)) : Derives Γ (existsLengthAt w f i) := by
  let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderHistoryInput.exists_at hZ w B z o n r l d f i hw hh hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hex := StructuralListLengthBasic.exists_length w.castSucc (Fin.last m) (.conjL hR)
  let T := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hex
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hInput := of_eq (inputAt_rename w.castSucc f.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) T)
  have hLen := intro_length _ _ _ _ _ hInput (.conjR hT)
  have hout : Derives Ξ (existsLengthAt w.castSucc.castSucc f.castSucc.castSucc i.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,lengthAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hT) hLen)
  simpa only [Formula.raise,existsLengthAt_rename] using hout

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d i a b : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SequenceSyntax.sequence f d w))
    (ha : Derives Γ (lengthAt w f i a)) (hb : Derives Γ (lengthAt w f i b)) : Derives Γ (.equal a b) := by
  let R := (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).conj (hasLength w.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) ha
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb1 := of_eq (lengthAt_rename w f i b Fin.castSucc) (under hb R)
  let T := (inputAt w.castSucc.castSucc f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (hasLength w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hb1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under hf R)
  have hf2 := of_eq (SequenceSyntax.sequence_rename f.castSucc d.castSucc w.castSucc Fin.castSucc) (under hf1 T)
  have hI := of_eq (inputAt_rename w.castSucc f.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) T)
  have hA := of_eq (hasLength_rename w.castSucc (Fin.last m) a.castSucc Fin.castSucc) (under (.conjR hR) T)
  have he := PacketReaderHistoryInput.unique_at hZ2 _ _ _ _ _ _ hw2 hf2 hI (.conjL hT)
  have hAc := StructuralListLengthBasic.code_subst _ _ _ _ he hA
  exact StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 hAc (.conjR hT)

end PPAC.Migration.Internal.PacketReaderLengthAt

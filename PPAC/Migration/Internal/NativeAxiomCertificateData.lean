import PPAC.Migration.Internal.ObjectProofTreeEquation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomEncode

/-! 原nativeZF的准确无Choice证书数据及完整schema；本模块的宿主数据对应不替代对象公理测试。 -/
namespace PPAC.Migration.Internal.NativeAxiomCertificateData
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open FirstOrder.FormalSystem.ProofT
attribute [local implicit_reducible] SetTheory.signature
open SetTheory.Definitional

inductive Certificate where
  | extensionality | emptySet | pairing | union | powerSet | infinity | foundation
  | separation {parameterCount : Nat} (schema : Project.UnarySchema parameterCount)
  | collection {parameterCount : Nat} (schema : Project.BinarySchema parameterCount)

def projectSentence : Certificate → Project.Sentence
  | .extensionality => Axioms.extensionality
  | .emptySet => Axioms.emptySet
  | .pairing => Axioms.pairing
  | .union => Axioms.union
  | .powerSet => Axioms.powerSet
  | .infinity => Axioms.infinity
  | .foundation => Axioms.foundation
  | .separation schema => Axioms.Schema.separation schema
  | .collection schema => Axioms.Schema.collection schema

def sentence (c : Certificate) : FirstOrder.Sentence ℒ := Project.fo_sentence (projectSentence c)

theorem project_sound (c : Certificate) : SetTheory.ZF (projectSentence c) := by
  cases c with
  | extensionality => exact .extensionality
  | emptySet => exact .emptySet
  | pairing => exact .pairing
  | union => exact .union
  | powerSet => exact .powerSet
  | infinity => exact .infinity
  | foundation => exact .foundation
  | separation schema => exact .separation schema
  | collection schema => exact .collection schema

theorem sound (c : Certificate) : nativeZF (sentence c) := ⟨projectSentence c,project_sound c,rfl⟩

theorem complete {p : FirstOrder.Sentence ℒ} (hp : nativeZF p) : ∃ c : Certificate, sentence c = p := by
  obtain ⟨s,hs,hp⟩ := hp
  cases hs with
  | extensionality => exact ⟨.extensionality,hp.symm⟩
  | emptySet => exact ⟨.emptySet,hp.symm⟩
  | pairing => exact ⟨.pairing,hp.symm⟩
  | union => exact ⟨.union,hp.symm⟩
  | powerSet => exact ⟨.powerSet,hp.symm⟩
  | infinity => exact ⟨.infinity,hp.symm⟩
  | foundation => exact ⟨.foundation,hp.symm⟩
  | separation schema => exact ⟨.separation schema,hp.symm⟩
  | collection schema => exact ⟨.collection schema,hp.symm⟩

def toZFC : Certificate → ZFC.ZFCAxiomCertificate
  | .extensionality => .extensionality
  | .emptySet => .emptySet
  | .pairing => .pairing
  | .union => .union
  | .powerSet => .powerSet
  | .infinity => .infinity
  | .foundation => .foundation
  | .separation schema => .separation schema
  | .collection schema => .collection schema

def narrow : ZFC.ZFCAxiomCertificate → Option Certificate
  | .extensionality => some .extensionality
  | .emptySet => some .emptySet
  | .pairing => some .pairing
  | .union => some .union
  | .powerSet => some .powerSet
  | .infinity => some .infinity
  | .foundation => some .foundation
  | .choice => none
  | .separation schema => some (.separation schema)
  | .collection schema => some (.collection schema)

theorem narrow_toZFC (c : Certificate) : narrow (toZFC c) = some c := by cases c <;> rfl

def encode (c : Certificate) : NatPacket.Tree := ZFC.zfc_base_axiom_encode (toZFC c)

def decode (t : NatPacket.Tree) : Option Certificate := (ZFC.zfc_base_axiom_decode t).bind narrow

theorem decode_encode (c : Certificate) : decode (encode c) = some c := by
  simp only [decode, encode, ZFC.zfc_base_axiom_roundtrip, Option.bind_some, narrow_toZFC]

theorem choice_packet_rejected : decode (NatPacket.leaf 7) = none := rfl

abbrev TargetCertificate := Sum Certificate (Fin 3)

def extraSentence (kind : Fin 3) : FirstOrder.Sentence ℒ :=
  match kind.val with
  | 0 => PP
  | 1 => ACwo
  | _ => notAC

def targetSentence : TargetCertificate → FirstOrder.Sentence ℒ
  | .inl c => sentence c
  | .inr k => extraSentence k

theorem target_sound (c : TargetCertificate) : targetTheory (targetSentence c) := by
  cases c with
  | inl c => exact Or.inl (sound c)
  | inr k =>
    rcases k with ⟨k,hk⟩
    have hc : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases hc with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem target_complete {p : FirstOrder.Sentence ℒ} (hp : targetTheory p) :
    ∃ c : TargetCertificate, targetSentence c = p := by
  rcases hp with h | rfl | rfl | rfl
  · obtain ⟨c,rfl⟩ := complete h
    exact ⟨.inl c,rfl⟩
  · exact ⟨.inr 0,rfl⟩
  · exact ⟨.inr 1,rfl⟩
  · exact ⟨.inr 2,rfl⟩

def fixedFormula (kind : Fin 10) : FirstOrder.Sentence ℒ :=
  match kind.val with
  | 0 => sentence .extensionality
  | 1 => sentence .emptySet
  | 2 => sentence .pairing
  | 3 => sentence .union
  | 4 => sentence .powerSet
  | 5 => sentence .infinity
  | 6 => sentence .foundation
  | 7 => PP
  | 8 => ACwo
  | _ => notAC

def fixedTag (kind : Fin 10) : Nat := if kind.val < 7 then kind.val else kind.val+3

theorem fixedTag_lt (kind : Fin 10) : fixedTag kind < 128 := by
  unfold fixedTag
  split <;> omega

theorem fixed_target_sound (kind : Fin 10) : targetTheory (fixedFormula kind) := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (sound .extensionality)
  · exact Or.inl (sound .emptySet)
  · exact Or.inl (sound .pairing)
  · exact Or.inl (sound .union)
  · exact Or.inl (sound .powerSet)
  · exact Or.inl (sound .infinity)
  · exact Or.inl (sound .foundation)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

def targetEncode : TargetCertificate → NatPacket.Tree
  | .inl c => encode c
  | .inr k => NatPacket.leaf (10+k.val)

def targetDecode (t : NatPacket.Tree) : Option TargetCertificate :=
  match t with
  | .node 10 [] => some (.inr 0)
  | .node 11 [] => some (.inr 1)
  | .node 12 [] => some (.inr 2)
  | _ => (decode t).map Sum.inl

theorem targetDecode_as_base (c : Certificate) :
    targetDecode (encode c) = (decode (encode c)).map Sum.inl := by cases c <;> rfl

theorem target_decode_encode (c : TargetCertificate) : targetDecode (targetEncode c) = some c := by
  cases c with
  | inl c =>
    rw [targetEncode, targetDecode_as_base, decode_encode]
    rfl
  | inr k =>
    rcases k with ⟨k,hk⟩
    have hc : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases hc with rfl | rfl | rfl <;> rfl

theorem target_choice_packet_rejected : targetDecode (NatPacket.leaf 7) = none := rfl

def fixedCertificate (kind : Fin 10) : TargetCertificate :=
  match kind.val with
  | 0 => .inl .extensionality
  | 1 => .inl .emptySet
  | 2 => .inl .pairing
  | 3 => .inl .union
  | 4 => .inl .powerSet
  | 5 => .inl .infinity
  | 6 => .inl .foundation
  | 7 => .inr 0
  | 8 => .inr 1
  | _ => .inr 2

theorem fixedTag_injective {i j : Fin 10} (h : fixedTag i = fixedTag j) : i = j := by
  apply Fin.ext
  by_cases hi : i.val < 7 <;> by_cases hj : j.val < 7 <;> simp only [fixedTag, hi, hj, if_true, if_false] at h <;> omega

theorem fixed_sentence_exact (kind : Fin 10) : targetSentence (fixedCertificate kind) = fixedFormula kind := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fixed_encode_exact (kind : Fin 10) : targetEncode (fixedCertificate kind) = NatPacket.leaf (fixedTag kind) := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem fixed_decode_exact (kind : Fin 10) : targetDecode (NatPacket.leaf (fixedTag kind)) = some (fixedCertificate kind) := by
  rw [← fixed_encode_exact kind]
  exact target_decode_encode (fixedCertificate kind)

theorem fixedTag_ne_choice (kind : Fin 10) : fixedTag kind ≠ 7 := by
  unfold fixedTag
  split <;> omega

end PPAC.Migration.Internal.NativeAxiomCertificateData

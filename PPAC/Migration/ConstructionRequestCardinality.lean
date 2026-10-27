/- Pinned CompleteRounds ProbeData/MergerData/Request.data_cardinal_le.
SAME source request set, internal omega and ALL prescription rows. Actual
injective re-encoding pads partial starts; native function-space injection
and existing infinite product/union bounds use exactly mu^omega=mu.
Consumer: CompleteRounds enumeration; no object Choice premise. -/
import PPAC.Migration.ConstructionRequestPadding

namespace PPAC.Migration.ConstructionRequestCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Small)
open ConstructionRequestCarrier (Carrier Element WellFormed)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ConstructionRequestPadding (Padding)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem function_space_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu X Y F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hX : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) X w)
    (hY : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y mu)
    (hF : (Project.FirstOrderSemantics.reduct M).IsFunctionSpace (KuratowskiZF.interpretation hM) F X Y) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) F mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨B,E,T,hB,hE,hT,hPower⟩ := hpow
  obtain ⟨domainMap,hDomainMap⟩ := hX
  obtain ⟨baseMap,hBaseMap⟩ := hY
  obtain ⟨omegaToE,hOmegaToE⟩ := hE.2
  obtain ⟨muToB,hMuToB⟩ := hB.2
  obtain ⟨toE,hToE⟩ := ZF.exists_compositionInjection hZF I hDomainMap hOmegaToE.1
  obtain ⟨toB,hToB⟩ := ZF.exists_compositionInjection hZF I hBaseMap hMuToB.1
  obtain ⟨z,_,hz⟩ := hw.1.1
  obtain ⟨wToMu,hWToMu⟩ := hmu.2
  obtain ⟨v,hv,_⟩ := hWToMu.1.2.2 z hz
  obtain ⟨defaultValue,hDefault,_⟩ := hMuToB.1.1.2.2 v hv
  obtain ⟨extension,hExtension⟩ := ZF.exists_functionSpaceExtensionInjection hZF I hF hT hToE hToB hDefault
  obtain ⟨toMu,hToMu⟩ := hPower.2.symm hZF I
  exact ZF.exists_compositionInjection hZF I hExtension hToMu.1

def Encoding (WW Options zero one q code : M.Carrier .set) : Prop :=
  (∃ a b node, ProbeCode zero a b node q ∧ code = q) ∨
  ∃ n P f, MergerCode one n P q ∧ MapsTo WW Options f ∧ Padding WW zero one P f ∧ MergerCode one n f code


def encoding {m : Nat} (WW Options zero one q code : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.conj (ConstructionRequestSchedule.probeCode zero.succ.succ.succ (2 :
  Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)) q.succ.succ.succ) (Project.Formula.extensionalEq (.bound
  code.succ.succ.succ) (.bound q.succ.succ.succ)))))) (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  q.succ.succ.succ) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+3))
  WW.succ.succ.succ Options.succ.succ.succ)) (.conj (ConstructionRequestPadding.padding WW.succ.succ.succ
  zero.succ.succ.succ one.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))
  code.succ.succ.succ))))))))

theorem encoding_freeClosed {m : Nat} (WW Options zero one q code : Fin m) :
    (encoding WW Options zero one q code).FreeClosed := by
  simp -implicitDefEqProofs [encoding,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,Project.Formula.extensionalEq,ConstructionRequestPadding.padding_freeClosed]

theorem encoding_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (WW Options zero one q code : Fin m) :
    Project.Formula.satisfies env (encoding WW Options zero one q code) ↔ Encoding (env.bound WW) (env.bound Options) (env.bound zero) (env.bound one) (env.bound q) (env.bound code) := by
  simp only [encoding,Encoding,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_disj_iff,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionRequestPadding.padding_semantics hM]
  rfl


theorem merger_fields {w D mul e zero one Requests q n P : M.Carrier .set}
    (hne : zero ≠ one) (hR : Carrier w D mul e zero one Requests)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q Requests) (hc : MergerCode one n P q) :
    (Project.FirstOrderSemantics.reduct M).mem n w ∧ WellFormed n D P ∧ ConstructionMergerRelations.Prescription n D P := by
  rcases (hR q).mp hq with ⟨a,b,node,hProbe,_⟩ | ⟨m,Q,hMerger,hm,_,hWell,hPres,_⟩
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hProbe hc)
  · obtain ⟨eqn,eqP⟩ := ConstructionRequestSchedule.merger_code_injective hMerger hc
    subst m; subst Q
    exact ⟨hm,hWell,hPres⟩

theorem encoding_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {WW Options zero one q x y : M.Carrier .set} (hne : zero ≠ one)
    (hx : Encoding WW Options zero one q x) (hy : Encoding WW Options zero one q y) : x = y := by
  rcases hx with ⟨a,b,node,hp,hx⟩ | ⟨n,P,f,hp,hf,hPad,hx⟩ <;>
    rcases hy with ⟨a',b',node',hp',hy⟩ | ⟨n',P',g,hp',hg,hPad',hy⟩
  · exact hx.trans hy.symm
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hp hp')
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hp' hp)
  · obtain ⟨eqn,eqP⟩ := ConstructionRequestSchedule.merger_code_injective hp hp'
    subst n'; subst P'
    have eqf := ConstructionRequestPadding.padding_unique hM hf hg hPad hPad'
    subst g
    exact ConstructionRequestSchedule.merger_code_unique hM hx hy

theorem encoding_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e WW Options zero one Requests x y code : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hne : zero ≠ one) (hR : Carrier w D mul e zero one Requests)
    (hWW : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) WW w w)
    (hxR : (Project.FirstOrderSemantics.reduct M).mem x Requests)
    (hyR : (Project.FirstOrderSemantics.reduct M).mem y Requests)
    (hx : Encoding WW Options zero one x code) (hy : Encoding WW Options zero one y code) : x = y := by
  rcases hx with ⟨a,b,node,hp,hx⟩ | ⟨n,P,f,hp,hf,hPad,hx⟩ <;>
    rcases hy with ⟨a',b',node',hp',hy⟩ | ⟨n',Q,g,hp',hg,hPad',hy⟩
  · exact hx.symm.trans hy
  · subst code
    exact False.elim (ConstructionRequestSchedule.code_disjoint hne hp hy)
  · subst code
    exact False.elim (ConstructionRequestSchedule.code_disjoint hne hp' hx)
  · obtain ⟨hn,hWellP,_⟩ := merger_fields hne hR hxR hp
    obtain ⟨hm,hWellQ,_⟩ := merger_fields hne hR hyR hp'
    obtain ⟨eqn,eqf⟩ := ConstructionRequestSchedule.merger_code_injective hx hy
    subst n'; subst g
    have eqP := ConstructionRequestPadding.padding_injective hM hw hn hm hne hWW hWellP hWellQ hPad hPad'
    subst Q
    exact ConstructionRequestSchedule.merger_code_unique hM hp hp'

theorem data_cardinal_le (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one Requests mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hne : zero ≠ one) (hR : Carrier w D mul e zero one Requests) : Small Requests mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hDsmall := (ForcingSupportSize.native_small hM D mu).mp hD
  have hSelf := (Structure.Equinumerous.refl hZF I w)
  obtain ⟨wId,hWId⟩ := hSelf
  have hWsmall : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual I w w := ⟨wId,hWId.1⟩
  have hWInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal I w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l I hZF hw,hWsmall⟩
  obtain ⟨WW,hWW⟩ := ZF.exists_cartesianProduct hZF I w w
  have hWWsmall := ExistingCardinalBounds.infinite_product_l I hZF hw hWInfinite hWsmall hWsmall hWW
  obtain ⟨DD,hDD⟩ := ZF.exists_cartesianProduct hZF I D D
  have hDDsmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hDsmall hDsmall hDD
  obtain ⟨B,hB⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) DD w
  have hBsmall := ExistingCardinalBounds.infinite_union_two_l I hZF hw hmu hDDsmall hmu.2 hB
  obtain ⟨Options,hOptions⟩ := ZF.exists_cartesianProduct hZF I B B
  have hOptionsSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hBsmall hBsmall hOptions
  obtain ⟨FP,hFP⟩ := ZF.exists_functionSpace hZF I w D
  have hFPSmall := function_space_bound hM hw hmu hpow hWsmall hDsmall hFP
  obtain ⟨A,hA⟩ := ZF.exists_cartesianProduct hZF I D FP
  have hASmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hDsmall hFPSmall hA
  obtain ⟨PB,hPB⟩ := ZF.exists_cartesianProduct hZF I D A
  have hPBSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hDsmall hASmall hPB
  obtain ⟨Probes,hProbes⟩ := ZF.exists_cartesianProduct hZF I w PB
  have hProbesSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hmu.2 hPBSmall hProbes
  obtain ⟨FM,hFM⟩ := ZF.exists_functionSpace hZF I WW Options
  have hFMSmall := function_space_bound hM hw hmu hpow hWWsmall hOptionsSmall hFM
  obtain ⟨MB,hMB⟩ := ZF.exists_cartesianProduct hZF I w FM
  have hMBSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hmu.2 hFMSmall hMB
  obtain ⟨Mergers,hMergers⟩ := ZF.exists_cartesianProduct hZF I w MB
  have hMergersSmall := ExistingCardinalBounds.infinite_product_l I hZF hw hmu hmu.2 hMBSmall hMergers
  obtain ⟨Raw,hRaw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Probes Mergers
  have hRawSmall := ExistingCardinalBounds.infinite_union_two_l I hZF hw hmu hProbesSmall hMergersSmall hRaw
  have hTotal (q : M.Carrier .set) (hq : (Project.FirstOrderSemantics.reduct M).mem q Requests) :
      ∃ code, Encoding WW Options zero one q code := by
    rcases (hR q).mp hq with ⟨a,b,node,hc,_⟩ | ⟨n,P,hc,_,_,hWell,hPres,_⟩
    · exact ⟨q,Or.inl ⟨a,b,node,hc,rfl⟩⟩
    · obtain ⟨f,hf,hPad⟩ := ConstructionRequestPadding.exists_padding hM hWell hPres hDD
        (fun ab hab => (hB ab).mpr (Or.inl hab)) hOptions
        ((hB zero).mpr (Or.inr hz)) ((hB one).mpr (Or.inr ho))
      obtain ⟨t,ht⟩ := I.total n f
      obtain ⟨code,hcode⟩ := I.total one t
      exact ⟨code,Or.inr ⟨n,P,f,hc,hf,hPad,t,hcode,ht⟩⟩
  have hRange (q code : M.Carrier .set) (hq : (Project.FirstOrderSemantics.reduct M).mem q Requests)
      (h : Encoding WW Options zero one q code) : (Project.FirstOrderSemantics.reduct M).mem code Raw := by
    rcases h with ⟨a,b,node,hc,he⟩ | ⟨n,P,f,hc,hf,_,hcode⟩
    · subst code
      rcases (hR q).mp hq with ⟨a',b',node',hc',hb,_,hPath⟩ | ⟨n,P,hMerger,_⟩
      · obtain ⟨eqA,eqB,eqNode⟩ := ConstructionRequestSchedule.probe_code_injective hc hc'
        subst a'; subst b'; subst node'
        obtain ⟨t,s,hq,ht,hs⟩ := hc
        have hnode := (hFP node).mpr ((ForcingSupportSize.native_mapsTo hM w D node).mp hPath.1)
        have hsA := (hA s).mpr ⟨b,hb,node,hnode,hs⟩
        have htPB := (hPB t).mpr ⟨a,hPath.2.1,s,hsA,ht⟩
        exact (hRaw q).mpr (Or.inl ((hProbes q).mpr ⟨zero,hz,t,htPB,hq⟩))
      · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hc hMerger)
    · have hn := (merger_fields hne hR hq hc).1
      obtain ⟨t,hcode,ht⟩ := hcode
      have hfm := (hFM f).mpr ((ForcingSupportSize.native_mapsTo hM WW Options f).mp hf)
      have htMB := (hMB t).mpr ⟨n,hn,f,hfm,ht⟩
      exact (hRaw code).mpr (Or.inr ((hMergers code).mpr ⟨one,ho,t,htMB,hcode⟩))
  let schema : Project.BinarySchema 4 := {
    body := encoding 2 3 4 5 1 0
    freeClosed := encoding_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases WW (Fin.cases Options (Fin.cases zero (Fin.cases one Fin.elim0))), free := fun _ => zero }
  have he (q code) : schema.denote env q code ↔ Encoding WW Options zero one q code :=
    encoding_semantics hM ((env.push q).push code) 2 3 4 5 1 0
  obtain ⟨F,hF⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I schema env
    (source := Requests) (target := Raw)
    (by intro q hq; obtain ⟨code,hcode⟩ := hTotal q hq; exact ⟨code,(he q code).mpr hcode⟩)
    (by intro q _ x y hx hy; exact encoding_unique hM hne ((he q x).mp hx) ((he q y).mp hy))
    (by intro q code hq hc; exact hRange q code hq ((he q code).mp hc))
    (by intro x y code hx hy hxc hyc; exact encoding_injective hM hw hne hR hWW hx hy ((he x code).mp hxc) ((he y code).mp hyc))
  obtain ⟨bound,hBound⟩ := hRawSmall
  exact (ForcingSupportSize.native_small hM Requests mu).mpr
    (ZF.exists_compositionInjection hZF I hF hBound)

def boundSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound 0) (.bound 7))
    (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound 7) (.bound 7) (.bound 0))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (1 : Fin 8) 7))
    (.imp (.mem (.bound 4) (.bound 0))
    (.imp (.mem (.bound 5) (.bound 0))
    (.imp (.neg (Project.Formula.extensionalEq (.bound 4) (.bound 5)))
    (.imp (ConstructionRequestCarrier.carrier (0 : Fin 8) 1 2 3 4 5 6)
      (ProjectSyntax.encode id (ForcingSupportSize.small (6 : Fin 8) 7))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionRequestCarrier.carrier_freeClosed,Project.Formula.extensionalEq,
      Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace]

theorem bound_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence boundSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) boundSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionRequestCarrier.carrier_semantics hM]
  exact fun hw hmu hpow hD hz ho hne hR => data_cardinal_le hM hw hmu hpow hD hz ho hne hR

theorem bound_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence boundSentence) := ModelTransfer.derives (fun _ hM => bound_models hM)


theorem exists_small_carrier (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero one mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : Small D mu)
    (hz : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hne : zero ≠ one) : ∃ Requests, Carrier w D mul e zero one Requests ∧ Small Requests mu := by
  obtain ⟨Requests,hR⟩ := ConstructionRequestCarrier.exists_carrier hM hw D mul e zero one
  exact ⟨Requests,hR,data_cardinal_le hM hw hmu hpow hD hz ho hne hR⟩

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound (0 : Fin 7))) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 7)) (.bound (6 :
    Fin 7))) (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (6 :
    Fin 7)) (.bound (6 : Fin 7)) (.bound (0 : Fin 7))) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (1 : Fin 7) (6 : Fin 7))) (.imp (.mem (.bound (4 : Fin 7)) (.bound (0 : Fin
    7))) (.imp (.mem (.bound (5 : Fin 7)) (.bound (0 : Fin 7))) (.imp (.neg (Project.Formula.extensionalEq
    (.bound (4 : Fin 7)) (.bound (5 : Fin 7)))) (.existsE (.conj (ConstructionRequestCarrier.carrier (0 :
    Fin 7).succ (1 : Fin 7).succ (2 : Fin 7).succ (3 : Fin 7).succ (4 : Fin 7).succ (5 : Fin 7).succ (0 :
    Fin 8)) (ProjectSyntax.encode id (ForcingSupportSize.small (0 : Fin 8) (6 : Fin
    7).succ))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionRequestCarrier.carrier_freeClosed,Project.Formula.extensionalEq,
      Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionRequestCarrier.carrier_semantics hM]
  exact fun hw hmu hpow hD hz ho hne => exists_small_carrier hM hw hmu hpow hD hz ho hne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionRequestCardinality

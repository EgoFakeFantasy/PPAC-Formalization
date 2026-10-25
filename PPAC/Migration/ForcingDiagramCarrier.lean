/- Pinned Diagram M I and its label-permutation action as actual internal sets.
Consumers: Diagram.permuteOrderIso and ProductNames.actionHom. Reuse the
native function space, Separation and definable-function constructor. -/
import PPAC.Migration.ForcingDiagramAction

namespace PPAC.Migration.ForcingDiagramCarrier
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingSupportSize (Injection injection_semantics native_mapsTo)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Carrier (D I X : M.Carrier .set) : Prop :=
  ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r X ↔ Injection D I r

def carrier {m : Nat} (D I X : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) X.castSucc).iff
    (Source.SetLanguage.injection (Fin.last m) D.castSucc I.castSucc))

theorem carrier_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D I X : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (carrier D I X) ↔
      Carrier (env D) (env I) (env X) := by
  simp only [carrier, Carrier, Source.Formula.iff, Formula.Realize, injection_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h r => ⟨(h r).1, (h r).2⟩, fun h r => ⟨(h r).mp, (h r).mpr⟩⟩

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (D I : M.Carrier .set) :
    ∃ X, Carrier D I X := by
  obtain ⟨space, hSpace⟩ := SetTheory.ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) D I
  let query := Source.SetLanguage.injection (Fin.last 2) (0 : Fin 2).castSucc (1 : Fin 2).castSucc
  let params := Source.SetLanguage.args2 D I
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨X, hX⟩ := sep params space
  have hq : ∀ r, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases r params) query ↔ Injection D I r := by
    intro r
    exact
      injection_semantics (M := M) (Fin.lastCases r params) (Fin.last 2) (0 : Fin 2).castSucc (1 : Fin 2).castSucc
  refine ⟨X, fun r => ?_⟩
  exact ⟨fun hr => (hq r).mp ((hX r).mp hr).2,
    fun hr => (hX r).mpr ⟨(hSpace r).mpr ((native_mapsTo hM D I r).mp hr.1), (hq r).mpr hr⟩⟩

def Graph (D X pi a : M.Carrier .set) : Prop :=
  ∀ r s, PureKuratowski.PairMember M r s a ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem r X ∧
    (Definitional.Project.FirstOrderSemantics.reduct M).mem s X ∧ CompositionGraph D pi r s

def graph {m : Nat} (D X pi a : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc X.castSucc.castSucc).conj
      ((Formula.mem (Fin.last (m+1)) X.castSucc.castSucc).conj
        (compositionGraph D.castSucc.castSucc pi.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))))

theorem graph_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D X pi a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (graph D X pi a) ↔
      Graph (env D) (env X) (env pi) (env a) := by
  simp only [graph, Graph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    compositionGraph_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  exact ⟨fun h r s => ⟨(h r s).1, (h r s).2⟩, fun h r s => ⟨(h r s).mp, (h r s).mpr⟩⟩

/-- The inverse label graph reverses the action on diagrams, without choosing values. -/
theorem reverse {D I pi inv r s : M.Carrier .set} (hp : Permutation I pi)
    (hr : Injection D I r) (hi : InverseGraph pi inv) (h : CompositionGraph D pi r s) :
    CompositionGraph D inv s r := by
  intro x z
  constructor
  · intro hxz
    have hx := function_input hr.1.1 hxz
    obtain ⟨y, hzy, _⟩ := hp.1.1.2 z (hr.1.2 x z hxz)
    exact ⟨hx, y, (h x y).mpr ⟨hx, z, hxz, hzy⟩, (hi z y).mp hzy⟩
  · rintro ⟨_, y, hxy, hyz⟩
    obtain ⟨_, w, hxw, hwy⟩ := (h x y).mp hxy
    exact hp.2.1 w z y hwy ((hi z y).mpr hyz) ▸ hxw

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF) {D I X pi : M.Carrier .set}
    (hX : Carrier D I X) (hp : Permutation I pi) :
    ∃ a, Permutation X a ∧ Graph D X pi a := by
  let params : Fin 3 → M.Carrier .set := Fin.lastCases pi (Source.SetLanguage.args2 D I)
  let query := (Source.SetLanguage.injection (Fin.last 4) (0 : Fin 2).castSucc.castSucc.castSucc
    (1 : Fin 2).castSucc.castSucc.castSucc).conj
    (compositionGraph (0 : Fin 2).castSucc.castSucc.castSucc (Fin.last 2).castSucc.castSucc
      (Fin.last 3).castSucc (Fin.last 4))
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := fun j => params j.rev, free := fun _ => I }
  have hRel : ∀ r s, (ProjectSyntax.binary query).denote env r s ↔ Injection D I s ∧ CompositionGraph D pi r s := by
    intro r s
    rw [ForcingMapConditions.binary_semantics hM query params I r s]
    simp only [ForcingMapConditions.MapRel, query, Formula.Realize,
      injection_semantics (M := M), compositionGraph_semantics (M := M), params,
      Fin.lastCases_last, Fin.lastCases_castSucc]
    rfl
  obtain ⟨a, ha, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (ProjectSyntax.binary query) env
    (source := X) (target := X)
    (fun r hr => by
      obtain ⟨s, hs, hps⟩ := ForcingDiagramAction.exists_permute hM hp ((hX r).mp hr)
      exact ⟨s, (hRel r s).mpr ⟨hs, hps⟩⟩)
    (fun r _ s t hs ht => by
      obtain ⟨hs, hps⟩ := (hRel r s).mp hs
      obtain ⟨ht, hpt⟩ := (hRel r t).mp ht
      exact ForcingDiagramAction.unique hM hs ht hps hpt)
    (fun r s _ hs => (hX s).mpr ((hRel r s).mp hs).1)
  have hg : Graph D X pi a := fun r s => (he r s).trans
    (and_congr Iff.rfl ((hRel r s).trans (and_congr (hX s).symm Iff.rfl)))
  obtain ⟨inv, hi, hpi⟩ := exists_inverse hM hp
  refine ⟨a, ⟨(native_endomap hM X a).mpr ha, ?_, ?_⟩, hg⟩
  · intro r s t hrt hst
    obtain ⟨hr, _, hrt⟩ := (hg r t).mp hrt
    obtain ⟨hs, _, hst⟩ := (hg s t).mp hst
    exact ForcingDiagramAction.unique hM ((hX r).mp hr) ((hX s).mp hs)
      (reverse hp ((hX r).mp hr) hpi hrt) (reverse hp ((hX s).mp hs) hpi hst)
  · intro s hs
    obtain ⟨r, hr, hir⟩ := ForcingDiagramAction.exists_permute hM hi ((hX s).mp hs)
    have hpr := reverse hi ((hX s).mp hs) (fun x y => (hpi y x).symm) hir
    exact ⟨r, (hX r).mpr hr, (hg r s).mpr ⟨(hX r).mpr hr, hs, hpr⟩⟩

/-- Pointwise source permute_one lifted to the constructed action graph. -/
theorem graph_identity (hM : FirstOrder.Theory.Models M nativeZF) {D I X e a : M.Carrier .set}
    (hX : Carrier D I X) (ha : Endomap X a) (he : IdentityGraph I e) (hg : Graph D X e a) :
    IdentityGraph X a := by
  have hfix : ∀ r s, PureKuratowski.PairMember M r s a → r = s := by
    intro r s hrs
    obtain ⟨hr, hs, hc⟩ := (hg r s).mp hrs
    exact (ForcingDiagramAction.permute_one hM he ((hX r).mp hr) ((hX s).mp hs) hc).symm
  intro r s
  constructor
  · intro hrs
    exact ⟨function_input ha.1 hrs, hfix r s hrs⟩
  · rintro ⟨hr, rfl⟩
    obtain ⟨t, hrt, _⟩ := ha.1.2 r hr
    exact (hfix r t hrt).symm ▸ hrt

/-- The source multiplication law holds for the actual set-level action graphs. -/
theorem graph_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {D I X pi sigma product a b c : M.Carrier .set}
    (hX : Carrier D I X) (ha : Endomap X a) (hb : Endomap X b) (hc : Endomap X c)
    (hproduct : CompositionGraph I pi sigma product)
    (hga : Graph D X pi a) (hgb : Graph D X sigma b) (hgc : Graph D X product c) :
    CompositionGraph X a b c := by
  intro r t
  constructor
  · intro hrt
    obtain ⟨hr, ht, hpr⟩ := (hgc r t).mp hrt
    obtain ⟨s, hrs, _⟩ := hb.1.2 r hr
    obtain ⟨_, hs, hsr⟩ := (hgb r s).mp hrs
    obtain ⟨v, hsv, _⟩ := ha.1.2 s hs
    obtain ⟨_, hv, hps⟩ := (hga s v).mp hsv
    have htv := ForcingDiagramAction.permute_mul hM ((hX r).mp hr) ((hX v).mp hv)
      ((hX t).mp ht) hproduct hsr hps hpr
    exact ⟨hr, s, hrs, htv ▸ hsv⟩
  · rintro ⟨hr, s, hrs, hst⟩
    obtain ⟨_, _, hsr⟩ := (hgb r s).mp hrs
    obtain ⟨_, ht, hps⟩ := (hga s t).mp hst
    obtain ⟨v, hrv, _⟩ := hc.1.2 r hr
    obtain ⟨_, hv, hpr⟩ := (hgc r v).mp hrv
    have hvt := ForcingDiagramAction.permute_mul hM ((hX r).mp hr) ((hX t).mp ht)
      ((hX v).mp hv) hproduct hsr hps hpr
    exact hvt ▸ hrv

def identitySentence : Source.Sentence :=
  ((carrier (0 : Fin 5) 1 2).imp ((endomap 2 4).imp ((identityGraph 1 3).imp
    ((graph 0 2 3 4).imp (identityGraph 2 4))))).close

def multiplicationSentence : Source.Sentence :=
  ((carrier (0 : Fin 9) 1 2).imp ((endomap 2 6).imp ((endomap 2 7).imp ((endomap 2 8).imp
    ((compositionGraph 1 3 4 5).imp ((graph 0 2 3 6).imp ((graph 0 2 4 7).imp
      ((graph 0 2 5 8).imp (compositionGraph 2 6 7 8))))))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hX ha he hg
  apply (identityGraph_semantics (M := M) env 2 4).mpr
  exact graph_identity hM ((carrier_semantics (M := M) env 0 1 2).mp hX)
    ((endomap_semantics (M := M) env 2 4).mp ha) ((identityGraph_semantics (M := M) env 1 3).mp he)
    ((graph_semantics (M := M) env 0 2 3 4).mp hg)

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hX ha hb hc hp hga hgb hgc
  apply (compositionGraph_semantics (M := M) env 2 6 7 8).mpr
  exact graph_multiplication hM ((carrier_semantics (M := M) env 0 1 2).mp hX)
    ((endomap_semantics (M := M) env 2 6).mp ha) ((endomap_semantics (M := M) env 2 7).mp hb)
    ((endomap_semantics (M := M) env 2 8).mp hc) ((compositionGraph_semantics (M := M) env 1 3 4 5).mp hp)
    ((graph_semantics (M := M) env 0 2 3 6).mp hga) ((graph_semantics (M := M) env 0 2 4 7).mp hgb)
    ((graph_semantics (M := M) env 0 2 5 8).mp hgc)

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)
theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)

def carrierSentence : Source.Sentence :=
  (Formula.ex (carrier (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2))).close

def actionSentence : Source.Sentence :=
  ((carrier (0 : Fin 4) 1 2).imp ((permutation 1 3).imp (.ex
    ((permutation (2 : Fin 4).castSucc (Fin.last 4)).conj
      (graph (0 : Fin 4).castSucc (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)))))).close

theorem carrier_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence carrierSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨X, hX⟩ := exists_carrier hM (env 0) (env 1)
  refine ⟨X, ?_⟩
  apply (carrier_semantics (M := M) (Fin.lastCases X env) (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)).mpr
  simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hX

theorem action_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence actionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hX hp
  obtain ⟨a, ha, hg⟩ := exists_graph hM ((carrier_semantics (M := M) env 0 1 2).mp hX)
    ((permutation_semantics (M := M) env 1 3).mp hp)
  refine ⟨a, ?_, ?_⟩
  · apply (permutation_semantics (M := M) (Fin.lastCases a env) (2 : Fin 4).castSucc (Fin.last 4)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using ha
  · apply (graph_semantics (M := M) (Fin.lastCases a env) (0 : Fin 4).castSucc
      (2 : Fin 4).castSucc (3 : Fin 4).castSucc (Fin.last 4)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hg

theorem carrier_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence carrierSentence) :=
  ModelTransfer.derives (fun _ hM => carrier_models hM)
theorem action_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence actionSentence) :=
  ModelTransfer.derives (fun _ hM => action_models hM)

end PPAC.Migration.ForcingDiagramCarrier

/- Pinned CohenForcing.Condition.permute_one/permute_mul. Lift the label
identity/composition twice through coordinatePerm, then through exact set
images. This is the source Cohen component of ProductNames.actionHom. -/
import PPAC.Migration.ForcingCohenOrderAction

namespace PPAC.Migration.ForcingCohenActionLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
open ForcingCohenCoordinates (Graph graph graph_semantics)
open ForcingCohenConditions (Carrier carrier carrier_semantics)
open ForcingCohenOrderAction (ActionGraph actionGraph actionGraph_semantics)
open ForcingStabilizerTransport (Image)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem coordinate_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {A S e f : M.Carrier .set} (hf : Endomap S f) (he : IdentityGraph A e)
    (hgraph : Graph S e f) : IdentityGraph S f := by
  have hfix : ∀ z w, PureKuratowski.PairMember M z w f → z = w := by
    intro z w hzw
    obtain ⟨_, x, y, v, hz, hxv, hw⟩ := (hgraph z w).mp hzw
    have hx := ((he x v).mp hxv).2
    exact KuratowskiZF.code_unique hM hz (hx ▸ hw)
  intro z w
  constructor
  · intro hzw
    exact ⟨function_input hf.1 hzw, hfix z w hzw⟩
  · rintro ⟨hz, rfl⟩
    obtain ⟨w, hzw, _⟩ := hf.1.2 z hz
    exact (hfix z w hzw).symm ▸ hzw

theorem coordinate_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {A S pi sigma product f g h : M.Carrier .set}
    (hs : Endomap A sigma) (hg : Endomap S g)
    (hp : CompositionGraph A pi sigma product)
    (hgf : Graph S pi f) (hgg : Graph S sigma g) (hgh : Graph S product h) :
    CompositionGraph S f g h := by
  intro z t
  constructor
  · intro hzt
    obtain ⟨hzS, x, y, v, hz, hxv, ht⟩ := (hgh z t).mp hzt
    obtain ⟨_, u, hxu, huv⟩ := (hp x v).mp hxv
    obtain ⟨w, hw⟩ := KuratowskiZF.exists_code hM u y
    have hzw := (hgg z w).mpr ⟨hzS, x, y, u, hz, hxu, hw⟩
    exact ⟨hzS, w, hzw, (hgf w t).mpr ⟨hg.2 z w hzw, u, y, v, hw, huv, ht⟩⟩
  · rintro ⟨hzS, w, hzw, hwt⟩
    obtain ⟨_, x, y, u, hz, hxu, hw⟩ := (hgg z w).mp hzw
    obtain ⟨_, a, b, v, hw', hav, ht⟩ := (hgf w t).mp hwt
    have hab := PureKuratowski.code_injective hw hw'
    have huv : PureKuratowski.PairMember M u v pi := hab.1.symm ▸ hav
    have ht' : PureKuratowski.Code M t v y := hab.2.symm ▸ ht
    exact (hgh z t).mpr ⟨hzS, x, y, v, hz,
      (hp x v).mpr ⟨function_input hs.1 hxu, u, hxu, huv⟩, ht'⟩

theorem image_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {S e p q : M.Carrier .set} (he : IdentityGraph S e)
    (hp : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z S) (him : Image e p q) : q = p := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members q p
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := (him z).mp hz
    exact ((he x z).mp hxz).2 ▸ hx
  · intro hz
    exact (him z).mpr ⟨z, hz, (he z z).mpr ⟨hp z hz, rfl⟩⟩

theorem image_multiplication {S f g h p q r : M.Carrier .set}
    (hp : ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z p →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem z S)
    (hc : CompositionGraph S f g h) (hg : Image g p q) (hf : Image f q r) : Image h p r := by
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy, hyz⟩ := (hf z).mp hz
    obtain ⟨x, hx, hxy⟩ := (hg y).mp hy
    exact ⟨x, hx, (hc x z).mpr ⟨hp x hx, y, hxy, hyz⟩⟩
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨_, y, hxy, hyz⟩ := (hc x z).mp hxz
    exact (hf z).mpr ⟨y, (hg y).mpr ⟨x, hx, hxy⟩, hyz⟩

theorem graph_identity (hM : FirstOrder.Theory.Models M nativeZF)
    {S w X e a : M.Carrier .set} (hX : Carrier S w X) (ha : Endomap X a)
    (he : IdentityGraph S e) (hga : ActionGraph X e a) : IdentityGraph X a := by
  have hfix : ∀ p q, PureKuratowski.PairMember M p q a → p = q := by
    intro p q hpq
    obtain ⟨hp, _, him⟩ := (hga p q).mp hpq
    exact (image_identity hM he ((hX p).mp hp).1 him).symm
  intro p q
  constructor
  · intro hpq
    exact ⟨function_input ha.1 hpq, hfix p q hpq⟩
  · rintro ⟨hp, rfl⟩
    obtain ⟨q, hpq, _⟩ := ha.1.2 p hp
    exact (hfix p q hpq).symm ▸ hpq

theorem graph_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {S w X f g h a b c : M.Carrier .set} (hX : Carrier S w X)
    (ha : Endomap X a) (hb : Endomap X b) (hc : CompositionGraph S f g h)
    (hga : ActionGraph X f a) (hgb : ActionGraph X g b) (hgc : ActionGraph X h c) :
    CompositionGraph X a b c := by
  intro p r
  constructor
  · intro hpr
    obtain ⟨hp, _, him⟩ := (hgc p r).mp hpr
    obtain ⟨q, hpq, _⟩ := hb.1.2 p hp
    obtain ⟨_, hq, hg⟩ := (hgb p q).mp hpq
    obtain ⟨v, hqv, _⟩ := ha.1.2 q hq
    have hf := ((hga q v).mp hqv).2.2
    have hr := ForcingCohenOrderAction.image_unique hM him
      (image_multiplication ((hX p).mp hp).1 hc hg hf)
    exact ⟨hp, q, hpq, hr.symm ▸ hqv⟩
  · rintro ⟨hp, q, hpq, hqr⟩
    obtain ⟨_, _, hg⟩ := (hgb p q).mp hpq
    obtain ⟨_, hr, hf⟩ := (hga q r).mp hqr
    exact (hgc p r).mpr ⟨hp, hr, image_multiplication ((hX p).mp hp).1 hc hg hf⟩

/-- The two coordinate lifts in the source coordinatePerm and the condition action. -/
theorem permute_one (hM : FirstOrder.Theory.Models M nativeZF)
    {I C S w X e f g a : M.Carrier .set} (hX : Carrier S w X)
    (hf : Endomap C f) (hg : Endomap S g) (ha : Endomap X a)
    (he : IdentityGraph I e) (hfg : Graph C e f) (hgg : Graph S f g) (hga : ActionGraph X g a) :
    IdentityGraph X a :=
  graph_identity hM hX ha (coordinate_identity hM hg (coordinate_identity hM hf he hfg) hgg) hga

theorem permute_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {I C S w X pi sigma product f1 f2 f3 g1 g2 g3 a b c : M.Carrier .set}
    (hX : Carrier S w X) (hs : Endomap I sigma) (hf2 : Endomap C f2) (hg2 : Endomap S g2)
    (ha : Endomap X a) (hb : Endomap X b) (hp : CompositionGraph I pi sigma product)
    (hf1g : Graph C pi f1) (hf2g : Graph C sigma f2) (hf3g : Graph C product f3)
    (hg1g : Graph S f1 g1) (hg2g : Graph S f2 g2) (hg3g : Graph S f3 g3)
    (hga : ActionGraph X g1 a) (hgb : ActionGraph X g2 b) (hgc : ActionGraph X g3 c) :
    CompositionGraph X a b c :=
  graph_multiplication hM hX ha hb
    (coordinate_multiplication hM hf2 hg2
      (coordinate_multiplication hM hs hf2 hp hf1g hf2g hf3g) hg1g hg2g hg3g) hga hgb hgc

def identitySentence : Source.Sentence :=
  ((carrier (2 : Fin 9) 3 4).imp ((endomap (1 : Fin 9) 6).imp ((endomap (2 : Fin 9) 7).imp ((endomap (4 : Fin 9) 8).imp ((identityGraph (0 : Fin 9) 5).imp ((graph (1 : Fin 9) 5 6).imp ((graph (2 : Fin 9) 6 7).imp ((actionGraph (4 : Fin 9) 7 8).imp ((identityGraph (4 : Fin 9) 8)))))))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3 h4 h5 h6 h7
  apply (identityGraph_semantics (M := M) env 4 8).mpr
  exact permute_one hM
    ((carrier_semantics (M := M) env 2 3 4).mp h0)
    ((endomap_semantics (M := M) env 1 6).mp h1)
    ((endomap_semantics (M := M) env 2 7).mp h2)
    ((endomap_semantics (M := M) env 4 8).mp h3)
    ((identityGraph_semantics (M := M) env 0 5).mp h4)
    ((graph_semantics (M := M) env 1 5 6).mp h5)
    ((graph_semantics (M := M) env 2 6 7).mp h6)
    ((actionGraph_semantics (M := M) env 4 7 8).mp h7)

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)

def multiplicationSentence : Source.Sentence :=
  ((carrier (2 : Fin 17) 3 4).imp ((endomap (0 : Fin 17) 6).imp ((endomap (1 : Fin 17) 9).imp ((endomap (2 : Fin 17) 12).imp ((endomap (4 : Fin 17) 14).imp ((endomap (4 : Fin 17) 15).imp ((compositionGraph (0 : Fin 17) 5 6 7).imp ((graph (1 : Fin 17) 5 8).imp ((graph (1 : Fin 17) 6 9).imp ((graph (1 : Fin 17) 7 10).imp ((graph (2 : Fin 17) 8 11).imp ((graph (2 : Fin 17) 9 12).imp ((graph (2 : Fin 17) 10 13).imp ((actionGraph (4 : Fin 17) 11 14).imp ((actionGraph (4 : Fin 17) 12 15).imp ((actionGraph (4 : Fin 17) 13 16).imp ((compositionGraph (4 : Fin 17) 14 15 16)))))))))))))))))).close

theorem multiplication_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence multiplicationSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  apply (compositionGraph_semantics (M := M) env 4 14 15 16).mpr
  exact permute_mul hM
    ((carrier_semantics (M := M) env 2 3 4).mp h0)
    ((endomap_semantics (M := M) env 0 6).mp h1)
    ((endomap_semantics (M := M) env 1 9).mp h2)
    ((endomap_semantics (M := M) env 2 12).mp h3)
    ((endomap_semantics (M := M) env 4 14).mp h4)
    ((endomap_semantics (M := M) env 4 15).mp h5)
    ((compositionGraph_semantics (M := M) env 0 5 6 7).mp h6)
    ((graph_semantics (M := M) env 1 5 8).mp h7)
    ((graph_semantics (M := M) env 1 6 9).mp h8)
    ((graph_semantics (M := M) env 1 7 10).mp h9)
    ((graph_semantics (M := M) env 2 8 11).mp h10)
    ((graph_semantics (M := M) env 2 9 12).mp h11)
    ((graph_semantics (M := M) env 2 10 13).mp h12)
    ((actionGraph_semantics (M := M) env 4 11 14).mp h13)
    ((actionGraph_semantics (M := M) env 4 12 15).mp h14)
    ((actionGraph_semantics (M := M) env 4 13 16).mp h15)

theorem multiplication_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence multiplicationSentence) :=
  ModelTransfer.derives (fun _ hM => multiplication_models hM)

end PPAC.Migration.ForcingCohenActionLaws

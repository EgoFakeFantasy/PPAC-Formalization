/- Pinned ProbePresentations.Word.head_transport/head_transport_eq_some.
Exact head relations for the existing literal internal transport, not a fresh
word map. Source and target Raw cases include every internal finite length. -/
import PPAC.Migration.ConstructionProbeGatesSyntax
import PPAC.Migration.ConstructionProbeWordTransport

namespace PPAC.Migration.ConstructionProbeHeadTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawTransport ConstructionProbeGates
open ConstructionProbeGatesSyntax (headNone headNone_freeClosed headNone_semantics headSome headSome_freeClosed headSome_semantics)
open ConstructionProbeRawTransportSyntax (value value_freeClosed value_semantics)
open ForcingSupportSize (MapsTo Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem head_transport_some (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g q Q s gs : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : Injection S SN g)
    (htr : Value w D S SN f g q Q) (hgs : PureKuratowski.PairMember M s gs g) :
    HeadSome w N SN Q gs ↔ HeadSome w D S q s := by
  constructor
  · intro hhead
    rcases cases_raw hM hw hz hzw (value_raw hf htr).1 with ⟨x,hx⟩ | ⟨t,v,ht⟩
    · obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
      exact (old_no_head hz (transport_old hM hz hf hx hfx htr) hhead).elim
    · obtain ⟨gt,hgt,_⟩ := hg.1.1.2 t (ConstructionProbeRawAction.cons_letter ht)
      obtain ⟨V,hV⟩ := value_total hM hf hg.1 (cons_raw ht).1
      have hmapped := transport_cons hM hw hf hg.1 ht hgt hV htr
      have he := head_unique hM hw ⟨V,hmapped⟩ hhead
      subst gt
      have he := hg.2 t s gs hgt hgs
      subst t
      exact ⟨v,ht⟩
  · rintro ⟨t,ht⟩
    obtain ⟨T,hT⟩ := value_total hM hf hg.1 (cons_raw ht).1
    exact ⟨T,transport_cons hM hw hf hg.1 ht hgs hT htr⟩

theorem head_transport_none (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g q Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (htr : Value w D S SN f g q Q) :
    HeadNone zero N Q ↔ HeadNone zero D q := by
  constructor
  · rintro ⟨y,hy⟩
    rcases cases_raw hM hw hz hzw (value_raw hf htr).1 with ⟨x,hx⟩ | ⟨s,t,ht⟩
    · exact ⟨x,hx⟩
    · obtain ⟨gs,hgs,_⟩ := hg.1.2 s (ConstructionProbeRawAction.cons_letter ht)
      obtain ⟨T,hT⟩ := value_total hM hf hg (cons_raw ht).1
      exact (old_ne_cons hz hy (transport_cons hM hw hf hg ht hgs hT htr)).elim
  · rintro ⟨x,hx⟩
    obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
    exact ⟨fx,transport_old hM hz hf hx hfx htr⟩

def HeadTransport (w D N S SN zero g q Q : M.Carrier .set) : Prop :=
  (HeadNone zero N Q ↔ HeadNone zero D q) ∧
  ∀ s gs, PureKuratowski.PairMember M s gs g → (HeadSome w N SN Q gs ↔ HeadSome w D S q s)

theorem head_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g q Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : Injection S SN g) (htr : Value w D S SN f g q Q) :
    HeadTransport w D N S SN zero g q Q :=
  ⟨head_transport_none hM hw hz hzw hf hg.1 htr,
    fun _ _ hgs => head_transport_some hM hw hz hzw hf hg htr hgs⟩

def headTransport {m : Nat} (w D N S SN zero g q Q : Fin m) : Project.Formula 1 m :=
  .conj (.iff (headNone zero N Q) (headNone zero D q))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ 1 0))
      (.iff (headSome w.succ.succ N.succ.succ SN.succ.succ Q.succ.succ 0)
        (headSome w.succ.succ D.succ.succ S.succ.succ q.succ.succ 1)))))

theorem headTransport_freeClosed {m : Nat} (w D N S SN zero g q Q : Fin m) :
    (headTransport w D N S SN zero g q Q).FreeClosed := by
  simp -implicitDefEqProofs [headTransport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    headNone_freeClosed,headSome_freeClosed]

theorem headTransport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N S SN zero g q Q : Fin m) :
    Project.Formula.satisfies env (headTransport w D N S SN zero g q Q) ↔
      HeadTransport (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN)
        (env.bound zero) (env.bound g) (env.bound q) (env.bound Q) := by
  simp only [headTransport,HeadTransport,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    headNone_semantics hM,headSome_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge]
  rfl

def transportSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 10))) (.imp (Project.Formula.isEmpty (.bound (5 : Fin
    10))) (.imp (.mem (.bound (5 : Fin 10)) (.bound (0 : Fin 10))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (6 : Fin 10) (1 : Fin 10) (2 : Fin 10))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection (7 : Fin 10) (3 : Fin 10) (4 : Fin 10))) (.imp (value (0 : Fin 10) (1 : Fin
    10) (3 : Fin 10) (4 : Fin 10) (6 : Fin 10) (7 : Fin 10) (8 : Fin 10) (9 : Fin 10)) (headTransport (0 : Fin
    10) (1 : Fin 10) (2 : Fin 10) (3 : Fin 10) (4 : Fin 10) (5 : Fin 10) (7 : Fin 10) (8 : Fin 10) (9 : Fin
    10))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      value_freeClosed,headTransport_freeClosed]

theorem transport_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence transportSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) transportSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    value_semantics hM,headTransport_semantics hM]
  exact fun hw hz hzw hf hg htr => head_transport hM hw hz hzw hf hg htr

theorem transport_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence transportSentence) := ModelTransfer.derives (fun _ hM => transport_models hM)

end PPAC.Migration.ConstructionProbeHeadTransport

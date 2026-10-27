/- Pinned CompleteRounds.MergerData.code_injective/data_cardinal_le.
The SAME complete partial start graph is padded on ALL internal omega pairs.
Option tags distinguish missing rows from actual starts, INCLUDING diagonals.
Consumer: ConstructionRequestCardinality, not a byte/reader backend. -/
import PPAC.Migration.ConstructionRequestCarrier
import PPAC.Migration.ExistingCardinalBounds
import YesMetaZFC.SetTheory.Card.Arithmetic.Basic

namespace PPAC.Migration.ConstructionRequestPadding
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Small)
open ConstructionRequestCarrier (WellFormed)
open ConstructionMergerRelations (Prescription)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (zero one P key value : M.Carrier .set) : Prop :=
  (∃ ab, PureKuratowski.PairMember M key ab P ∧ PureKuratowski.Code M value one ab) ∨
  (¬ ∃ ab, PureKuratowski.PairMember M key ab P) ∧ PureKuratowski.Code M value zero zero

def Padding (WW zero one P f : M.Carrier .set) : Prop := ∀ key value,
  PureKuratowski.PairMember M key value f ↔
    (Project.FirstOrderSemantics.reduct M).mem key WW ∧ Value zero one P key value

theorem prescription_single (hM : FirstOrder.Theory.Models M nativeZF) {n D P key a b : M.Carrier .set}
    (hWell : WellFormed n D P) (hP : Prescription n D P)
    (ha : PureKuratowski.PairMember M key a P) (hb : PureKuratowski.PairMember M key b P) : a = b := by
  obtain ⟨row,hrow,hr⟩ := ha
  obtain ⟨i,j,x,y,ij,ab,hcode,hij,hab,hi,hj,hx,hy⟩ := hWell row hr
  obtain ⟨eqKey,eqA⟩ := PureKuratowski.code_injective hrow hcode
  obtain ⟨row',hrow',hr'⟩ := hb
  obtain ⟨i',j',x',y',ij',ab',hcode',hij',hab',hi',hj',hx',hy'⟩ := hWell row' hr'
  obtain ⟨eqKey',eqB⟩ := PureKuratowski.code_injective hrow' hcode'
  have hh : ij = ij' := eqKey.symm.trans eqKey'
  have hk : PureKuratowski.Code M ij i' j' := hh.symm ▸ hij'
  obtain ⟨eqi,eqj⟩ := PureKuratowski.code_injective hij hk
  subst i'; subst j'
  obtain ⟨eqx,eqy⟩ := hP.2 i j x y x' y'
    ⟨ab,hab,ij,hij,row,hcode,hr⟩ ⟨ab',hab',ij',hij',row',hcode',hr'⟩
  subst x'; subst y'
  exact eqA.trans ((KuratowskiZF.code_unique hM hab hab').trans eqB.symm)

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {n D zero one P key x y : M.Carrier .set}
    (hWell : WellFormed n D P) (hP : Prescription n D P)
    (hx : Value zero one P key x) (hy : Value zero one P key y) : x = y := by
  rcases hx with ⟨a,ha,hx⟩ | ⟨ha,hx⟩ <;> rcases hy with ⟨b,hb,hy⟩ | ⟨hb,hy⟩
  · have he := prescription_single hM hWell hP ha hb
    subst b
    exact KuratowskiZF.code_unique hM hx hy
  · exact False.elim (hb ⟨a,ha⟩)
  · exact False.elim (ha ⟨b,hb⟩)
  · exact KuratowskiZF.code_unique hM hx hy


def padValue {m : Nat} (zero one P key value : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge P.succ key.succ (0 : Fin (m+1))))
  (PureKuratowskiProject.code (.bound value.succ) (.bound one.succ) (.bound (0 : Fin (m+1)))))) (.conj (.neg
  (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge P.succ key.succ (0 : Fin (m+1))))))
  (PureKuratowskiProject.code (.bound value) (.bound zero) (.bound zero))))

theorem padValue_freeClosed {m : Nat} (zero one P key value : Fin m) :
    (padValue zero one P key value).FreeClosed := by
  simp -implicitDefEqProofs [padValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem padValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero one P key value : Fin m) :
    Project.Formula.satisfies env (padValue zero one P key value) ↔ Value (env.bound zero) (env.bound one) (env.bound P) (env.bound key) (env.bound value) := by
  simp only [padValue,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,KuratowskiZF.code_correct hM]
  rfl


def padding {m : Nat} (WW zero one P f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound WW.succ.succ)) (padValue zero.succ.succ
  one.succ.succ P.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem padding_freeClosed {m : Nat} (WW zero one P f : Fin m) :
    (padding WW zero one P f).FreeClosed := by
  simp -implicitDefEqProofs [padding,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,padValue_freeClosed]

theorem padding_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (WW zero one P f : Fin m) :
    Project.Formula.satisfies env (padding WW zero one P f) ↔ Padding (env.bound WW) (env.bound zero) (env.bound one) (env.bound P) (env.bound f) := by
  simp only [padding,Padding,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,padValue_semantics hM]
  rfl


theorem exists_padding (hM : FirstOrder.Theory.Models M nativeZF)
    {n D P WW DD B Options zero one : M.Carrier .set}
    (hWell : WellFormed n D P) (hP : Prescription n D P)
    (hDD : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) DD D D)
    (hB : ∀ ab, (Project.FirstOrderSemantics.reduct M).mem ab DD → (Project.FirstOrderSemantics.reduct M).mem ab B)
    (hOptions : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) Options B B)
    (hzB : (Project.FirstOrderSemantics.reduct M).mem zero B)
    (hoB : (Project.FirstOrderSemantics.reduct M).mem one B) :
    ∃ f, MapsTo WW Options f ∧ Padding WW zero one P f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  let schema : Project.BinarySchema 3 := {
    body := padValue 2 3 4 1 0
    freeClosed := padValue_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases zero (Fin.cases one (Fin.cases P Fin.elim0)), free := fun _ => zero }
  have he (key out) : schema.denote env key out ↔ Value zero one P key out :=
    padValue_semantics hM ((env.push key).push out) 2 3 4 1 0
  obtain ⟨f,hf,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I schema env
    (source := WW) (target := Options) (by
      intro key _
      by_cases h : ∃ ab, PureKuratowski.PairMember M key ab P
      · obtain ⟨ab,hab⟩ := h
        obtain ⟨out,hout⟩ := I.total one ab
        exact ⟨out,(he key out).mpr (Or.inl ⟨ab,hab,hout⟩)⟩
      · obtain ⟨out,hout⟩ := I.total zero zero
        exact ⟨out,(he key out).mpr (Or.inr ⟨h,hout⟩)⟩)
    (by intro key _ x y hx hy; exact value_unique hM hWell hP ((he key x).mp hx) ((he key y).mp hy))
    (by
      intro key out _ hout
      rcases (he key out).mp hout with ⟨ab,hab,hout⟩ | ⟨_,hout⟩
      · obtain ⟨row,hrow,hr⟩ := hab
        obtain ⟨i,j,a,b,ij,ab',hrow',hij,hab',_,_,ha,hb⟩ := hWell row hr
        have eqAb := (PureKuratowski.code_injective hrow hrow').2
        have habD := (hDD ab').mpr ⟨a,ha,b,hb,hab'⟩
        exact (hOptions out).mpr ⟨one,hoB,ab,hB ab (eqAb.symm ▸ habD),hout⟩
      · exact (hOptions out).mpr ⟨zero,hzB,zero,hzB,hout⟩)
  exact ⟨f,(ForcingSupportSize.native_mapsTo hM WW Options f).mpr hf,
    fun key out => (hGraph key out).trans (and_congr_right fun _ => he key out)⟩

theorem padding_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {WW Options zero one P f g : M.Carrier .set}
    (hf : MapsTo WW Options f) (hg : MapsTo WW Options g)
    (hpf : Padding WW zero one P f) (hpg : Padding WW zero one P g) : f = g := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro row
  constructor <;> intro hr
  · obtain ⟨key,out,_,hc⟩ := hf.1.1 row hr
    obtain ⟨row',hc',hr'⟩ := (hpg key out).mpr ((hpf key out).mp ⟨row,hc,hr⟩)
    exact KuratowskiZF.code_unique hM hc hc' ▸ hr'
  · obtain ⟨key,out,_,hc⟩ := hg.1.1 row hr
    obtain ⟨row',hc',hr'⟩ := (hpf key out).mpr ((hpg key out).mp ⟨row,hc,hr⟩)
    exact KuratowskiZF.code_unique hM hc hc' ▸ hr'

theorem recover_edge (hM : FirstOrder.Theory.Models M nativeZF)
    {WW zero one P Q f key ab : M.Carrier .set}
    (hne : zero ≠ one) (hP : Padding WW zero one P f) (hQ : Padding WW zero one Q f)
    (hk : (Project.FirstOrderSemantics.reduct M).mem key WW)
    (hab : PureKuratowski.PairMember M key ab P) : PureKuratowski.PairMember M key ab Q := by
  obtain ⟨out,hout⟩ := (KuratowskiZF.interpretation hM).total one ab
  have hf := (hP key out).mpr ⟨hk,Or.inl ⟨ab,hab,hout⟩⟩
  rcases ((hQ key out).mp hf).2 with ⟨ab',hab',hc⟩ | ⟨_,hc⟩
  · have he := (PureKuratowski.code_injective hout hc).2
    exact he.symm ▸ hab'
  · exact False.elim (hne (PureKuratowski.code_injective hc hout).1)

theorem padding_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w n m D WW zero one P Q f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hne : zero ≠ one)
    (hWW : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) WW w w)
    (hWellP : WellFormed n D P) (hWellQ : WellFormed m D Q)
    (hP : Padding WW zero one P f) (hQ : Padding WW zero one Q f) : P = Q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have transfer {n P Q} (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
      (hWell : WellFormed n D P) (hP : Padding WW zero one P f) (hQ : Padding WW zero one Q f)
      (row : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem row P) :
      (Project.FirstOrderSemantics.reduct M).mem row Q := by
    obtain ⟨i,j,a,b,ij,ab,hrow,hij,hab,hi,hj,_,_⟩ := hWell row hr
    have hk := (hWW ij).mpr ⟨i,(hw.isOrdinal hZF).transitive n hn i hi,
      j,(hw.isOrdinal hZF).transitive n hn j hj,hij⟩
    obtain ⟨row',hc,hr'⟩ := recover_edge hM hne hP hQ hk ⟨row,hrow,hr⟩
    exact KuratowskiZF.code_unique hM hrow hc ▸ hr'
  exact (ModelTransfer.extensionality hM).eq_of_same_members P Q (fun row =>
    ⟨transfer hn hWellP hP hQ row,transfer hm hWellQ hQ hP row⟩)

end PPAC.Migration.ConstructionRequestPadding

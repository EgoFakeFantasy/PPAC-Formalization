/- Pinned ProductForcing.Condition and ProductNames.Poset orders.
The actual product/WithTop carriers inherit the source Diagram partial order.
The certificate supplies the preorder consumed by AtomicForcing, antisymmetry
and an internal greatest condition; it retains the stage-8 monoid hypotheses. -/
import PPAC.Migration.ForcingDiagramPoset
import PPAC.Migration.ForcingProductSymmetry

namespace PPAC.Migration.ForcingProductPoset
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingDiagramPoset (LeftCancelMonoid Conical leftCancelMonoid conical)
open ForcingCohenCoordinates (Cartesian)
open ForcingWithTopCarrier (Carrier Single Empty)
open ForcingProductFamily (Presentation presentation)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem product_refl {D I mul e X Y P z : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hP : Cartesian X Y P) (hY : ForcingDiagramCarrier.Carrier D I Y)
    (hz : (Definitional.Project.FirstOrderSemantics.reduct M).mem z P) : ForcingProductAction.Le D mul z z := by
  obtain ⟨x, _, y, hy, hz⟩ := (hP z).mp hz
  exact ⟨x,y,x,y,hz,hz,fun _ hx => hx,ForcingDiagramPoset.le_refl h ((hY y).mp hy)⟩

theorem product_trans {D mul e a b c : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hab : ForcingProductAction.Le D mul a b) (hbc : ForcingProductAction.Le D mul b c) :
    ForcingProductAction.Le D mul a c := by
  obtain ⟨x,y,u,v,ha,hb,hxu,hyv⟩ := hab
  obtain ⟨u',v',p,q,hb',hc,hup,hvq⟩ := hbc
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hb hb'
  exact ⟨x,y,p,q,ha,hc,fun z hz => hxu z (hup z hz),ForcingDiagramPoset.le_trans h hyv hvq⟩

theorem diagram_mem_of_code {X Y P z x y : M.Carrier .set} (hP : Cartesian X Y P)
    (hz : (Definitional.Project.FirstOrderSemantics.reduct M).mem z P) (hc : PureKuratowski.Code M z x y) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y Y := by
  obtain ⟨a,_,b,hb,hab⟩ := (hP z).mp hz
  exact (PureKuratowski.code_injective hab hc).2 ▸ hb

theorem product_antisymm (hM : FirstOrder.Theory.Models M nativeZF) {D I mul e X Y P a b : M.Carrier .set}
    (h : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hP : Cartesian X Y P)
    (hY : ForcingDiagramCarrier.Carrier D I Y)
    (haP : (Definitional.Project.FirstOrderSemantics.reduct M).mem a P)
    (hbP : (Definitional.Project.FirstOrderSemantics.reduct M).mem b P)
    (hab : ForcingProductAction.Le D mul a b) (hba : ForcingProductAction.Le D mul b a) : a = b := by
  obtain ⟨x,y,u,v,ha,hb,hxu,hyv⟩ := hab
  obtain ⟨u',v',x',y',hb',ha',hux,hvy⟩ := hba
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hb hb'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ha ha'
  have hxuEq := (ModelTransfer.extensionality hM).eq_of_same_members x u
    (fun z => ⟨hux z,hxu z⟩)
  have hyvEq := ForcingDiagramPoset.le_antisymm hM h hc
    ((hY y).mp (diagram_mem_of_code hP haP ha)) ((hY v).mp (diagram_mem_of_code hP hbP hb)) hyv hvy
  subst u
  subst v
  exact KuratowskiZF.code_unique hM ha hb

theorem coe_mem {P W z p : M.Carrier .set} (hW : Carrier P W)
    (hz : (Definitional.Project.FirstOrderSemantics.reduct M).mem z W) (hp : Single z p) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem p P := by
  rcases (hW z).mp hz with he | ⟨q,hq,hzq⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hp he)
  · exact (ForcingWithTopCarrier.single_injective hzq hp) ▸ hq

theorem withtop_refl {D I mul e X Y P W z : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hP : Cartesian X Y P) (hY : ForcingDiagramCarrier.Carrier D I Y) (hW : Carrier P W)
    (hz : (Definitional.Project.FirstOrderSemantics.reduct M).mem z W) : ForcingWithTopAction.Le D mul z z := by
  rcases (hW z).mp hz with he | ⟨p,hp,hzp⟩
  · exact Or.inl he
  · exact Or.inr ⟨p,p,hzp,hzp,product_refl h hP hY hp⟩

theorem withtop_trans {D mul e a b c : M.Carrier .set} (h : LeftCancelMonoid D mul e)
    (hab : ForcingWithTopAction.Le D mul a b) (hbc : ForcingWithTopAction.Le D mul b c) :
    ForcingWithTopAction.Le D mul a c := by
  rcases hbc with he | ⟨p,q,hbp,hcq,hpq⟩
  · exact Or.inl he
  · rcases hab with he | ⟨x,y,hax,hby,hxy⟩
    · exact False.elim (ForcingWithTopCarrier.single_nonempty hbp he)
    · have heq := ForcingWithTopCarrier.single_injective hby hbp
      subst y
      exact Or.inr ⟨x,q,hax,hcq,product_trans h hxy hpq⟩

theorem withtop_antisymm (hM : FirstOrder.Theory.Models M nativeZF) {D I mul e X Y P W a b : M.Carrier .set}
    (h : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hP : Cartesian X Y P)
    (hY : ForcingDiagramCarrier.Carrier D I Y) (hW : Carrier P W)
    (ha : (Definitional.Project.FirstOrderSemantics.reduct M).mem a W)
    (hb : (Definitional.Project.FirstOrderSemantics.reduct M).mem b W)
    (hab : ForcingWithTopAction.Le D mul a b) (hba : ForcingWithTopAction.Le D mul b a) : a = b := by
  rcases hab with hbE | ⟨p,q,hap,hbq,hpq⟩
  · rcases hba with haE | ⟨p,q,hbp,_,_⟩
    · exact ForcingWithTopCarrier.empty_unique hM haE hbE
    · exact False.elim (ForcingWithTopCarrier.single_nonempty hbp hbE)
  · rcases hba with haE | ⟨q',p',hbq',hap',hqp⟩
    · exact False.elim (ForcingWithTopCarrier.single_nonempty hap haE)
    · have heq := ForcingWithTopCarrier.single_injective hbq hbq'
      have hep := ForcingWithTopCarrier.single_injective hap hap'
      subst q'
      subst p'
      have hpqEq := product_antisymm hM h hc hP hY (coe_mem hW ha hap) (coe_mem hW hb hbq) hpq hqp
      subst q
      exact ForcingWithTopCarrier.single_unique hM hap hbq

theorem exists_top (hM : FirstOrder.Theory.Models M nativeZF) {P W : M.Carrier .set} (D mul : M.Carrier .set)
    (hW : Carrier P W) : ∃ t, Empty (M := M) t ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem t W ∧
      ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z W → ForcingWithTopAction.Le D mul z t := by
  obtain ⟨t,ht⟩ := ForcingWithTopCarrier.exists_empty hM
  exact ⟨t,ht,(hW t).mpr (Or.inl ht),fun _ _ => Or.inl ht⟩

/-- The exact already-used atomic forcing preorder, now discharged for this relation. -/
theorem preorder {k : Nat} (env : Fin k → M.Carrier .set)
    (D mul W : Fin k) {I e X Y P : M.Carrier .set} (h : LeftCancelMonoid (env D) (env mul) e)
    (hP : Cartesian X Y P) (hY : ForcingDiagramCarrier.Carrier (env D) I Y) (hW : Carrier P (env W)) :
    ForcingAtomicBasic.PreorderOn (ForcingProductSymmetry.orderFormula D mul) env (env W) := by
  constructor
  · intro z hz
    exact (ForcingProductSymmetry.orderFormula_semantics env D mul z z).mpr (withtop_refl h hP hY hW hz)
  · intro a b c _ _ _ hab hbc
    exact (ForcingProductSymmetry.orderFormula_semantics env D mul a c).mpr (withtop_trans h
      ((ForcingProductSymmetry.orderFormula_semantics env D mul a b).mp hab)
      ((ForcingProductSymmetry.orderFormula_semantics env D mul b c).mp hbc))

def antisymmetric {m : Nat} (D mul W : Fin m) : Formula m :=
  let a := (Fin.last m).castSucc
  let b := Fin.last (m+1)
  .all (.all ((Formula.mem a W.castSucc.castSucc).imp ((Formula.mem b W.castSucc.castSucc).imp
    ((ForcingWithTopAction.le D.castSucc.castSucc mul.castSucc.castSucc a b).imp
      ((ForcingWithTopAction.le D.castSucc.castSucc mul.castSucc.castSucc b a).imp (.equal a b))))))

def top {m : Nat} (D mul W : Fin m) : Formula m :=
  .ex ((ForcingWithTopCarrier.empty (Fin.last m)).conj ((Formula.mem (Fin.last m) W.castSucc).conj
    (.all ((Formula.mem (Fin.last (m+1)) W.castSucc.castSucc).imp
      (ForcingWithTopAction.le D.castSucc.castSucc mul.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)))))

theorem antisymmetric_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul W : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (antisymmetric D mul W) ↔
    ∀ a b, (Definitional.Project.FirstOrderSemantics.reduct M).mem a (env W) →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem b (env W) →
      ForcingWithTopAction.Le (env D) (env mul) a b → ForcingWithTopAction.Le (env D) (env mul) b a → a = b := by
  simp only [antisymmetric, Formula.Realize, ForcingWithTopAction.le_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem top_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul W : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (top D mul W) ↔
    ∃ t, Empty (M := M) t ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem t (env W) ∧
      ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z (env W) →
        ForcingWithTopAction.Le (env D) (env mul) z t := by
  simp only [top, Formula.Realize, ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingWithTopAction.le_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def sentence : Source.Sentence :=
  ((leftCancelMonoid (0 : Fin 13) 11 12).imp ((conical (0 : Fin 13) 11 12).imp
    ((presentation (0 : Fin 13) 1 2 3 4 5 6 7 8 9 10).imp
      ((ForcingAtomicBasic.preorder (ForcingProductSymmetry.orderFormula (0 : Fin 13) 11) id 10).conj
        ((antisymmetric (0 : Fin 13) 11 10).conj (top (0 : Fin 13) 11 10)))))).close

theorem models (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence sentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hc hp
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env 0 11 12).mp hm
  have hc' := (ForcingDiagramPoset.conical_semantics (M := M) env 0 11 12).mp hc
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env 0 1 2 3 4 5 6 7 8 9 10).mp hp
  obtain ⟨_,_,_,hY,hP,hW⟩ := hp'
  refine ⟨?_,?_,?_⟩
  · exact (ForcingAtomicBasic.preorder_semantics (M := M) env (ForcingProductSymmetry.orderFormula (0 : Fin 13) 11) id 10).mpr
      (preorder env 0 11 10 hm' hP hY hW)
  · exact (antisymmetric_semantics (M := M) env 0 11 10).mpr
      (fun a b ha hb hab hba => withtop_antisymm hM hm' hc' hP hY hW ha hb hab hba)
  · exact (top_semantics (M := M) env 0 11 10).mpr (exists_top hM (env 0) (env 11) hW)

theorem kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence sentence) :=
  ModelTransfer.derives (fun _ hM => models hM)

end PPAC.Migration.ForcingProductPoset

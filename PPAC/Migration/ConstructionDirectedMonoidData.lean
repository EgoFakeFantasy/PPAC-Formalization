/- Pinned DirectLimits.ConservativeLimit stage monoids and transition MonoidHoms.
Actual input tables, with the SAME arbitrary directed-system Domains/F.
Reuse original native LeftCancelMonoid/Conical and native function uniqueness.
These are SOURCE stage assumptions, never assumed laws of the limit. -/
import PPAC.Migration.ConstructionDirectedLimitCarrier
import PPAC.Migration.ConstructionProbeTransitions

namespace PPAC.Migration.ConstructionDirectedMonoidData
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingConditionGraphs (FunctionOn function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Family (J Domains Muls Units : M.Carrier .set) : Prop :=
  FunctionOn J Domains ∧ FunctionOn J Muls ∧ FunctionOn J Units ∧
    ∀ i D mul e, PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
      PureKuratowski.PairMember M i e Units → LeftCancelMonoid D mul e

def ProductAt (J Domains Muls i x y z : M.Carrier .set) : Prop :=
  At J Domains i x ∧ At J Domains i y ∧ At J Domains i z ∧
    ∃ mul, PureKuratowski.PairMember M i mul Muls ∧ Product mul x y z

def UnitAt (J Domains Units i e : M.Carrier .set) : Prop :=
  At J Domains i e ∧ PureKuratowski.PairMember M i e Units

/-- Pointwise map_mul/map_one for the actual transition FUNCTION GRAPHS. -/
def HomLaws (J E Domains F Muls Units : M.Carrier .set) : Prop :=
  (∀ i j x y z xx yy zz, PureKuratowski.PairMember M i j E → ProductAt J Domains Muls i x y z →
    Transition J Domains F i j x xx → Transition J Domains F i j y yy → Transition J Domains F i j z zz →
      ProductAt J Domains Muls j xx yy zz) ∧
  ∀ i j e ee, PureKuratowski.PairMember M i j E → UnitAt J Domains Units i e →
    Transition J Domains F i j e ee → UnitAt J Domains Units j ee

def ConicalFamily (J Domains Muls Units : M.Carrier .set) : Prop :=
  ∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
      PureKuratowski.PairMember M i e Units → Conical D mul e

theorem family_at {J Domains Muls Units i : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ D mul e, PureKuratowski.PairMember M i D Domains ∧ PureKuratowski.PairMember M i mul Muls ∧
      PureKuratowski.PairMember M i e Units ∧ LeftCancelMonoid D mul e := by
  obtain ⟨D,hD,_⟩ := hF.1.2 i hi
  obtain ⟨mul,hm,_⟩ := hF.2.1.2 i hi
  obtain ⟨e,he,_⟩ := hF.2.2.1.2 i hi
  exact ⟨D,mul,e,hD,hm,he,hF.2.2.2 i D mul e hD hm he⟩

theorem domain_mem {J Domains Muls Units i D x : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hD : PureKuratowski.PairMember M i D Domains)
    (hx : At J Domains i x) : (Project.FirstOrderSemantics.reduct M).mem x D := by
  obtain ⟨_,D',hD',hx'⟩ := hx
  exact (function_unique hF.1 hD' hD) ▸ hx'

theorem product_data {J Domains Muls Units i D mul x y z : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hD : PureKuratowski.PairMember M i D Domains)
    (hm : PureKuratowski.PairMember M i mul Muls) (hp : ProductAt J Domains Muls i x y z) :
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ (Project.FirstOrderSemantics.reduct M).mem y D ∧
      (Project.FirstOrderSemantics.reduct M).mem z D ∧ Product mul x y z := by
  obtain ⟨hx,hy,hz,mul',hm',hprod⟩ := hp
  exact ⟨domain_mem hF hD hx,domain_mem hF hD hy,domain_mem hF hD hz,(function_unique hF.2.1 hm' hm) ▸ hprod⟩

theorem product_mk {J Domains Muls i D mul x y z : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) (hD : PureKuratowski.PairMember M i D Domains)
    (hm : PureKuratowski.PairMember M i mul Muls)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z D) (hp : Product mul x y z) :
    ProductAt J Domains Muls i x y z := ⟨⟨hi,D,hD,hx⟩,⟨hi,D,hD,hy⟩,⟨hi,D,hD,hz⟩,mul,hm,hp⟩

theorem product_total {J Domains Muls Units i x y : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hx : At J Domains i x) (hy : At J Domains i y) :
    ∃ z, ProductAt J Domains Muls i x y z := by
  obtain ⟨D,mul,e,hD,hm,_,hMon⟩ := family_at hF hx.1
  have hxD := domain_mem hF hD hx
  have hyD := domain_mem hF hD hy
  obtain ⟨z,hz,hp⟩ := (hMon.2.1 x hxD).1 y hyD
  exact ⟨z,product_mk hx.1 hD hm hxD hyD hz hp⟩

theorem product_unique {J Domains Muls Units i x y z zz : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hp : ProductAt J Domains Muls i x y z)
    (hq : ProductAt J Domains Muls i x y zz) : z = zz := by
  obtain ⟨D,mul,e,hD,hm,_,hMon⟩ := family_at hF hp.1.1
  obtain ⟨hx,hy,_,hp'⟩ := product_data hF hD hm hp
  obtain ⟨_,_,_,hq'⟩ := product_data hF hD hm hq
  exact (hMon.2.1 x hx).2.1 y z zz hy hp' hq'

theorem product_left_cancel {J Domains Muls Units i x y z out : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hp : ProductAt J Domains Muls i x y out)
    (hq : ProductAt J Domains Muls i x z out) : y = z := by
  obtain ⟨D,mul,e,hD,hm,_,hMon⟩ := family_at hF hp.1.1
  obtain ⟨hx,hy,_,hp'⟩ := product_data hF hD hm hp
  obtain ⟨_,hz,_,hq'⟩ := product_data hF hD hm hq
  exact (hMon.2.1 x hx).2.2 y z out hy hz hp' hq'

theorem product_assoc {J Domains Muls Units i x y z xy yz out : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hp : ProductAt J Domains Muls i x y xy)
    (hq : ProductAt J Domains Muls i y z yz) (hr : ProductAt J Domains Muls i xy z out) :
    ProductAt J Domains Muls i x yz out := by
  obtain ⟨D,mul,e,hD,hm,_,hMon⟩ := family_at hF hp.1.1
  obtain ⟨hx,hy,_,hp'⟩ := product_data hF hD hm hp
  obtain ⟨_,hz,hyz,hq'⟩ := product_data hF hD hm hq
  obtain ⟨_,_,hout,hr'⟩ := product_data hF hD hm hr
  exact product_mk hp.1.1 hD hm hx hyz hout ((hMon.2.2 x y z xy yz out hx hy hz hp' hq').mp hr')

theorem unit_total {J Domains Muls Units i : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ e, UnitAt J Domains Units i e := by
  obtain ⟨D,mul,e,hD,_,he,hMon⟩ := family_at hF hi
  exact ⟨e,⟨hi,D,hD,hMon.1.1⟩,he⟩

theorem unit_unique {J Domains Units i e ee : M.Carrier .set}
    (hU : FunctionOn J Units) (he : UnitAt J Domains Units i e) (hee : UnitAt J Domains Units i ee) : e = ee :=
  function_unique hU he.2 hee.2

theorem unit_left {J Domains Muls Units i e x : M.Carrier .set}
    (hF : Family J Domains Muls Units) (he : UnitAt J Domains Units i e) (hx : At J Domains i x) :
    ProductAt J Domains Muls i e x x := by
  obtain ⟨D,mul,e',hD,hm,he',hMon⟩ := family_at hF hx.1
  have heq := function_unique hF.2.2.1 he' he.2
  subst e'
  have hxD := domain_mem hF hD hx
  exact product_mk hx.1 hD hm hMon.1.1 hxD hxD (((hMon.1.2 x hxD x).1).mpr rfl)

theorem unit_right {J Domains Muls Units i e x : M.Carrier .set}
    (hF : Family J Domains Muls Units) (he : UnitAt J Domains Units i e) (hx : At J Domains i x) :
    ProductAt J Domains Muls i x e x := by
  obtain ⟨D,mul,e',hD,hm,he',hMon⟩ := family_at hF hx.1
  have heq := function_unique hF.2.2.1 he' he.2
  subst e'
  have hxD := domain_mem hF hD hx
  exact product_mk hx.1 hD hm hxD hMon.1.1 hxD (((hMon.1.2 x hxD x).2).mpr rfl)

theorem product_conical {J Domains Muls Units i x y e : M.Carrier .set}
    (hF : Family J Domains Muls Units) (hCon : ConicalFamily J Domains Muls Units)
    (he : UnitAt J Domains Units i e) (hp : ProductAt J Domains Muls i x y e) : x = e ∧ y = e := by
  obtain ⟨D,mul,e',hD,hm,he',_⟩ := family_at hF he.1.1
  have heq := function_unique hF.2.2.1 he' he.2
  subst e'
  obtain ⟨hx,hy,_,hp'⟩ := product_data hF hD hm hp
  exact hCon i D mul e he.1.1 hD hm he' x y hx hy hp'

def family {m : Nat} (J Domains Muls Units : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains J)) (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.functionOn Muls J)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn Units J)) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge ((((Domains).succ).succ).succ).succ ((((0 : Fin
  (m+1))).succ).succ).succ (((0 : Fin (m+2))).succ).succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge ((((Muls).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ ((0 :
  Fin (m+3))).succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  ((((Units).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ (0 : Fin (m+4))))
  (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (((0 : Fin (m+2))).succ).succ ((0 : Fin
  (m+3))).succ (0 : Fin (m+4))))))))))))))

theorem family_freeClosed {m : Nat} (J Domains Muls Units : Fin m) : (family J Domains Muls Units).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Units : Fin m) :
    Project.Formula.satisfies env (family J Domains Muls Units) ↔ Family (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M)]
  rfl

def productAt {m : Nat} (J Domains Muls i x y z : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionDirectedSystem.atStage J Domains i x) (.conj (ConstructionDirectedSystem.atStage J
  Domains i y) (.conj (ConstructionDirectedSystem.atStage J Domains i z) (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge (Muls).succ (i).succ (0 : Fin (m+1))))
  (ProjectSyntax.encode id (ForcingDiagramOrder.product (0 : Fin (m+1)) (x).succ (y).succ (z).succ)))))))

theorem productAt_freeClosed {m : Nat} (J Domains Muls i x y z : Fin m) : (productAt J Domains Muls i x y z).FreeClosed := by
  simp -implicitDefEqProofs [productAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.atStage_freeClosed]

theorem productAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls i x y z : Fin m) :
    Project.Formula.satisfies env (productAt J Domains Muls i x y z) ↔ ProductAt (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound i) (env.bound x) (env.bound y) (env.bound z) := by
  simp only [productAt,ProductAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),ConstructionDirectedSystem.atStage_semantics hM]
  rfl

def unitAt {m : Nat} (J Domains Units i e : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionDirectedSystem.atStage J Domains i e) (ProjectSyntax.encode id
  (Source.SetLanguage.edge Units i e)))

theorem unitAt_freeClosed {m : Nat} (J Domains Units i e : Fin m) : (unitAt J Domains Units i e).FreeClosed := by
  simp -implicitDefEqProofs [unitAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.atStage_freeClosed]

theorem unitAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Units i e : Fin m) :
    Project.Formula.satisfies env (unitAt J Domains Units i e) ↔ UnitAt (env.bound J) (env.bound Domains) (env.bound Units) (env.bound i) (env.bound e) := by
  simp only [unitAt,UnitAt,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedSystem.atStage_semantics hM]
  rfl

def homLaws {m : Nat} (J E Domains F Muls Units : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  ((((((((E).succ).succ).succ).succ).succ).succ).succ).succ ((((((((0 : Fin
  (m+1))).succ).succ).succ).succ).succ).succ).succ (((((((0 : Fin
  (m+2))).succ).succ).succ).succ).succ).succ)) (.imp (productAt
  ((((((((J).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Domains).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Muls).succ).succ).succ).succ).succ).succ).succ).succ ((((((((0 : Fin
  (m+1))).succ).succ).succ).succ).succ).succ).succ ((((((0 : Fin (m+3))).succ).succ).succ).succ).succ
  (((((0 : Fin (m+4))).succ).succ).succ).succ ((((0 : Fin (m+5))).succ).succ).succ) (.imp
  (ConstructionDirectedSystem.transition ((((((((J).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Domains).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((F).succ).succ).succ).succ).succ).succ).succ).succ ((((((((0 : Fin
  (m+1))).succ).succ).succ).succ).succ).succ).succ (((((((0 : Fin
  (m+2))).succ).succ).succ).succ).succ).succ ((((((0 : Fin (m+3))).succ).succ).succ).succ).succ (((0 :
  Fin (m+6))).succ).succ) (.imp (ConstructionDirectedSystem.transition
  ((((((((J).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Domains).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((F).succ).succ).succ).succ).succ).succ).succ).succ ((((((((0 : Fin
  (m+1))).succ).succ).succ).succ).succ).succ).succ (((((((0 : Fin
  (m+2))).succ).succ).succ).succ).succ).succ (((((0 : Fin (m+4))).succ).succ).succ).succ ((0 : Fin
  (m+7))).succ) (.imp (ConstructionDirectedSystem.transition
  ((((((((J).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Domains).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((F).succ).succ).succ).succ).succ).succ).succ).succ ((((((((0 : Fin
  (m+1))).succ).succ).succ).succ).succ).succ).succ (((((((0 : Fin
  (m+2))).succ).succ).succ).succ).succ).succ ((((0 : Fin (m+5))).succ).succ).succ (0 : Fin (m+8)))
  (productAt ((((((((J).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Domains).succ).succ).succ).succ).succ).succ).succ).succ
  ((((((((Muls).succ).succ).succ).succ).succ).succ).succ).succ (((((((0 : Fin
  (m+2))).succ).succ).succ).succ).succ).succ (((0 : Fin (m+6))).succ).succ ((0 : Fin (m+7))).succ (0 :
  Fin (m+8)))))))))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge ((((E).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ (((0 : Fin
  (m+2))).succ).succ)) (.imp (unitAt ((((J).succ).succ).succ).succ ((((Domains).succ).succ).succ).succ
  ((((Units).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ ((0 : Fin (m+3))).succ) (.imp
  (ConstructionDirectedSystem.transition ((((J).succ).succ).succ).succ
  ((((Domains).succ).succ).succ).succ ((((F).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ
  (((0 : Fin (m+2))).succ).succ ((0 : Fin (m+3))).succ (0 : Fin (m+4))) (unitAt
  ((((J).succ).succ).succ).succ ((((Domains).succ).succ).succ).succ ((((Units).succ).succ).succ).succ
  (((0 : Fin (m+2))).succ).succ (0 : Fin (m+4)))))))))))

theorem homLaws_freeClosed {m : Nat} (J E Domains F Muls Units : Fin m) : (homLaws J E Domains F Muls Units).FreeClosed := by
  simp -implicitDefEqProofs [homLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,productAt_freeClosed,unitAt_freeClosed,ConstructionDirectedSystem.transition_freeClosed]

theorem homLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Units : Fin m) :
    Project.Formula.satisfies env (homLaws J E Domains F Muls Units) ↔ HomLaws (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) := by
  simp only [homLaws,HomLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,productAt_semantics hM,unitAt_semantics hM,ConstructionDirectedSystem.transition_semantics hM]
  rfl

def conicalFamily {m : Nat} (J Domains Muls Units : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound ((((0 : Fin (m+1))).succ).succ).succ) (.bound
  ((((J).succ).succ).succ).succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  ((((Domains).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ (((0 : Fin
  (m+2))).succ).succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  ((((Muls).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ ((0 : Fin (m+3))).succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge ((((Units).succ).succ).succ).succ ((((0 : Fin
  (m+1))).succ).succ).succ (0 : Fin (m+4)))) (ProjectSyntax.encode id (ForcingDiagramPoset.conical (((0 :
  Fin (m+2))).succ).succ ((0 : Fin (m+3))).succ (0 : Fin (m+4))))))))))))

theorem conicalFamily_freeClosed {m : Nat} (J Domains Muls Units : Fin m) : (conicalFamily J Domains Muls Units).FreeClosed := by
  simp -implicitDefEqProofs [conicalFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem conicalFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Units : Fin m) :
    Project.Formula.satisfies env (conicalFamily J Domains Muls Units) ↔ ConicalFamily (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) := by
  simp only [conicalFamily,ConicalFamily,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramPoset.conical_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionDirectedMonoidData

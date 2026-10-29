/- Pinned PersistentCodes.Works/works_mono:122-136.
The existing actual families, component and quotient are rebound at EVERY
principal condition. No new family or quotient backend is introduced. -/
import PPAC.Migration.ForcingPersistentCodes

namespace PPAC.Migration.ForcingPersistentWorks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Bundle {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr : M.Carrier .set) : Prop :=
  MapsTo (v 4) objImage objects ∧
  ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects ∧
  ForcingEligibleMapFamily.Arrows (v 0) mul (v 4) S ∧ MapsTo S mapImage maps ∧
  ForcingEligibleMapFamily.Family R Hdom env v G F mul g q bound labels E S maps ∧
  ForcingComponentGluing.Component (v 0) I mul q objects maps root P ∧ MapsTo P Q gluePr ∧
  ForcingComponentGluing.Classes (v 0) I mul q objects maps P Q ∧
  ForcingComponentGluing.Projection (v 0) I mul q objects maps P gluePr

def bundle {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) objImage))
    (.conj (ProjectSyntax.encode id (ForcingEligibleFamily.family R Hdom base rho G F mul g q bound labels E (rho 4) objects))
    (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul (rho 4) S))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.family R Hdom base rho G F mul g q bound labels E S maps))
    (.conj (ForcingComponentGluing.component (rho 0) I mul q objects maps root P)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo gluePr P Q))
    (.conj (ForcingComponentGluing.classes (rho 0) I mul q objects maps P Q)
    (ForcingComponentGluing.projection (rho 0) I mul q objects maps P gluePr)))))))))

theorem bundle_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr : Fin m) :
    (bundle R Hdom base rho I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr).FreeClosed := by
  simp [bundle,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentGluing.component_freeClosed,ForcingComponentGluing.classes_freeClosed,ForcingComponentGluing.projection_freeClosed]

theorem bundle_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr : Fin m) :
    Project.Formula.satisfies env (bundle R Hdom base rho I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr) ↔
      Bundle R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound g) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound root) (env.bound objImage) (env.bound objects) (env.bound S) (env.bound mapImage) (env.bound maps) (env.bound P) (env.bound Q) (env.bound gluePr) := by
  simp only [bundle,Bundle,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingComponentGluing.component_semantics hM,ForcingComponentGluing.classes_semantics hM,ForcingComponentGluing.projection_semantics hM]
  rfl

theorem assemble_at_filter (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root : Fin k) (g : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g) :
    ∃ objImage objects S mapImage maps P Q gluePr,
      Bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) g (env q) (env bound) (env labels) (env E) (env root)
        objImage objects S mapImage maps P Q gluePr := by
  obtain ⟨objImage,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family_over hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (Fin.lastCases g env)
    Fin.castSucc (fun j => (rho j).castSucc) G.castSucc F.castSucc mul.castSucc (Fin.last k)
    q.castSucc bound.castSucc labels.castSucc E.castSucc I.castSucc (rho 4).castSucc
    (by simpa only [Fin.lastCases_castSucc] using hp.2.2.2.1)
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last] at hObjMap hObj
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM env (rho 0) mul (rho 4)
  obtain ⟨mapImage,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family_at_filter hM env rho G F mul
    I K B w one q bound labels E g S hm hp hg hS
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (env (rho 0)) (env I) (env mul) (env q)
  obtain ⟨image,fibers,hFibers,hFamily⟩ := ForcingComponentFibers.exists_family hM hp.2.2.2.1 hObjMap hVertices
  obtain ⟨A,hA⟩ := ForcingComponentMatches.exists_carrier hM hVertices hFibers hFamily
  obtain ⟨P,hP⟩ := ForcingComponentGluing.exists_component hM hA (root := env root)
  obtain ⟨Q,gluePr,hpr,hQ,hProjection⟩ := ForcingComponentGluing.exists_quotient hM
    (env (rho 0)) (env I) (env mul) (env q) objects maps P
  exact ⟨objImage,objects,S,mapImage,maps,P,Q,gluePr,hObjMap,hObj,hS,hMap,hMaps,hP,hpr,hQ,hProjection⟩


theorem assemble (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w one G F mul g q bound labels E root : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) (env g)) :
    ∃ objImage objects S mapImage maps P Q gluePr,
      Bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) (env g) (env q) (env bound) (env labels) (env E) (env root)
        objImage objects S mapImage maps P Q gluePr := by
  exact assemble_at_filter hM env rho I K B w one G F mul q bound labels E root (env g) hm hp hg

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul g q bound labels E root : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => j.succ.succ.succ.succ.succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ.succ.succ.succ.succ) I.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ g.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ bound.succ.succ.succ.succ.succ.succ.succ.succ labels.succ.succ.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 4 3 2 1 0))))))))))))
  freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,bundle_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul g q bound labels E root : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w one G F mul g q bound labels E root)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),bundle_semantics hM]
  exact assemble hM env rho I K B w one G F mul g q bound labels E root

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul g q bound labels E root : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w one G F mul g q bound labels E root)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w one G F mul g q bound labels E root hM)

/-- PersistentCodes.works_covariance uses this presentation at every stronger
condition. Only the filter varies; R, Hdom and their ambient parameters stay fixed. -/
theorem assemble_principal (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root : Fin k) {d : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) :
    ∃ g objImage objects S mapImage maps P Q gluePr,
      ForcingPrincipalFilter.Principal (env (rho 3)) d g ∧
      Bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) g (env q) (env bound) (env labels) (env E) (env root)
        objImage objects S mapImage maps P Q gluePr := by
  obtain ⟨g,hg⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) d
  obtain ⟨oi,objects,S,mi,maps,P,Q,pr,hB⟩ := assemble_at_filter hM env rho
    I K B w one G F mul q bound labels E root g hm hp (ForcingPrincipalFilter.principal_filter hd hg)
  exact ⟨g,oi,objects,S,mi,maps,P,Q,pr,hg,hB⟩

def principalSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root d : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+9) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Project.Formula.forallClosure k
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (.mem (.bound d) (.bound (rho 3)))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
        (.conj (ForcingPrincipalFilter.principal (up (rho 3)) (up d) 8)
          (bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun j => up (rho j))
            (up I) (up G) (up F) (up mul) 8 (up q) (up bound) (up labels) (up E) (up root)
            7 6 5 4 3 2 1 0))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingPrincipalFilter.principal_freeClosed,bundle_freeClosed]

theorem principal_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root d : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (principalSentence rho I K B w one G F mul q bound labels E root d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingPrincipalFilter.principal_semantics (M := M),bundle_semantics hM]
  exact assemble_principal hM env rho I K B w one G F mul q bound labels E root

theorem principal_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w one G F mul q bound labels E root d : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (principalSentence rho I K B w one G F mul q bound labels E root d)) :=
  ModelTransfer.derives (fun _ hM => principal_models rho I K B w one G F mul q bound labels E root d hM)

def Represented {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (I G F mul q bound labels E root w chain d a : M.Carrier .set) : Prop :=
  ∃ g objImage objects S mapImage maps P Q gluePr b,
    ForcingPrincipalFilter.Principal (v 3) d g ∧
    Bundle R Hdom env v I G F mul g q bound labels E root objImage objects S mapImage maps P Q gluePr ∧
    (Project.FirstOrderSemantics.reduct M).mem b Q ∧
    ForcingTailCodes.Represents R Hdom env v I G F mul g q bound labels E objects maps root gluePr w chain a b

def Works {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (I G F mul q bound labels E root w chain d a : M.Carrier .set) : Prop :=
  ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (v 3) → ForcingPowerName.Subset d e →
    Represented R Hdom env v I G F mul q bound labels E root w chain e a

theorem works_mono {k : Nat} {R : Formula (k+2)} {Hdom : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul q bound labels E root w chain d e a : M.Carrier .set}
    (hde : ForcingPowerName.Subset d e) (h : Works R Hdom env v I G F mul q bound labels E root w chain d a) :
    Works R Hdom env v I G F mul q bound labels E root w chain e a :=
  fun f hf hef => h f hf (fun z hz => hef z (hde z hz))


def represented {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingPrincipalFilter.principal (rho 3).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9)
    (.conj (bundle R Hdom (fun j => (base j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ bound.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ labels.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7 6 5 4 3 2 1)
      (.conj (.mem (.bound 0) (.bound 2))
        (ForcingTailCodes.represents R Hdom (fun j => (base j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ bound.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ labels.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 4 root.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0))))))))))))))

theorem represented_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) :
    (represented R Hdom base rho I G F mul q bound labels E root w chain d a).FreeClosed := by
  simp [represented,Definitional.Formula.FreeClosed,ForcingPrincipalFilter.principal_freeClosed,
    bundle_freeClosed,ForcingTailCodes.represents_freeClosed]

theorem represented_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) :
    Project.Formula.satisfies env (represented R Hdom base rho I G F mul q bound labels E root w chain d a) ↔
    Represented R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound root) (env.bound w) (env.bound chain) (env.bound d) (env.bound a) := by
  simp only [represented,Represented,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ForcingPrincipalFilter.principal_semantics,
    bundle_semantics hM,ForcingTailCodes.represents_semantics hM]
  rfl

def works {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ))
    (.imp (Project.Formula.subset (.bound d.succ) (.bound 0))
      (represented R Hdom (fun j => (base j).succ) (fun j => (rho j).succ) I.succ G.succ F.succ mul.succ q.succ bound.succ labels.succ E.succ root.succ w.succ chain.succ 0 a.succ)))

theorem works_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) :
    (works R Hdom base rho I G F mul q bound labels E root w chain d a).FreeClosed := by
  simp [works,Definitional.Formula.FreeClosed,represented_freeClosed]

theorem works_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul q bound labels E root w chain d a : Fin m) :
    Project.Formula.satisfies env (works R Hdom base rho I G F mul q bound labels E root w chain d a) ↔
    Works R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound root) (env.bound w) (env.bound chain) (env.bound d) (env.bound a) := by
  simp only [works,Works,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,represented_semantics hM]
  rfl


-- Exact families and class graphs fix the represented quotient, independently
-- of any chosen functional-image bound used during construction.
theorem bundle_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E root oi objects S mi maps P Q pr oi' objects' S' mi' maps' P' Q' pr' : M.Carrier .set}
    (h : Bundle R Hdom env v I G F mul g q bound labels E root oi objects S mi maps P Q pr)
    (h' : Bundle R Hdom env v I G F mul g q bound labels E root oi' objects' S' mi' maps' P' Q' pr') :
    objects = objects' ∧ S = S' ∧ maps = maps' ∧ P = P' ∧ Q = Q' ∧ pr = pr' := by
  obtain ⟨ho,hO,hS,hm,hMaps,hP,hpr,hQ,hPr⟩ := h
  obtain ⟨ho',hO',hS',hm',hMaps',hP',hpr',hQ',hPr'⟩ := h'
  have heO : objects = objects' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp ho).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp ho').1.1
    (fun r O => (hO r O).trans (hO' r O).symm)
  subst objects'
  have heS := (ModelTransfer.extensionality hM).eq_of_same_members S S' (fun z => (hS z).trans (hS' z).symm)
  subst S'
  have heMaps : maps = maps' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp hm).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp hm').1.1
    (fun z a => (hMaps z a).trans (hMaps' z a).symm)
  subst maps'
  have heP := (ModelTransfer.extensionality hM).eq_of_same_members P P' (fun z => (hP z).trans (hP' z).symm)
  subst P'
  have heQ := (ModelTransfer.extensionality hM).eq_of_same_members Q Q' (fun z => (hQ z).trans (hQ' z).symm)
  subst Q'
  have hePr : pr = pr' := SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff
    (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp hpr).1.1
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp hpr').1.1
    (fun x y => (hPr x y).trans (hPr' x y).symm)
  exact ⟨rfl,rfl,rfl,rfl,rfl,hePr⟩

theorem represented_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E root w chain d a oi objects S mi maps P Q pr : M.Carrier .set}
    (hg : ForcingPrincipalFilter.Principal (v 3) d g)
    (hB : Bundle R Hdom env v I G F mul g q bound labels E root oi objects S mi maps P Q pr) :
    Represented R Hdom env v I G F mul q bound labels E root w chain d a ↔
    ∃ b, (Project.FirstOrderSemantics.reduct M).mem b Q ∧
      ForcingTailCodes.Represents R Hdom env v I G F mul g q bound labels E objects maps root pr w chain a b := by
  constructor
  · rintro ⟨g',oi',objects',S',mi',maps',P',Q',pr',b,hg',hB',hb,ha⟩
    have he := ForcingPrincipalFilter.principal_unique hM hg hg'
    subst g'
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := bundle_unique hM hB hB'
    exact ⟨b,hb,ha⟩
  · rintro ⟨b,hb,ha⟩
    exact ⟨g,oi,objects,S,mi,maps,P,Q,pr,b,hg,hB,hb,ha⟩


def representationSentence {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ForcingPrincipalFilter.principal (rho 3) d g)
      (.imp (bundle R Hdom id rho I G F mul g q bound labels E root oi objects S mi maps P Q pr)
        (.iff (represented R Hdom id rho I G F mul q bound labels E root w chain d a) (.existsE (.conj (.mem (.bound 0) (.bound Q.succ)) (ForcingTailCodes.represents R Hdom (fun j => j.succ) (fun j => (rho j).succ) I.succ G.succ F.succ mul.succ g.succ q.succ bound.succ labels.succ E.succ objects.succ maps.succ root.succ pr.succ w.succ chain.succ a.succ 0))))))
  freeClosed := by simp [Definitional.Formula.FreeClosed,ForcingPrincipalFilter.principal_freeClosed,
    bundle_freeClosed,represented_freeClosed,ForcingTailCodes.represents_freeClosed]

theorem representation_models {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (representationSentence R Hdom rho I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,ForcingPrincipalFilter.principal_semantics,bundle_semantics hM,
    represented_semantics hM,ForcingTailCodes.represents_semantics hM]
  intro hg hB
  exact represented_iff hM hg hB

theorem representation_kernel_certificate {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (representationSentence R Hdom rho I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr)) :=
  ModelTransfer.derives (fun _ hM => representation_models R Hdom rho I G F mul q bound labels E root w chain d a g oi objects S mi maps P Q pr hM)

def lower {k : Nat} : Project.Formula 1 (k+2) := Project.Formula.subset (.bound 1) (.bound 0)

def working {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain : Fin k) : Project.Formula 1 (k+2) :=
  works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
    (fun j => j.succ.succ) (fun j => (rho j).succ.succ) I.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ root.succ.succ w.succ.succ chain.succ.succ 0 1

def equalAt {k : Nat} (rho : Fin 7 → Fin k) (mul w chain : Fin k) : Project.Formula 1 (k+3) :=
  ForcingPersistentCodes.same (orderFormula (rho 0) mul) (fun j => j.succ.succ.succ)
    (rho 6).succ.succ.succ w.succ.succ.succ chain.succ.succ.succ 0 1 2

theorem working_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain : Fin k) :
    (working rho I G F mul q bound labels E root w chain).FreeClosed := works_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem equalAt_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (mul w chain : Fin k) :
    (equalAt rho mul w chain).FreeClosed := ForcingPersistentCodes.same_freeClosed _ _ _ _ _ _ _ _

theorem lower_semantics {k : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (p q : M.Carrier .set) :
    ForcingPersistentSelection.Rel2 (lower (k := k)) env p q ↔ ForcingPowerName.Subset q p := by
  simp only [ForcingPersistentSelection.Rel2,lower,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

theorem working_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain : Fin k) (p a : M.Carrier .set) :
    ForcingPersistentSelection.Rel2 (working rho I G F mul q bound labels E root w chain) env p a ↔
      Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env.bound
        (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound root) (env.bound w) (env.bound chain) p a := by
  exact works_semantics hM ((env.push a).push p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem equalAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k)
    (mul w chain : Fin k) (p a b : M.Carrier .set) :
    ForcingPersistentSelection.Rel3 (equalAt rho mul w chain) env p a b ↔
      ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env.bound
        (env.bound (rho 6)) (env.bound w) (env.bound chain) p a b := by
  exact ForcingPersistentCodes.same_semantics hM (((env.push b).push a).push p) _ _ _ _ _ _ _ _


-- Concrete ChainCode.Selected: the generic laws are discharged by actual
-- condition inclusion, Works, Same and the already constructed code carrier.
def selectionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul q bound labels E root zero vertices chain names codes order : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (ForcingPersistentSelection.conclusion lower (working rho I G F mul q bound labels E root w chain) (equalAt rho mul w chain) id (rho 3) codes order)))))))
  freeClosed := by
    simp [ForcingPersistentSelection.conclusion,ForcingPersistentSelection.selected,
      ForcingPersistentSelection.rel2,ForcingPersistentSelection.rel3,lower,
      Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,working_freeClosed,equalAt_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.carrier_freeClosed]
    exact ⟨Project.Formula.isOmega_freeClosed _ rfl,
      Project.Formula.isSetCodedWellOrder_freeClosed _ _ _ rfl rfl⟩

theorem selection_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul q bound labels E root zero vertices chain names codes order : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectionSentence rho I K B w one G F mul q bound labels E root zero vertices chain names codes order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM]
  intro hm hp hw hChain hCodes hWO
  have hLaws : Project.Formula.satisfies ({bound := env,free := free} : SetTheory.Env _ k)
      (ForcingPersistentSelection.laws lower (working rho I G F mul q bound labels E root w chain) (equalAt rho mul w chain) id (rho 3) codes) := by
    simp only [ForcingPersistentSelection.laws,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
      Project.Term.eval_bound,ForcingPersistentSelection.rel2_semantics,ForcingPersistentSelection.rel3_semantics,
      lower_semantics,working_semantics hM,equalAt_semantics hM]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · intro p _ z hz
      exact hz
    · intro p r t _ _ _ hpr hrt z hz
      exact hpr z (hrt z hz)
    · intro p r a _ _ _ hpr ha
      exact works_mono hpr ha
    · intro p r a b hp' _ _ _ hpr hab
      exact ForcingPersistentCodes.same_mono hM env rho mul hm hp hChain hp' hpr hab
    · intro p a hp' ha
      exact ForcingPersistentCodes.same_refl hM env rho mul hm hp hw hChain ((hCodes a).mp ha).1 hp'
    · intro p a b _ _ _ hab
      exact ForcingPersistentCodes.same_symm hM hab
    · intro p a b c hp' _ hb _ hab hbc
      exact ForcingPersistentCodes.same_trans hM env rho mul hm hp hw hChain ((hCodes b).mp hb).1 hp' hab hbc
  have general := ForcingPersistentSelection.selection_models lower (working rho I G F mul q bound labels E root w chain) (equalAt rho mul w chain)
    (by simp [lower]) (working_freeClosed rho I G F mul q bound labels E root w chain) (equalAt_freeClosed rho mul w chain)
    id (rho 3) codes order hM
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff] at general
  have supplied := (Project.Formula.satisfies_forallClosure_iff free _).mp (general free) env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound] at supplied
  exact supplied hWO hLaws

theorem selection_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w one G F mul q bound labels E root zero vertices chain names codes order : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectionSentence rho I K B w one G F mul q bound labels E root zero vertices chain names codes order)) :=
  ModelTransfer.derives (fun _ hM => selection_models rho I K B w one G F mul q bound labels E root zero vertices chain names codes order hM)

end PPAC.Migration.ForcingPersistentWorks

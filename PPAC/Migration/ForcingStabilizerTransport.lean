/- Pinned HS.smul: transport actual stabilizers through conjugation, then
apply the conjugation clause of the normal filter. All hypotheses concern
condition graphs, group-code permutations and filter membership, never HS or
forced target axioms. Concrete ProductNames.actionHom must supply these data. -/
import PPAC.Migration.ForcingNameConjugacy

namespace PPAC.Migration.ForcingStabilizerTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Action Fixed Stabilizer Symmetric)
open ForcingConditionGraphs (Permutation Endomap InverseGraph)
open ForcingNameConjugacy (Conjugate)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source action supplies a condition permutation at every group code. -/
def Family {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set) (G P : M.Carrier .set) : Prop :=
  (∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G → ∃ r, MapRel A params g r) ∧
  (∀ g r, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G → MapRel A params g r → Permutation P r)

def family {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last m) G.castSucc).imp (.ex
    (ReplacementPredicates.rel A (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1)))))).conj
  (.all (.all ((Formula.mem (Fin.last m).castSucc G.castSucc.castSucc).imp
    ((ReplacementPredicates.rel A (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (ForcingConditionGraphs.permutation P.castSucc.castSucc (Fin.last (m+1)))))))

theorem family_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (family A rho G P) ↔
      Family A (fun i => env (rho i)) (env G) (env P) := by
  simp only [family,Family,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Action-homomorphism conjugacy, stated solely on the actual condition graphs. -/
def Covariance {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P c r i : M.Carrier .set) : Prop :=
  ∀ g h s t, (Definitional.Project.FirstOrderSemantics.reduct M).mem g G →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem h G → PureKuratowski.PairMember M g h c →
    MapRel A params g s → MapRel A params h t → Conjugate P r i s t

def covariance {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P c r i : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun j => j.castSucc.castSucc.castSucc.castSucc
  let g := (Fin.last m).castSucc.castSucc.castSucc
  let h := (Fin.last (m+1)).castSucc.castSucc
  let s := (Fin.last (m+2)).castSucc
  let t := Fin.last (m+3)
  .all (.all (.all (.all ((Formula.mem g (up G)).imp ((Formula.mem h (up G)).imp
    ((Source.SetLanguage.edge (up c) g h).imp ((ReplacementPredicates.rel A (fun j => up (rho j)) g s).imp
      ((ReplacementPredicates.rel A (fun j => up (rho j)) h t).imp
        (ForcingNameConjugacy.conjugate (up P) (up r) (up i) s t)))))))))

theorem covariance_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P c r i : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (covariance A rho G P c r i) ↔
      Covariance A (fun j => env (rho j)) (env G) (env P) (env c) (env r) (env i) := by
  simp only [covariance,Covariance,Formula.Realize,KuratowskiZF.source_edge,ForcingMapConditions.rel_semantics (M := M),
    ForcingNameConjugacy.conjugate_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def image {m : Nat} (c S T : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) T.castSucc).iff (.ex
    ((Formula.mem (Fin.last (m+1)) S.castSucc.castSucc).conj
      (Source.SetLanguage.edge c.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))

def Image (c S T : M.Carrier .set) : Prop :=
  ∀ h, (Definitional.Project.FirstOrderSemantics.reduct M).mem h T ↔
    ∃ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g S ∧ PureKuratowski.PairMember M g h c

theorem image_semantics {m : Nat} (env : Fin m → M.Carrier .set) (c S T : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (image c S T) ↔
      Image (env c) (env S) (env T) := by
  simp only [image,Image,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

/-- One instance of the original normal-filter conjugation clause. -/
def NormalImage (F c : M.Carrier .set) : Prop :=
  ∀ S T, (Definitional.Project.FirstOrderSemantics.reduct M).mem S F → Image c S T →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem T F

def normalImage {m : Nat} (F c : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc F.castSucc.castSucc).imp
    ((image c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.mem (Fin.last (m+1)) F.castSucc.castSucc))))

theorem normalImage_semantics {m : Nat} (env : Fin m → M.Carrier .set) (F c : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (normalImage F c) ↔
      NormalImage (env F) (env c) := by
  simp only [normalImage,NormalImage,Formula.Realize,image_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- No name/stabilizer/HS preservation assertion occurs in this algebraic context. -/
def Context {k : Nat} (A : Formula (k+2)) (params : Fin k → M.Carrier .set)
    (G P F c r i : M.Carrier .set) : Prop :=
  Family A params G P ∧ Permutation G c ∧ Permutation P r ∧ Endomap P i ∧ InverseGraph r i ∧
    Covariance A params G P c r i ∧ NormalImage F c

def context {k m : Nat} (A : Formula (k+2)) (rho : Fin k → Fin m) (G P F c r i : Fin m) : Formula m :=
  (family A rho G P).conj ((ForcingConditionGraphs.permutation G c).conj
    ((ForcingConditionGraphs.permutation P r).conj ((ForcingConditionGraphs.endomap P i).conj
      ((ForcingConditionGraphs.inverseGraph r i).conj ((covariance A rho G P c r i).conj (normalImage F c))))))

theorem context_semantics {k m : Nat} (env : Fin m → M.Carrier .set) (A : Formula (k+2))
    (rho : Fin k → Fin m) (G P F c r i : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (context A rho G P F c r i) ↔
      Context A (fun j => env (rho j)) (env G) (env P) (env F) (env c) (env r) (env i) := by
  simp only [context,Context,Formula.Realize,family_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingConditionGraphs.endomap_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),
    covariance_semantics (M := M),normalImage_semantics (M := M)]

theorem fixed_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P c r i sigma out g h : M.Carrier .set}
    (hf : Family A params G P) (hr : Permutation P r) (hi : Endomap P i) (hri : InverseGraph r i)
    (hc : Covariance A params G P c r i) (hg : (Definitional.Project.FirstOrderSemantics.reduct M).mem g G)
    (hh : (Definitional.Project.FirstOrderSemantics.reduct M).mem h G) (hgh : PureKuratowski.PairMember M g h c)
    (hn : ForcingNames.IsName P sigma) (ha : Action P r sigma out) :
    Fixed A params P sigma g ↔ Fixed A params P out h := by
  constructor
  · rintro ⟨s,hgs,hfix⟩
    obtain ⟨t,hht⟩ := hf.1 h hh
    exact ⟨t,hht,(ForcingNameConjugacy.fixed_conjugacy hM hr hi (hf.2 g s hg hgs).1
      (hf.2 h t hh hht).1 hri (hc g h s t hg hh hgh hgs hht) hn ha).mp hfix⟩
  · rintro ⟨t,hht,hfix⟩
    obtain ⟨s,hgs⟩ := hf.1 g hg
    exact ⟨s,hgs,(ForcingNameConjugacy.fixed_conjugacy hM hr hi (hf.2 g s hg hgs).1
      (hf.2 h t hh hht).1 hri (hc g h s t hg hh hgh hgs hht) hn ha).mpr hfix⟩

theorem stabilizer_image (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P F c r i sigma out S T : M.Carrier .set}
    (hc : Context A params G P F c r i) (hn : ForcingNames.IsName P sigma) (ha : Action P r sigma out)
    (hS : Stabilizer A params G P sigma S) (hT : Stabilizer A params G P out T) : Image c S T := by
  obtain ⟨hf,hcperm,hr,hi,hri,hcov,_⟩ := hc
  intro h
  constructor
  · intro hTmem
    obtain ⟨hh,hfix⟩ := (hT h).mp hTmem
    obtain ⟨g,hg,hgh⟩ := hcperm.2.2 h hh
    exact ⟨g,(hS g).mpr ⟨hg,(fixed_transport hM hf hr hi hri hcov hg hh hgh hn ha).mpr hfix⟩,hgh⟩
  · rintro ⟨g,hgS,hgh⟩
    obtain ⟨hg,hfix⟩ := (hS g).mp hgS
    have hh := hcperm.1.2 g h hgh
    exact (hT h).mpr ⟨hh,(fixed_transport hM hf hr hi hri hcov hg hh hgh hn ha).mp hfix⟩

theorem symmetric_transport (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {A : Formula (k+2)} {params : Fin k → M.Carrier .set} {G P F c r i sigma out : M.Carrier .set}
    (hc : Context A params G P F c r i) (hn : ForcingNames.IsName P sigma) (ha : Action P r sigma out)
    (hs : Symmetric A params G P F sigma) : Symmetric A params G P F out := by
  obtain ⟨S,hS,hSF⟩ := hs
  obtain ⟨T,hT⟩ := ForcingStabilizer.exists_stabilizer hM A params G P out
  exact ⟨T,hT,hc.2.2.2.2.2.2 S T hSF (stabilizer_image hM hc hn ha hS hT)⟩

def sentence {k : Nat} (A : Formula (k+2)) (G P F c r i sigma out : Fin k) : Source.Sentence :=
  ((context A id G P F c r i).imp ((ForcingNames.isName P sigma).imp
    ((ForcingStabilizer.action P r sigma out).imp ((ForcingStabilizer.symmetric A id G P F sigma).imp
      (ForcingStabilizer.symmetric A id G P F out))))).close

theorem models {k : Nat} (A : Formula (k+2)) (G P F c r i sigma out : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence A G P F c r i sigma out)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hc hn ha hs
  exact (ForcingStabilizer.symmetric_semantics (M := M) env A id G P F out).mpr
    (symmetric_transport hM ((context_semantics (M := M) env A id G P F c r i).mp hc)
      ((ForcingNames.isName_semantics (M := M) env P sigma).mp hn)
      ((ForcingStabilizer.action_semantics (M := M) env P r sigma out).mp ha)
      ((ForcingStabilizer.symmetric_semantics (M := M) env A id G P F sigma).mp hs))

theorem kernel_certificate {k : Nat} (A : Formula (k+2)) (G P F c r i sigma out : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence A G P F c r i sigma out)) :=
  ModelTransfer.derives (fun _ hM => models A G P F c r i sigma out hM)

end PPAC.Migration.ForcingStabilizerTransport

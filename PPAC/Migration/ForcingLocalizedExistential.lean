/- Pinned Construction/DiagramPlacements.localized_existential:156-218.
Consume the actual unrestricted-rank witness_placement, existing name support,
diagram coverage and forces_at_supporting_root. No existential/support/density
oracle and no new recursion, choice or forcing backend. -/
import PPAC.Migration.ForcingWitnessPlacement
import PPAC.Migration.ConstructionDiagramCoverage

namespace PPAC.Migration.ForcingLocalizedExistential
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Injection Small)
open ForcingSupportedNames (Range Supported)
open ForcingSupportingRoot (Code)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Restricted Compatible)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem force_reindex {k l n : Nat} (env : Fin k → M.Carrier .set) (other : Fin l → M.Carrier .set)
    (up : Fin k → Fin l) (he : ∀ j, other (up j) = env j) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (phi : Formula n) (v : Fin n → M.Carrier .set) (p : M.Carrier .set) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p phi ↔
      Force (orderFormula (up (rho 0)) (up mul)) (domain (fun j => up (rho j)) (up G) (up F))
        other v (env (rho 6)) p phi := by
  apply ForcingSeparation.force_congr ?_ ?_ phi v _ p
  · intro x y
    simp only [orderFormula_semantics,he]
  · intro x
    simp only [domain_semantics,he]

/-- Literal source localized_existential. Every quantified name has arbitrary
internal rank; the one diagram q is specified before choosing the witness.
Both the strengthened condition and its final support lie on that SAME q. -/
theorem localized_existential (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 : Fin k)
    (phi : Formula (n+1)) (v : Fin n → M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul)
      (env unit) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hp : Injection (env (rho 0)) (env I) (env p)) (hq : Injection (env (rho 0)) (env I) (env q))
    (hSubQ : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hJp : Range (env (rho 0)) (env p) (env Jp)) (hHp : ForcingLabelPermutations.Fixing (env G) (env Jp) (env Hp))
    (hJq : Range (env (rho 0)) (env q) (env Jq)) (hHq : ForcingLabelPermutations.Fixing (env G) (env Jq) (env Hq))
    (hv : ∀ j, Supported (fun i => env (rho i)) (env Hp) (v j))
    (_hd0 : Condition (env (rho 2)) (env w) (env d0)) (hc : Condition (env (rho 2)) (env w) (env c))
    (hc0 : (Project.FirstOrderSemantics.reduct M).MemberSubset (env d0) (env c))
    (hcq : ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) (env c))
    (hz0 : Code (env z0) (env d0) (env p))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) (env z0) (.ex phi)) :
    ∃ a nu out, Condition (env (rho 2)) (env w) a ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset (env c) a ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) a ∧
      ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) nu ∧
      Supported (fun i => env (rho i)) (env Hq) nu ∧ Code out a (env q) ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases nu v) (env (rho 6)) out phi := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hLarge : ¬ Small (env I) (env mu) := fun h =>
    hI.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hqp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env q) (env p) := ⟨env mark,hMark,hSubQ⟩
  obtain ⟨cq,hCq⟩ := ForcingSupportingRoot.exists_code hM (env c) (env q)
  have hCqW := ForcingSupportingRoot.code_mem hPres hc hq hCq
  have hCq0 := (orderFormula_semantics env (rho 0) mul cq (env z0)).mpr
    ((ForcingSupportingRoot.code_le hCq hz0).mpr ⟨hc0,hqp⟩)
  obtain ⟨r,hr,hrcq,tau,hTau,hForce⟩ := (ForcingFormula.force_ex _ _ _ _ _ _ _).mp hf cq hCqW hCq0
  have hTauHS := (domain_semantics env rho G F tau).mp hTau
  obtain ⟨dr,r0,zr,hdr,hr0,hZr,hZrr⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hp hr
  have hZrW := ForcingSupportingRoot.code_mem hPres hdr hr0 hZr
  have hZrr' := (orderFormula_semantics env (rho 0) mul zr r).mpr hZrr
  have hZrcq := hpre.2 zr r cq hZrW hr hCqW hZrr' hrcq
  obtain ⟨hCdr,hR0q⟩ := (ForcingSupportingRoot.code_le hZr hCq).mp
    ((orderFormula_semantics env (rho 0) mul zr cq).mp hZrcq)
  obtain ⟨stabilizer,hStabilizer,hStabilizerF⟩ := ForcingHS.symmetric_of_hs hTauHS
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hFilter stabilizer).mp hStabilizerF
  have hTauSupport : Supported (fun i => env (rho i)) HJ tau := by
    intro pi hpi A hA
    obtain ⟨a,ha,hFixed⟩ := ((hStabilizer pi).mp (hIncluded pi hpi)).2
    have eq := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp ha) ((mapRel_action _ _ _).mp hA)
    exact eq ▸ hFixed
  obtain ⟨s,hs,hSubS,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hr0 hJI hJSmall
  have hSR0 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r0 := ⟨env mark,hMark,hSubS⟩
  have hSP := ForcingDiagramPoset.le_trans hm hSR0 (ForcingDiagramPoset.le_trans hm hR0q hqp)
  obtain ⟨Js,hJs,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hs hD
  obtain ⟨Hs,hHs⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Js
  have hTauS := ForcingSupportedNames.supported_mono hFixJ hHs (fun x hx => (hJs x).mpr (hCover x hx)) hTauSupport
  have hvS : ∀ j, Supported (fun i => env (rho i)) Hs (v j) := fun j =>
    ForcingSupportedNames.supported_mono hHp hHs
      (fun x hx => (hJs x).mpr (ConstructionDescentPlacement.range_antitone hSP ((hJp x).mp hx))) (hv j)
  have hVecS : ∀ j, Supported (fun i => env (rho i)) Hs (Fin.lastCases tau v j) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [Fin.lastCases_last] using hTauS
    · simpa only [Fin.lastCases_castSucc] using hvS j
  obtain ⟨zs,hZs⟩ := ForcingSupportingRoot.exists_code hM dr s
  have hZsW := ForcingSupportingRoot.code_mem hPres hdr hs hZs
  have hZszr := (orderFormula_semantics env (rho 0) mul zs zr).mpr
    ((ForcingSupportingRoot.code_le hZs hZr).mpr ⟨fun _ h => h,hSR0⟩)
  have hZsr := hpre.2 zs zr r hZsW hZrW hr hZszr hZrr'
  have hForceS := ForcingFormula.mono hM hpre phi _ hr hZsW hZsr hForce
  obtain ⟨dR,hdR,hRestrS,hWithinS⟩ := ConstructionCohenCompatibility.exists_restrict hM hdr Js
  obtain ⟨zR,hZR⟩ := ForcingSupportingRoot.exists_code hM dR s
  have hForceR := ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hPres hG hFilter hs hs (ForcingDiagramPoset.le_refl hm hs)
    hdr hJs hHs hRestrS hZs hZR phi (Fin.lastCases tau v) hVecS hForceS
  obtain ⟨b,hb,hSubP⟩ := hSP
  obtain ⟨delta,_,hRestrP,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hdR (env Jp)
  have hRoot : Compatible (env c) delta := by
    intro x bit bit' hx hx'
    obtain ⟨z,hz,hzc⟩ := hx
    obtain ⟨z',hz',hzDelta⟩ := hx'
    exact hdr.2.1 x bit bit' ⟨z,hz,hCdr z hzc⟩
      ⟨z',hz',((hRestrS z').mp ((hRestrP z').mp hzDelta).1).1⟩
  let other : Fin (k+8) → M.Carrier .set := Fin.cases s (Fin.cases b (Fin.cases dR
    (Fin.cases Js (Fin.cases Hs (Fin.cases delta (Fin.cases tau (Fin.cases zR env)))))))
  let up : Fin k → Fin (k+8) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ
  have he j : other (up j) = env j := rfl
  have hSupportDR : ForcingLocalRecordPullback.Supported (env (rho 0)) s dR :=
    fun i j bit h => (hJs i).mp (hWithinS i j bit h)
  have hForceR' := (force_reindex env other up he rho G F mul phi (Fin.lastCases tau v) zR).mp hForceR
  obtain ⟨a,nu,out,ha,hca,hNu,hNuSupport,hOut,hForced⟩ := ForcingWitnessPlacement.witness_placement hM hChoice other
    (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up mu) (up G) (up F) (up mul) (up unit) (up mark)
    (up index) (up p) (up q) 0 1 2 (up c) (up Jp) (up Hp) 3 4 (up Jq) (up Hq) 5 6 7 phi v
    hPres hG hNormal hw hMu hLarge hD hm hMark hProbes hIndex hp hq hs hb hSubQ hSubP
    hJp hHp hJs hHs hJq hHq hv hTauHS hTauS hdR hc hSupportDR hRestrP hRoot hZR hForceR'
  have hForced' := (force_reindex env other up he rho G F mul phi (Fin.lastCases nu v) out).mpr hForced
  obtain ⟨aR,haR,hRestrQ,hWithinQ⟩ := ConstructionCohenCompatibility.exists_restrict hM ha (env Jq)
  have hCaR : (Project.FirstOrderSemantics.reduct M).MemberSubset (env c) aR := by
    intro z hz
    obtain ⟨coord,hCoord,bit,hBit,hCode⟩ := (hPres.2.1 z).mp (hc.1 z hz)
    obtain ⟨i,_,j,_,hCoordCode⟩ := (hPres.1 coord).mp hCoord
    have hi := hcq i j bit ⟨coord,hCoordCode,z,hCode,hz⟩
    exact (hRestrQ z).mpr ⟨hca z hz,i,⟨coord,j,bit,hCode,hCoordCode⟩,(hJq i).mpr hi⟩
  have hSupportAR : ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) aR :=
    fun i j bit h => (hJq i).mp (hWithinQ i j bit h)
  have hvQ : ∀ j, Supported (fun i => env (rho i)) (env Hq) (v j) := fun j =>
    ForcingSupportedNames.supported_mono hHp hHq
      (fun x hx => (hJq x).mpr (ConstructionDescentPlacement.range_antitone hqp ((hJp x).mp hx))) (hv j)
  have hVecQ : ∀ j, Supported (fun i => env (rho i)) (env Hq) (Fin.lastCases nu v j) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [he,Fin.lastCases_last] using hNuSupport
    · simpa only [Fin.lastCases_castSucc] using hvQ j
  obtain ⟨final,hFinal⟩ := ForcingSupportingRoot.exists_code hM aR (env q)
  have hFinalForce := ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hPres hG hFilter hq hq (ForcingDiagramPoset.le_refl hm hq)
    ha hJq hHq hRestrQ hOut hFinal phi (Fin.lastCases nu v) hVecQ hForced'
  exact ⟨aR,nu,final,haR,hCaR,hSupportAR,hNu,hNuSupport,hFinal,hFinalForce⟩

private theorem lastCases_map {a : Type v1} {b : Type v2} {n : Nat} (f : a → b) (x : a) (v : Fin n → a) :
    (fun j => f (Fin.lastCases x v j)) = Fin.lastCases (f x) (fun j => f (v j)) := by
  funext j
  refine Fin.lastCases ?_ (fun _ => ?_) j <;>
    simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Actual strengthened Cohen condition, its q-support, and the unrestricted
HS witness with exact q-stabilizer and full formula forcing. -/
def resultFormula {k n : Nat} (rho : Fin 7 → Fin k) (G F w q c Hq mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  .existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 2))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset (up c) 2))
        (.conj (ForcingLocalRecordPullback.supported (up (rho 0)) (up q) 2)
          (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 1))
            (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => up (rho j)) (up Hq) 1))
              (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 2 (up q)))
                (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
                  (Fin.lastCases 1 (fun j => up (v j))) (up (rho 6)) 0 phi))))))))))

theorem resultFormula_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (G F w q c Hq mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    (resultFormula rho G F w q c Hq mul v phi).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingLocalRecordPullback.supported_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k) (G F w q c Hq mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    Project.Formula.satisfies env (resultFormula rho G F w q c Hq mul v phi) ↔
      ∃ a nu out, Condition (env.bound (rho 2)) (env.bound w) a ∧
        (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound c) a ∧
        ForcingLocalRecordPullback.Supported (env.bound (rho 0)) (env.bound q) a ∧
        ForcingHS.HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) nu ∧
        Supported (fun j => env.bound (rho j)) (env.bound Hq) nu ∧ Code out a (env.bound q) ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env.bound
          (Fin.lastCases nu (fun j => env.bound (v j))) (env.bound (rho 6)) out phi := by
  simp only [resultFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M)]
  simp only [id_eq,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero,lastCases_map]
  rfl

/-- The full pinned localized_existential sentence scheme with existing actual
saturation/cardinal guards; the existential witness and support are outputs. -/
def sentence {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ConstructionSaturationIndex.hartogs mu I)
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
      (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
      (.imp (ConstructionSaturationMergers.allMergers w history kappa)
      (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul unit mark H C incoming base kappa)
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (.mem (.bound mark) (.bound (rho 0)))
      (.imp (ForcingRootProbes.rootProbes index (rho 0) mul unit mark)
      (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small index w)))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul q mark p))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Jp))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jp Hp))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Jq))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jq Hq))
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho Hp v))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w c))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset d0 c))
      (.imp (ForcingLocalRecordPullback.supported (rho 0) q c)
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 p))
      (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id v (rho 6) z0 (.ex phi)))
      (resultFormula rho G F w q c Hq mul v phi)))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingRootProbes.rootProbes_freeClosed,
      ForcingLocalRecordPullback.supported_freeClosed,resultFormula_freeClosed]

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 v phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingRootProbes.rootProbes_semantics hM,ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportingRoot.tupleSupported_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),resultFormula_semantics hM]
  intro hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
    hJp hHp hJq hHq hv hd0 hc hc0 hcq hz0 hf
  exact localized_existential hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 phi (fun j => env (v j))
    hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
    hJp hHp hJq hHq hv hd0 hc hc0 hcq hz0 hf

/-- Native ZF's original proof kernel, with ground Choice discharged in its
already constructed internal L. This does not yet prove actual ACwo or Con. -/
theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 v phi))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 :=
    ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) _).mp
      (models rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 c Jp Hp Jq Hq z0 v phi hL hChoice)

end PPAC.Migration.ForcingLocalizedExistential


module
/-
# Obend.Apps.FidgetCamCert — the fidget tool path, checked from its committed certificate

`apps/fidget-cam/cam/impeller_5axis.cert` is, per pass, groups of consecutive moves each with a k-d
subdivision of part box × swept tool-position box (`KdCert`), written once by
`lean/tools/emitcam` (`lake exe obend-emit-cam`) beside the program it certifies
(`impeller_5axis.ngc`, the text of `Obend.Apps.FidgetCam.impeller5AxisNgc`). The build only replays
it: `checkCamGouge` evaluates one interval per leaf and searches nothing. The judge is
`Obend.Hardware.GeometryCAM.camGougeFormat` (`cam-gouge@1`), registered in `Obend.Judge.registry`.
If the part, the process or the tool path changes, the certificate no longer matches and this
module goes red until `obend-emit-cam` is run again.
-/
public import Obend.Apps.FidgetCam
import all Obend.Apps.FidgetCam
import all Obend.Hardware.GeometryCAM
public meta import Obend.Apps.FidgetCam
public section

namespace Obend.Apps.FidgetCamCert

open Obend.Hardware.GeometryCAM
open Obend.Hardware.Kinematics
open Obend.Apps.FidgetCam

set_option autoImplicit false

@[expose] def fidgetCertText : String := include_str "../../../apps/fidget-cam/cam/impeller_5axis.cert"

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

#freeze_cam_obj fidgetCamObj as Frozen
private theorem frozen_eq : Frozen = fidgetCamObj := by decide +kernel

set_option Elab.async false in
#replay_cam_cert Frozen from "apps/fidget-cam/cam/impeller_5axis.cert" as FidgetCertificate

private def accepted (o : CamGougeObj) (cert : List CamPassCert) : Bool :=
  match checkCamGouge o cert with | .ok => true | _ => false
private theorem accepted_of_check (o : CamGougeObj) (cert : List CamPassCert)
    (h : checkCamGouge o cert = .ok) : accepted o cert = true := by
  unfold accepted; rw [h]

/-- The committed certificate is checked in bounded kernel slices and composed exactly. -/
def fidgetCertAccepted : Bool := accepted fidgetCamObj FidgetCertificate.passes

private theorem frozenAccepted : checkCamGouge Frozen FidgetCertificate.passes = .ok := by
  apply checkCamGouge_of_groups
  · rfl
  · rw [FidgetCertificate.chunks_eq,FidgetCertificate.passes_eq]
    simp only [List.zip_cons_cons,List.zip_nil_left,List.all_cons,List.all_nil,Bool.and_eq_true]
    exact ⟨FidgetCertificate.verified0,FidgetCertificate.verified1,FidgetCertificate.verified2,
      FidgetCertificate.verified3,FidgetCertificate.verified4,FidgetCertificate.verified5,
      FidgetCertificate.verified6,FidgetCertificate.verified7,True.intro⟩

theorem fidgetCertAccepted_true : fidgetCertAccepted = true :=
  accepted_of_check _ _ (Eq.mp (congrArg
    (fun o => checkCamGouge o FidgetCertificate.passes = .ok) frozen_eq) frozenAccepted)

theorem fidgetCamObj_meaning : CamGougeMeaning fidgetCamObj := by
  rw [← frozen_eq]
  exact checkCamGouge_sound _ _ frozenAccepted

/-- **`fidget_toolpath_no_gouge_continuous`**: for every pass, every move `c₀ → c₁` the control
interpolates (plunges and retracts included), every rational time `t ∈ [0, 1]`, and every rational
point of the part, the ball end mill with its shank at `c₀ + t (c₁ - c₀)`, at its true radius and
length, does not contain the point. Coordinates are in 5 µm units (`camParams`): the tool path's
100 µm lattice points are `camScale = 20` times larger there. -/
theorem fidget_toolpath_no_gouge_continuous (pass : CamPass) (hPass : pass ∈ fidgetParams.passes)
    (c₀ c₁ : CLPoint)
    (hm : (c₀, c₁) ∈ (fidgetParams.certPath pass).zip (fidgetParams.certPath pass).tail)
    (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) (x y z : Rat)
    (hPart : evalFRepQ x y z camParams.part ≤ 0) :
    0 < evalFRepQ (x - (((camScale * c₀.x : Int) : Rat) + t * (((camScale * c₁.x : Int) : Rat) - ((camScale * c₀.x : Int) : Rat))))
        (y - (((camScale * c₀.y : Int) : Rat) + t * (((camScale * c₁.y : Int) : Rat) - ((camScale * c₀.y : Int) : Rat))))
        (z - (((camScale * c₀.z : Int) : Rat) + t * (((camScale * c₁.z : Int) : Rat) - ((camScale * c₀.z : Int) : Rat))))
      (frepBallEndMill 0 0 0 c₀.axis (camParams.lat camParams.toolR)
        (camParams.lat camParams.shankLen)) := by
  have hax := fidgetParams.certPath_axis pass c₀ (List.of_mem_zip hm).1
  have hmm : scaleMove ((c₀.x, c₀.y, c₀.z), (c₁.x, c₁.y, c₁.z)) ∈
      (fidgetParams.passMoves pass).map scaleMove :=
    List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨(c₀, c₁), hm, rfl⟩, rfl⟩
  have hch : ({ axis := pass.axis, moves := (fidgetParams.passMoves pass).map scaleMove } : CamChunk) ∈
      fidgetCamObj.chunks := List.mem_map.mpr ⟨pass, hPass, rfl⟩
  have hBox : fidgetCamObj.box.toQ.contains x y z := by
    show camParams.partBox.toQ.contains x y z
    rw [FidgetParams.partBox_toQ]
    exact camParams.part_in_boxQ x y z hPart
  have := fidgetCamObj_meaning _ hch _ hmm t h0 h1 x y z hBox hPart
  rw [hax]
  exact this

end Obend.Apps.FidgetCamCert
end

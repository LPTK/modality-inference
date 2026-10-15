import ModalityInference.Declarative

/-! Admissible scheme instances carry definedness obligations for their body
and quantified images. These obligations are source goals of comparison; they
do not enlarge the declared assumptions used to discharge those goals. -/
namespace ModalityInference.Scheme

def instanceGuards (s : Scheme) : Bounds :=
  s.body.wellFormedBounds ++
    s.typeParams.map (fun n => .sub (.var (.flex n)) (.var (.flex n))) ++
    s.modParams.map (fun n => .defined (.var (.flex n)))

def requireDefinedInstances (s : Scheme) : Scheme :=
  { s with bounds := s.bounds ++ s.instanceGuards }

end ModalityInference.Scheme

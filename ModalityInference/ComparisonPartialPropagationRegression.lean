import ModalityInference.ComparisonPartialPropagation

namespace ModalityInference.ComparisonPartialPropagationRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def a : Ty := .var (.rigid 0)
def b : Ty := .var (.rigid 1)
def x : Ty := .var (.flex 0)

def compensatedSource : Scheme :=
  { typeParams := [0], body := .prod (.modal x .top) (.modal x .top) }
def compensatedTarget : Scheme :=
  { bounds := [.sub a b], body := .prod
      (.modal (.modal a bad) (.const (Mode.global.compose Mode.top)))
      (.modal (.modal b bad) (.const (Mode.global.compose Mode.top))) }
def symbolicCompensatedTarget : Scheme :=
  { bounds := [.sub a b], body := .prod
      (.modal (.modal a bad) (.compose (.const Mode.global) .top))
      (.modal (.modal b bad) (.compose (.const Mode.global) .top)) }

def declaredSource : Scheme :=
  { typeParams := [0], body := .prod (.modal x .top) x }
def declaredTarget : Scheme :=
  { bounds := [.sub (.modal b .top) a], body := .prod a (.modal b bad) }

def freeSource : Scheme :=
  { typeParams := [0], body := .prod x (.var (.rigid 2)) }
def freeTarget : Scheme := .mono (.prod (.modal a bad) (.var (.rigid 2)))
def changedFreeTarget : Scheme := .mono (.prod (.modal a bad) (.var (.rigid 3)))

def accepted (source target : Scheme) : Bool :=
  match ComparisonPartialPropagation.attempt 20000 (SchemePreparation.prepare [] source target) with
  | .success (some _) => true
  | _ => false

def declined (source target : Scheme) : Bool :=
  match ComparisonPartialPropagation.attempt 20000 (SchemePreparation.prepare [] source target) with
  | .success none | .rejected _ => true
  | _ => false

def unsupported (source target : Scheme) : Bool :=
  match ComparisonPartialPropagation.attempt 20000 (SchemePreparation.prepare [] source target) with
  | .success none => true
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard [(compensatedSource, compensatedTarget), (declaredSource, declaredTarget),
    (compensatedSource, symbolicCompensatedTarget),
    (freeSource, freeTarget), ({ typeParams := [0], body := x }, Scheme.mono .unit)].all
  (fun (source, target) => accepted source target)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard [(freeSource, changedFreeTarget),
    ({ typeParams := [0], body := .prod x x }, Scheme.mono (.prod .unit .credit)),
    (Scheme.mono (.modal a bad), { bounds := [.sub a b], body := .modal b bad }),
    (Scheme.mono (.modal (.modal a .epsilon) bad), Scheme.mono (.modal a bad))].all
  (fun (source, target) => declined source target)

#guard unsupported { modParams := [0], body := .unit } (Scheme.mono .unit)
#guard unsupported { typeParams := [0], bounds := [.defined .epsilon], body := x }
  (Scheme.mono (.modal a bad))
#guard unsupported { typeParams := [0], body := .fn x .unit }
  (Scheme.mono (.fn (.modal a bad) .unit))

end ModalityInference.ComparisonPartialPropagationRegression

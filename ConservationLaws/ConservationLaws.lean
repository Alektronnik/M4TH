/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import ConservationLaws.TestFunction
public import ConservationLaws.Galilean
public import ConservationLaws.WeakSolution
public import ConservationLaws.ShockProfile
public import ConservationLaws.ShockReduction
public import ConservationLaws.Burgers

/-!
# Scalar conservation laws in Lean 4

Weak (distributional) solutions of one-dimensional scalar conservation laws
`∂ₜ u + ∂ₓ (f (u)) = 0`, travelling shock profiles, the Rankine–Hugoniot
condition, the exact reduction of the shock residual to the interface jump, and
the Lax/Oleinik entropy theory for the Burgers flux — with zero axioms and zero
`sorry`.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates `shockProfile`, `RankineHugoniot`, `HasShockIntegralReduction`,
and the Lax/Oleinik admissibility distinction for Burgers shocks, but it does
not add mathematical assumptions or alter the API of the formal package.
-/

namespace ConservationLawsGraph

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  strip : String := "#eaf2fb"
  box : String := "#1f5fd1"
  shock : String := "#b91c1c"
  characteristic : String := "#475569"
  admissible : String := "#0f766e"
  inadmissible : String := "#991b1b"
  stateLeft : String := "#dbeafe"
  stateRight : String := "#fee2e2"
  muted : String := "#475569"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1900.0
def height : Float := 1400.0

def plotLeft : Float := 180.0
def plotRight : Float := 1720.0
def plotTop : Float := 250.0
def plotBottom : Float := 1120.0

def tMin : Float := 0.0
def tMax : Float := 1.0
def xMin : Float := -0.35
def xMax : Float := 1.05

def shockSpeed : Float := 0.62

def localOutputPath : System.FilePath :=
  "ConservationLaws.svg"

def repositoryOutputDir : System.FilePath :=
  "M4TH/ConservationLaws"

def repositoryOutputPath : System.FilePath :=
  "M4TH/ConservationLaws/ConservationLaws.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

def px (t : Float) : Float :=
  plotLeft + ((t - tMin) / (tMax - tMin)) * (plotRight - plotLeft)

def py (x : Float) : Float :=
  plotBottom - ((x - xMin) / (xMax - xMin)) * (plotBottom - plotTop)

def shockX (t : Float) : Float :=
  shockSpeed * t

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

def attrs (xs : List (String × String)) : String :=
  xs.foldl (fun acc (k, v) => acc ++ " " ++ k ++ "=\"" ++ esc v ++ "\"") ""

def tag (name : String) (xs : List (String × String)) (body : String := "") : String :=
  if body.isEmpty then
    s!"  <{name}{attrs xs}/>\n"
  else
    s!"  <{name}{attrs xs}>{body}</{name}>\n"

def line (x1 y1 x2 y2 : Float) (color : String) (w : Float)
    (dash : Option String := none) (extra : List (String × String) := []) : String :=
  let base := [
    ("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
    ("stroke", color), ("stroke-width", fstr w), ("fill", "none")
  ]
  let dashed := match dash with
    | none => base
    | some d => base ++ [("stroke-dasharray", d)]
  tag "line" (dashed ++ extra)

def rect (x y w h : Float) (fill stroke : String) (sw : Float)
    (opacity : Option Float := none) : String :=
  let base := [
    ("x", fstr x), ("y", fstr y), ("width", fstr w), ("height", fstr h),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]
  let extra := match opacity with
    | none => base
    | some a => base ++ [("opacity", fstr a)]
  tag "rect" extra

def polygon (points fill stroke : String) (sw : Float) (opacity : Float) : String :=
  tag "polygon" [
    ("points", points), ("fill", fill), ("stroke", stroke),
    ("stroke-width", fstr sw), ("opacity", fstr opacity)
  ]

def circle (cx cy r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr cx), ("cy", fstr cy), ("r", fstr r),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]

def textAt (x y : Float) (content : String) (size : Nat) (color : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text" ([
    ("x", fstr x), ("y", fstr y), ("font-size", toString size),
    ("fill", color), ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] ++ extra) (esc content)

def arrowMarker : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-slate\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#475569\"/>\n" ++
  "    </marker>\n" ++
  "    <marker id=\"arrow-teal\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#0f766e\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def grid : String :=
  [0.0, 0.25, 0.5, 0.75, 1.0].foldl (fun out t =>
    out ++ line (px t) plotTop (px t) plotBottom "#e5e7eb" 0.65 (some "4 6")
  ) "" ++
  [-0.25, 0.0, 0.25, 0.5, 0.75, 1.0].foldl (fun out x =>
    out ++ line plotLeft (py x) plotRight (py x) "#d1d5db" 0.65 (some "4 6")
  ) ""

def axesAndTicks : String :=
  grid ++
  line plotLeft plotBottom plotRight plotBottom style.axis 2.2 ++
  line plotLeft plotTop plotLeft plotBottom style.axis 2.2 ++
  textAt (px 0.0) (plotBottom + 42.0) "0" 26 style.axis ++
  textAt (px 0.5) (plotBottom + 42.0) "T/2" 26 style.axis ++
  textAt (px 1.0) (plotBottom + 42.0) "T" 26 style.axis ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 95.0) "time t" 30 style.axis ++
  textAt (plotLeft - 95.0) ((plotTop + plotBottom) / 2.0) "space x" 30 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 95.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def shockRegions : String :=
  let p0 := s!"{fstr (px 0.0)},{fstr (py xMin)}"
  let p1 := s!"{fstr (px 1.0)},{fstr (py xMin)}"
  let p2 := s!"{fstr (px 1.0)},{fstr (py (shockX 1.0))}"
  let p3 := s!"{fstr (px 0.0)},{fstr (py 0.0)}"
  let q0 := s!"{fstr (px 0.0)},{fstr (py 0.0)}"
  let q1 := s!"{fstr (px 1.0)},{fstr (py (shockX 1.0))}"
  let q2 := s!"{fstr (px 1.0)},{fstr (py xMax)}"
  let q3 := s!"{fstr (px 0.0)},{fstr (py xMax)}"
  polygon (String.intercalate " " [p0, p1, p2, p3]) style.stateLeft "none" 0.0 0.72 ++
  polygon (String.intercalate " " [q0, q1, q2, q3]) style.stateRight "none" 0.0 0.62

def shockLine : String :=
  line (px 0.0) (py 0.0) (px 1.0) (py (shockX 1.0)) style.shock 5.0 none ++
  circle (px 0.0) (py 0.0) 7.0 style.shock style.white 1.5 ++
  circle (px 1.0) (py (shockX 1.0)) 7.0 style.shock style.white 1.5 ++
  textAt (px 0.62 + 38.0) (py (shockX 0.62) - 20.0) "interface x = s t" 24 style.shock "start"

def characteristics : String :=
  -- Left region, constant state uL = 1.2: characteristics are parallel and steeper than s.
  line (px 0.10) (py (-0.054)) (px 0.30) (py (shockX 0.30)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  line (px 0.35) (py 0.072) (px 0.60) (py (shockX 0.60)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  line (px 0.60) (py 0.198) (px 0.90) (py (shockX 0.90)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  -- Right region, constant state uR = 0.04: characteristics are parallel and flatter than s.
  line (px 0.00) (py 0.132) (px 0.20) (py (shockX 0.20)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  line (px 0.15) (py 0.324) (px 0.50) (py (shockX 0.50)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  line (px 0.35) (py 0.514) (px 0.80) (py (shockX 0.80)) style.characteristic 2.2 (some "10 9")
    [("marker-end", "url(#arrow-slate)")] ++
  textAt (px 0.15) (py 0.03) "uL" 32 style.axis ++
  textAt (px 0.85) (py 0.70) "uR" 32 style.axis ++
  textAt (px 0.35) (py 0.42) "characteristics enter the shock" 22 style.characteristic "middle"

def reductionPanel : String :=
  let x := 1030.0
  let y := 835.0
  rect x y 590.0 205.0 style.white "#cbd5e1" 1.6 (some 0.92) ++
  textAt (x + 34.0) (y + 42.0) "HasShockIntegralReduction" 24 style.axis "start" ++
  textAt (x + 34.0) (y + 85.0) "weakResidual =" 24 style.muted "start" ++
  textAt (x + 34.0) (y + 122.0) "integral over x = s t" 24 style.muted "start" ++
  textAt (x + 34.0) (y + 166.0) "(f(uL)-f(uR)) - s(uL-uR)" 22 style.shock "start"

def entropyPanel : String :=
  let x := 275.0
  let y := 300.0
  rect x y 485.0 170.0 style.white "#cbd5e1" 1.6 (some 0.92) ++
  textAt (x + 32.0) (y + 42.0) "Burgers flux: f(u) = u^2 / 2" 23 style.axis "start" ++
  textAt (x + 32.0) (y + 82.0) "Rankine-Hugoniot: s = (uL + uR) / 2" 22 style.muted "start" ++
  textAt (x + 32.0) (y + 122.0) "compression: uL > uR satisfies Lax" 22 style.admissible "start"

def annotations : String :=
  textAt (px 0.18) (py (-0.22)) "left state region: x < s t" 24 style.muted "start" ++
  textAt (px 0.67) (py 0.83) "right state region: x >= s t" 24 style.muted "start" ++
  reductionPanel ++
  entropyPanel

def titleBlock : String :=
  textAt (width / 2.0) 62.0 "ConservationLaws" 54 style.axis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Travelling shocks, Rankine-Hugoniot reduction, and entropy admissibility" 34 style.muted

def footer : String :=
  textAt (width / 2.0) 1350.0
    "Illustration of formal objects in ConservationLaws: shockProfile, weakResidual, RankineHugoniot, HasShockIntegralReduction, LaxEntropyCondition."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) "none" style.axis 2.4 ++
  shockRegions ++
  axesAndTicks ++
  characteristics ++
  shockLine ++
  annotations ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end ConservationLawsGraph

#eval ConservationLawsGraph.writeDefault

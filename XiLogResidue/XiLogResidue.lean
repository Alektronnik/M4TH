/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import XiLogResidue.Basic
public import XiLogResidue.LocalResidue
public import XiLogResidue.Divisor

/-!
# XiLogResidue

Residue of the logarithmic derivative of the entire Xi variant and its
dictionary with `MeromorphicOn.divisor`.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates the main objects certified in this package, but it does not
add mathematical assumptions or alter the API of the formal package.
-/

namespace XiLogResidueGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "XiLogResidue.svg"

def repositoryOutputDir : System.FilePath :=
  "XiLogResidue"

def repositoryOutputPath : System.FilePath :=
  "XiLogResidue/XiLogResidue.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  x.toString

def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

def attrs (xs : List (String × String)) : String :=
  String.intercalate " " (xs.map fun (k, v) => s!"{k}=\"{esc v}\"")

def tag (name : String) (xs : List (String × String)) (body : String := "") : String :=
  if body.isEmpty then
    s!"<{name} {attrs xs}/>\n"
  else
    s!"<{name} {attrs xs}>{body}</{name}>\n"

def rect (x y w h : Float) (fill stroke : String) (sw : Float) (opacity : Option Float := none) :
    String :=
  tag "rect" <|
    [("x", fstr x), ("y", fstr y), ("width", fstr w), ("height", fstr h),
      ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)] ++
      match opacity with
      | none => []
      | some a => [("opacity", fstr a)]

def line (x1 y1 x2 y2 : Float) (stroke : String) (sw : Float) (dash : Option String := none) :
    String :=
  tag "line" <|
    [("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
      ("stroke", stroke), ("stroke-width", fstr sw), ("stroke-linecap", "round")] ++
      match dash with
      | none => []
      | some d => [("stroke-dasharray", d)]

def circle (cx cy r : Float) (fill stroke : String) (sw : Float) : String :=
  tag "circle"
    [("cx", fstr cx), ("cy", fstr cy), ("r", fstr r), ("fill", fill),
      ("stroke", stroke), ("stroke-width", fstr sw)]

def textAt (x y : Float) (body : String) (size : Nat) (fill : String)
    (anchor : String := "middle") : String :=
  tag "text"
    [("x", fstr x), ("y", fstr y), ("font-family", "DejaVu Serif, Georgia, serif"),
      ("font-size", toString size), ("fill", fill), ("text-anchor", anchor)] body

def styleAxis : String := "#1f2937"
def styleMuted : String := "#475569"
def styleGrid : String := "#dbe4ef"
def styleBlue : String := "#2563eb"
def styleTeal : String := "#0f766e"
def styleRed : String := "#b91c1c"
def stylePale : String := "#f8fafc"
def stylePanel : String := "#ffffff"

def title : String :=
  textAt (width / 2.0) 62.0 "XiLogResidue" 54 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "logarithmic residue, analytic multiplicity, and the meromorphic divisor"
    31 styleMuted

def plotLeft : Float := 260.0
def plotTop : Float := 245.0
def plotRight : Float := 1540.0
def plotBottom : Float := 795.0

def px (x : Float) : Float :=
  plotLeft + (x + 0.15) / 1.30 * (plotRight - plotLeft)

def py (y : Float) : Float :=
  plotBottom - y / 34.0 * (plotBottom - plotTop)

def box : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) "#f0f7ff" styleAxis 2.2 (some 0.72) ++
  line (px 0.0) plotTop (px 0.0) plotBottom styleBlue 5.0 ++
  line (px 1.0) plotTop (px 1.0) plotBottom styleBlue 5.0 ++
  line (px 0.0) (py 0.0) (px 1.0) (py 0.0) styleBlue 5.0 ++
  line (px 0.0) (py 32.0) (px 1.0) (py 32.0) styleBlue 5.0 ++
  line (px 0.5) plotTop (px 0.5) plotBottom styleMuted 2.2 (some "10 9") ++
  textAt (px 0.5) (plotBottom + 56.0) "Re(s)" 28 styleAxis ++
  textAt (plotLeft - 72.0) ((plotTop + plotBottom) / 2.0) "Im(s)" 28 styleAxis
    "middle"

def zeros : String :=
  circle (px 0.48) (py 8.0) 9.0 "#111827" stylePanel 2.0 ++
  circle (px 0.54) (py 15.0) 9.0 "#111827" stylePanel 2.0 ++
  circle (px 0.45) (py 23.0) 9.0 "#111827" stylePanel 2.0 ++
  circle (px 0.51) (py 30.0) 9.0 "#111827" stylePanel 2.0 ++
  textAt (px 0.57) (py 8.0 + 7.0) "p₁" 22 styleMuted "start" ++
  textAt (px 0.61) (py 15.0 + 7.0) "p₂" 22 styleMuted "start" ++
  textAt (px 0.52) (py 23.0 + 7.0) "p₃" 22 styleMuted "start" ++
  textAt (px 0.58) (py 30.0 + 7.0) "p₄" 22 styleMuted "start"

def localPanel : String :=
  let x := 315.0
  let y := 305.0
  rect x y 530.0 190.0 stylePanel "#cbd5e1" 1.6 (some 0.94) ++
  textAt (x + 28.0) (y + 42.0) "local logarithmic residue" 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 86.0) "lim (z-p) · ξ'(z) / ξ(z)" 23 styleRed "start" ++
  textAt (x + 28.0) (y + 128.0) "= analyticOrderNatAt ξ p" 23 styleTeal "start" ++
  textAt (x + 28.0) (y + 166.0) "entireXi_logDeriv_residue_eq_multiplicity" 18 styleMuted "start"

def divisorPanel : String :=
  let x := 960.0
  let y := 305.0
  rect x y 505.0 190.0 stylePanel "#cbd5e1" 1.6 (some 0.94) ++
  textAt (x + 28.0) (y + 42.0) "divisor dictionary" 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 86.0) "divisor ξ box p" 23 styleRed "start" ++
  textAt (x + 28.0) (y + 128.0) "= multiplicity p" 23 styleTeal "start" ++
  textAt (x + 28.0) (y + 166.0) "entireXi_divisor_eq_multiplicity" 18 styleMuted "start"

def arrows : String :=
  line (px 0.48) (py 8.0) 610.0 495.0 styleRed 2.0 (some "8 7") ++
  line (px 0.54) (py 15.0) 1200.0 495.0 styleTeal 2.0 (some "8 7")

def footer : String :=
  textAt (width / 2.0) 1080.0
    "Illustration of formal objects in XiLogResidue: entireXiLogDeriv, analyticOrderNatAt, MeromorphicOn.divisor, zerosUpToImFinset."
    21 styleMuted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  rect 0.0 0.0 width height "#fffefd" "none" 0.0 ++
  title ++
  box ++
  arrows ++
  zeros ++
  localPanel ++
  divisorPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  let path ← defaultOutputPath
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end XiLogResidueGraph

#eval XiLogResidueGraph.writeDefault

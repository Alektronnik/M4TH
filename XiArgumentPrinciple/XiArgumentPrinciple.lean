/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import XiArgumentPrinciple.Basic
public import XiArgumentPrinciple.Contour
public import XiArgumentPrinciple.Counting

/-!
# XiArgumentPrinciple

Critical-box argument-principle chain for the entire Xi variant.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates the main objects certified in this package, but it does not
add mathematical assumptions or alter the API of the formal package.
-/

namespace XiArgumentPrincipleGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "XiArgumentPrinciple.svg"

def repositoryOutputDir : System.FilePath :=
  "XiArgumentPrinciple"

def repositoryOutputPath : System.FilePath :=
  "XiArgumentPrinciple/XiArgumentPrinciple.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String := x.toString

def esc (s : String) : String := s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
def attrs (xs : List (String × String)) : String :=
  String.intercalate " " (xs.map fun (k, v) => s!"{k}=\"{esc v}\"")
def tag (name : String) (xs : List (String × String)) (body : String := "") : String :=
  if body.isEmpty then s!"<{name} {attrs xs}/>\n" else s!"<{name} {attrs xs}>{esc body}</{name}>\n"

def rect (x y w h : Float) (fill stroke : String) (sw : Float) (opacity : Option Float := none) :
    String :=
  tag "rect" <|
    [("x", fstr x), ("y", fstr y), ("width", fstr w), ("height", fstr h),
      ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)] ++
      match opacity with | none => [] | some a => [("opacity", fstr a)]

def arrowMarker : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-muted\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#475569\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def line (x1 y1 x2 y2 : Float) (stroke : String) (sw : Float) (dash : Option String := none)
    (extra : List (String × String) := []) : String :=
  tag "line" <|
    [("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
      ("stroke", stroke), ("stroke-width", fstr sw), ("stroke-linecap", "round")] ++
      match dash with | none => [] | some d => [("stroke-dasharray", d)] ++ extra

def circle (cx cy r : Float) (fill stroke : String) (sw : Float) : String :=
  tag "circle"
    [("cx", fstr cx), ("cy", fstr cy), ("r", fstr r), ("fill", fill),
      ("stroke", stroke), ("stroke-width", fstr sw)]

def textAt (x y : Float) (body : String) (size : Nat) (fill : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text"
    ([("x", fstr x), ("y", fstr y), ("font-family", "DejaVu Serif, Georgia, serif"),
      ("font-size", toString size), ("fill", fill), ("text-anchor", anchor)] ++ extra)
    body

def styleAxis : String := "#1f2937"
def styleMuted : String := "#475569"
def styleBlue : String := "#2563eb"
def styleTeal : String := "#0f766e"
def styleRed : String := "#b91c1c"
def stylePanel : String := "#ffffff"

def title : String :=
  textAt (width / 2.0) 62.0 "XiArgumentPrinciple" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "critical-box contour, winding index, and zero counting"
    30 styleMuted

def plotLeft : Float := 265.0
def plotTop : Float := 245.0
def plotRight : Float := 1535.0
def plotBottom : Float := 795.0

def px (x : Float) : Float := plotLeft + x * (plotRight - plotLeft)
def py (y : Float) : Float := plotBottom - y / 32.0 * (plotBottom - plotTop)

def box : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) "#f0f7ff" styleAxis 2.2 (some 0.72) ++
  line (px 0.0) plotBottom (px 1.0) plotBottom styleBlue 5.0 ++
  line (px 1.0) plotBottom (px 1.0) (py 32.0) styleBlue 5.0 ++
  line (px 1.0) (py 32.0) (px 0.0) (py 32.0) styleBlue 5.0 ++
  line (px 0.0) (py 32.0) (px 0.0) plotBottom styleBlue 5.0 ++
  line (px 0.5) plotTop (px 0.5) plotBottom styleMuted 2.0 (some "10 9") ++
  textAt (px 0.5) (plotBottom + 58.0) "Re(s)" 28 styleAxis ++
  textAt (plotLeft - 82.0) ((plotTop + plotBottom) / 2.0) "Im(s)" 28 styleAxis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 82.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def zeros : String :=
  circle (px 0.48) (py 7.0) 8.5 "#111827" stylePanel 2.0 ++
  circle (px 0.54) (py 14.0) 8.5 "#111827" stylePanel 2.0 ++
  circle (px 0.45) (py 22.0) 8.5 "#111827" stylePanel 2.0 ++
  circle (px 0.51) (py 29.0) 8.5 "#111827" stylePanel 2.0

def panels : String :=
  rect 330.0 322.0 500.0 160.0 stylePanel "#cbd5e1" 1.6 (some 0.94) ++
  textAt 360.0 365.0 "ArgumentPrincipleBridge T" 24 styleAxis "start" ++
  textAt 360.0 408.0 "index one inside, index zero outside" 21 styleMuted "start" ++
  textAt 360.0 448.0 "residue sum = local multiplicities" 21 styleTeal "start" ++
  rect 970.0 322.0 500.0 160.0 stylePanel "#cbd5e1" 1.6 (some 0.94) ++
  textAt 1000.0 365.0 "ContourWindingEqualsCount" 24 styleAxis "start" ++
  textAt 1000.0 408.0 "∮ ξ'/ξ = 2πi · zeroCounting" 22 styleRed "start" ++
  textAt 1000.0 448.0 "contour_winding_equals_count_of_safe" 18 styleMuted "start"

def arrows : String :=
  line 830.0 402.0 970.0 402.0 styleTeal 3.0 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  line (px 0.54) (py 14.0) 970.0 482.0 styleRed 2.0 (some "8 8")
    [("marker-end", "url(#arrow-muted)")]

def footer : String :=
  textAt (width / 2.0) 1120.0
    "Illustration of formal objects in XiArgumentPrinciple: criticalBoxRectangleIntegral, contourCauchyIndexIntegral, ArgumentPrincipleBridge, zeroCountingWithMultiplicity."
    21 styleMuted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height "#fffefd" "none" 0.0 ++
  title ++ box ++ arrows ++ zeros ++ panels ++ footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  let path ← defaultOutputPath
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end XiArgumentPrincipleGraph

#eval XiArgumentPrincipleGraph.writeDefault

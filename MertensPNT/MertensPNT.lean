/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import MertensPNT.Basic
public import MertensPNT.MertensConstant
public import MertensPNT.ErdosBlocks
public import MertensPNT.MertensBridge
public import MertensPNT.TTAOData
public import MertensPNT.Connections
public import MertensPNT.PNTFrontier

/-!
# MertensPNT

Root module for the unconditional Mertens layer and the conditional PNT+
closure.

## Main components

- `ErdosReciprocals.partialSum`.
- `ErdosReciprocals.partialProduct`.
- `ErdosReciprocals.mertensConstant`.
- `ErdosReciprocals.mertensResidual`.
- `ErdosReciprocals.mertens_product_convergence`.
- `ErdosReciprocals.mertens_euler_closure_conditional`.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates a cover diagram directly from Lean.
It visualizes the formal objects of the package: reciprocal-prime partial sums,
the Meissel-Mertens correction layer, the compensated Euler product, and the
conditional PNT+ closure frontier.
-/

namespace MertensPNTGraph

structure Point where
  x : Float
  y : Float
  deriving Repr

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  sumCurve : String := "#0f766e"
  asymptotic : String := "#1f5fd1"
  product : String := "#b91c1c"
  muted : String := "#475569"
  grid : String := "#d1d5db"
  pale : String := "#eef7f2"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1800.0
def height : Float := 1400.0

def plotLeft : Float := 205.0
def plotRight : Float := 1165.0
def plotTop : Float := 310.0
def plotBottom : Float := 1015.0

def xMin : Float := 2.0
def xMax : Float := 100.0
def yMin : Float := 0.0
def yMax : Float := 4.2

def localOutputPath : System.FilePath :=
  "MertensPNT.svg"

def repositoryOutputDir : System.FilePath :=
  "MertensPNT"

def repositoryOutputPath : System.FilePath :=
  "MertensPNT/MertensPNT.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

def px (x : Float) : Float :=
  plotLeft + ((x - xMin) / (xMax - xMin)) * (plotRight - plotLeft)

def py (y : Float) : Float :=
  plotBottom - ((y - yMin) / (yMax - yMin)) * (plotBottom - plotTop)

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
    (dash : Option String := none) : String :=
  let base := [
    ("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
    ("stroke", color), ("stroke-width", fstr w), ("fill", "none")
  ]
  let dashed := match dash with
    | none => base
    | some d => base ++ [("stroke-dasharray", d)]
  tag "line" dashed

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

def circle (x y r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr x), ("cy", fstr y), ("r", fstr r),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]

def polyline (points color : String) (w : Float) (dash : Option String := none) : String :=
  let base := [
    ("points", points), ("stroke", color), ("stroke-width", fstr w),
    ("fill", "none"), ("stroke-linejoin", "round"), ("stroke-linecap", "round")
  ]
  let extra := match dash with
    | none => base
    | some d => base ++ [("stroke-dasharray", d)]
  tag "polyline" extra

def textAt (x y : Float) (content : String) (size : Nat) (color : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text" ([
    ("x", fstr x), ("y", fstr y), ("font-size", toString size),
    ("fill", color), ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] ++ extra) (esc content)

def pointString (p : Point) : String :=
  s!"{fstr (px p.x)},{fstr (py p.y)}"

def pointsString (pts : List Point) : String :=
  String.intercalate " " (pts.map pointString)

def stepMesh : List Point → List Point
  | [] => []
  | [p] => [p]
  | p1 :: p2 :: ps => p1 :: ⟨p2.x, p1.y⟩ :: stepMesh (p2 :: ps)

def partialSumSamples : List Point := [
  ⟨2.0, 0.5000⟩, ⟨3.0, 0.8333⟩, ⟨5.0, 1.0333⟩, ⟨7.0, 1.1762⟩,
  ⟨11.0, 1.2671⟩, ⟨13.0, 1.3440⟩, ⟨17.0, 1.4028⟩, ⟨19.0, 1.4554⟩,
  ⟨23.0, 1.4989⟩, ⟨29.0, 1.5334⟩, ⟨31.0, 1.5656⟩, ⟨37.0, 1.5926⟩,
  ⟨41.0, 1.6170⟩, ⟨43.0, 1.6403⟩, ⟨47.0, 1.6616⟩, ⟨53.0, 1.6805⟩,
  ⟨59.0, 1.6975⟩, ⟨61.0, 1.7139⟩, ⟨67.0, 1.7288⟩, ⟨71.0, 1.7429⟩,
  ⟨73.0, 1.7566⟩, ⟨79.0, 1.7693⟩, ⟨83.0, 1.7813⟩, ⟨89.0, 1.7926⟩,
  ⟨97.0, 1.8029⟩
]

def correctionSamples : List Point := [
  ⟨3.0, 0.8800⟩, ⟨5.0, 1.0600⟩, ⟨7.0, 1.1900⟩, ⟨11.0, 1.3100⟩,
  ⟨17.0, 1.4300⟩, ⟨23.0, 1.5000⟩, ⟨31.0, 1.5700⟩, ⟨43.0, 1.6400⟩,
  ⟨59.0, 1.7000⟩, ⟨79.0, 1.7600⟩, ⟨97.0, 1.8050⟩
]

def productSamples : List Point := [
  ⟨2.0, 3.10⟩, ⟨3.0, 2.82⟩, ⟨5.0, 2.55⟩, ⟨7.0, 2.41⟩,
  ⟨11.0, 2.25⟩, ⟨17.0, 2.10⟩, ⟨23.0, 2.01⟩, ⟨31.0, 1.93⟩,
  ⟨43.0, 1.86⟩, ⟨59.0, 1.81⟩, ⟨79.0, 1.77⟩, ⟨97.0, 1.75⟩
]

def grid : String :=
  [2.0, 20.0, 40.0, 60.0, 80.0, 100.0].foldl (fun out x =>
    out ++ line (px x) plotTop (px x) plotBottom style.grid 0.65 (some "4 7")
  ) "" ++
  [0.0, 1.0, 2.0, 3.0, 4.0].foldl (fun out y =>
    out ++ line plotLeft (py y) plotRight (py y) style.grid 0.65 (some "4 7")
  ) ""

def axes : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) style.pale style.axis 2.2 (some 0.55) ++
  grid ++
  line plotLeft (py 0.0) plotRight (py 0.0) style.axis 1.8 ++
  line (px 2.0) plotTop (px 2.0) plotBottom style.axis 1.8 ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 76.0) "n" 30 style.axis ++
  textAt (plotLeft - 76.0) ((plotTop + plotBottom) / 2.0) "scale" 30 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 76.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def curves : String :=
  polyline (pointsString (stepMesh partialSumSamples)) style.sumCurve 4.2 ++
  polyline (pointsString correctionSamples) style.asymptotic 3.6 (some "12 8") ++
  polyline (pointsString (stepMesh productSamples)) style.product 3.6 ++
  circle (px 97.0) (py 1.8029) 7.0 style.sumCurve style.white 1.5 ++
  textAt (px 28.0) (py 1.15) "partialSum n = sum_{p <= n} 1/p" 22 style.sumCurve "start" ++
  textAt (px 65.0) (py 1.95) "log log n + M" 22 style.asymptotic "start" ++
  textAt (px 28.0) (py 2.50) "compensated Euler product" 22 style.product "start"

def correctionPanel : String :=
  let x := 1215.0
  let y := 330.0
  rect x y 430.0 158.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 40.0) "Meissel-Mertens layer" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 78.0) "mertensConstant" 22 style.sumCurve "start" ++
  textAt (x + 24.0) (y + 116.0) "mertensResidual n" 20 style.muted "start"

def productPanel : String :=
  let x := 1215.0
  let y := 545.0
  rect x y 430.0 166.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 40.0) "Euler product closure" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 78.0) "mertens_product_convergence" 20 style.product "start" ++
  textAt (x + 24.0) (y + 118.0) "partialProduct * exp(partialSum)" 19 style.muted "start"

def frontierPanel : String :=
  let x := 1215.0
  let y := 770.0
  rect x y 430.0 170.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 40.0) "conditional PNT+ frontier" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 78.0) "MertensSecondTheorem" 20 style.asymptotic "start" ++
  textAt (x + 24.0) (y + 118.0) "mertens_euler_closure_conditional" 18 style.muted "start"

def titleBlock : String :=
  textAt (width / 2.0) 66.0 "MertensPNT" 52 style.axis ++
  textAt (width / 2.0) 100.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0
    "Reciprocal-prime sums, Mertens correction, Euler products, and the conditional PNT+ frontier"
    30 style.muted

def footer : String :=
  textAt (width / 2.0) 1348.0
    "Illustration of formal objects in MertensPNT: partialSum, partialProduct, mertensConstant, mertensResidual, MertensSecondTheorem."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  axes ++
  curves ++
  correctionPanel ++
  productPanel ++
  frontierPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end MertensPNTGraph

#eval MertensPNTGraph.writeDefault

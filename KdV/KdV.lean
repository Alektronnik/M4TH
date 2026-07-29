/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import KdV.Basic
public import KdV.Hyperbolic
public import KdV.Soliton
public import KdV.ConservationLaws

/-!
# KdV: exact soliton and conservation laws

This is the root module for the KdV package.

It migrates the fully proved `KdV` namespace into Mathlib contribution style:
English names and docstrings, a small module dependency graph, and a clear split
between the travelling-wave reduction, the hyperbolic-function calculus, the
exact soliton, and compact-support conservation laws.

## Main results

- `KdV.travellingWave_reduction`: travelling-wave KdV solutions satisfy the
  stationary soliton ODE.
- `KdV.soliton_satisfies_kdv`: the exact profile
  `3 c sech^2 ((sqrt c / 2) x)` solves that ODE for `c > 0`.
- `KdV.ConservedSolution.massRate_conserved`: `∫ u_t = 0`.
- `KdV.ConservedSolution.energyRate_conserved`: `∫ u u_t = 0`.

## Tags

KdV equation, soliton, conservation law, dispersive PDE
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates `solitonProfile`, the travelling-wave ansatz `x - c t`,
`travellingWave_reduction`, and the compact-support conservation layer, but it
does not add mathematical assumptions or alter the API of the formal package.
-/

namespace KdVGraph

structure Point where
  x : Float
  y : Float
  deriving Repr

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  grid : String := "#d1d5db"
  soliton : String := "#0f766e"
  shifted : String := "#1f5fd1"
  characteristic : String := "#475569"
  critical : String := "#b91c1c"
  muted : String := "#475569"
  paleBlue : String := "#eaf2fb"
  paleGreen : String := "#ecfdf5"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1900.0
def height : Float := 1400.0

def plotLeft : Float := 170.0
def plotRight : Float := 1730.0
def plotTop : Float := 250.0
def plotBottom : Float := 1120.0

def xMin : Float := -8.0
def xMax : Float := 8.0
def yMin : Float := -0.15
def yMax : Float := 3.35

def localOutputPath : System.FilePath :=
  "KdV.svg"

def repositoryOutputDir : System.FilePath :=
  "KdV"

def repositoryOutputPath : System.FilePath :=
  "KdV/KdV.svg"

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

def circle (cx cy r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr cx), ("cy", fstr cy), ("r", fstr r),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]

def polyline (points color : String) (w : Float)
    (dash : Option String := none) : String :=
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

def arrowMarker : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-blue\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#1f5fd1\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def solitonSamples : List Point := [
  ⟨-8.0, 0.0040⟩, ⟨-7.0, 0.0109⟩, ⟨-6.0, 0.0296⟩, ⟨-5.0, 0.0798⟩,
  ⟨-4.0, 0.2120⟩, ⟨-3.0, 0.5420⟩, ⟨-2.0, 1.2600⟩, ⟨-1.0, 2.3580⟩,
  ⟨0.0, 3.0000⟩, ⟨1.0, 2.3580⟩, ⟨2.0, 1.2600⟩, ⟨3.0, 0.5420⟩,
  ⟨4.0, 0.2120⟩, ⟨5.0, 0.0798⟩, ⟨6.0, 0.0296⟩, ⟨7.0, 0.0109⟩,
  ⟨8.0, 0.0040⟩
]

def shiftedSamples : List Point :=
  [
    ⟨-5.6, 0.0040⟩, ⟨-4.6, 0.0109⟩, ⟨-3.6, 0.0296⟩, ⟨-2.6, 0.0798⟩,
    ⟨-1.6, 0.2120⟩, ⟨-0.6, 0.5420⟩, ⟨0.4, 1.2600⟩, ⟨1.4, 2.3580⟩,
    ⟨2.4, 3.0000⟩, ⟨3.4, 2.3580⟩, ⟨4.4, 1.2600⟩, ⟨5.4, 0.5420⟩,
    ⟨6.4, 0.2120⟩, ⟨7.4, 0.0798⟩, ⟨8.0, 0.0440⟩
  ]

def pointString (p : Point) : String :=
  s!"{fstr (px p.x)},{fstr (py p.y)}"

def curveString (pts : List Point) : String :=
  String.intercalate " " (pts.map pointString)

def grid : String :=
  [-8.0, -4.0, 0.0, 4.0, 8.0].foldl (fun out x =>
    out ++ line (px x) plotTop (px x) plotBottom "#e5e7eb" 0.65 (some "4 6")
  ) "" ++
  [0.0, 1.0, 2.0, 3.0].foldl (fun out y =>
    out ++ line plotLeft (py y) plotRight (py y) style.grid 0.65 (some "4 6")
  ) ""

def axesAndTicks : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) "none" style.axis 2.4 ++
  grid ++
  line plotLeft (py 0.0) plotRight (py 0.0) style.axis 2.2 ++
  line (px 0.0) plotTop (px 0.0) plotBottom style.axis 2.0 (some "8 8") ++
  textAt (px (-8.0)) (plotBottom + 42.0) "-8" 24 style.axis ++
  textAt (px 0.0) (plotBottom + 42.0) "0" 24 style.axis ++
  textAt (px 8.0) (plotBottom + 42.0) "8" 24 style.axis ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 95.0) "space coordinate" 30 style.axis ++
  textAt (plotLeft - 92.0) ((plotTop + plotBottom) / 2.0) "amplitude" 30 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 92.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def curves : String :=
  polyline (curveString solitonSamples) style.soliton 4.4 ++
  polyline (curveString shiftedSamples) style.shifted 4.0 (some "16 11") ++
  line (px 0.0) (py 3.0) (px 2.4) (py 3.0) style.shifted 2.4 (some "10 8")
    [("marker-end", "url(#arrow-blue)")] ++
  circle (px 0.0) (py 3.0) 8.0 style.soliton style.white 1.8 ++
  circle (px 2.4) (py 3.0) 8.0 style.shifted style.white 1.8 ++
  textAt (px 1.25) (py 3.18) "translation by c t" 22 style.shifted "middle"

def translationLines : String :=
  line (px (-3.0)) (py 0.0) (px (-3.0)) (py (-0.12)) style.characteristic 2.0 (some "8 6") ++
  line (px 3.0) (py 0.0) (px 3.0) (py (-0.12)) style.characteristic 2.0 (some "8 6") ++
  textAt (px (-3.0)) (py (-0.30)) "-c t" 24 style.axis "middle" ++
  textAt (px 3.0) (py (-0.30)) "+c t" 24 style.axis "middle"

def reductionPanel : String :=
  let x := 1275.0
  let y := 282.0
  rect x y 410.0 130.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 36.0) "travellingWave_reduction" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 70.0) "-c f' + f f' + f''' = 0" 21 style.critical "start" ++
  textAt (x + 24.0) (y + 104.0) "soliton_satisfies_kdv" 20 style.soliton "start"

def conservationPanel : String :=
  let x := 215.0
  let y := 282.0
  rect x y 500.0 130.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 36.0) "compact-support conservation" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 70.0) "massRate_conserved: integral u_t = 0" 19 style.muted "start" ++
  textAt (x + 24.0) (y + 104.0) "energyRate_conserved: integral u u_t = 0" 19 style.muted "start"

def titleBlock : String :=
  textAt (width / 2.0) 62.0 "KdV" 54 style.axis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Exact sech-squared soliton, travelling-wave reduction, and conservation laws" 34 style.muted

def footer : String :=
  textAt (width / 2.0) 1350.0
    "Illustration of formal objects in KdV: solitonProfile, travellingWave_reduction, soliton_satisfies_kdv, massRate_conserved, energyRate_conserved."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) style.paleGreen "none" 0.0 (some 0.45) ++
  axesAndTicks ++
  curves ++
  translationLines ++
  reductionPanel ++
  conservationPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end KdVGraph

#eval KdVGraph.writeDefault

/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import BurgersBlowUp.Calculus
public import BurgersBlowUp.ODE
public import BurgersBlowUp.Characteristics
public import BurgersBlowUp.BlowUp

/-!
# Gradient blow-up for the inviscid Burgers equation, in Lean 4

Finite-time singularity formation for `∂ₜ u + u ∂ₓ u = 0`: with the compressive
initial datum `u₀ (x) = -x`, no `C²` regular solution exists on `[0, T)` once
`T ≥ 1`.  Method of characteristics, linear-ODE uniqueness via a Lyapunov
energy, and the exact Riccati solution `V (t) = -1 / (1 - t)` of the gradient
evolution — with zero axioms and zero `sorry`.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates `initialRamp`, `constant_along_characteristic`,
`gradient_eq_neg_one_div`, and `not_isRegularSolution_initialRamp`, but it does
not add mathematical assumptions or alter the API of the formal package.
-/

namespace BurgersBlowUpGraph

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  grid : String := "#d1d5db"
  characteristic : String := "#475569"
  critical : String := "#b91c1c"
  state : String := "#1f5fd1"
  curve : String := "#0f766e"
  muted : String := "#475569"
  paleBlue : String := "#eaf2fb"
  paleRed : String := "#fee2e2"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1900.0
def height : Float := 1400.0

def leftX0 : Float := 150.0
def leftX1 : Float := 920.0
def plotTop : Float := 250.0
def plotBottom : Float := 1120.0

def rightX0 : Float := 1060.0
def rightX1 : Float := 1770.0

def tMin : Float := 0.0
def tMax : Float := 1.05
def xMin : Float := -1.15
def xMax : Float := 1.15
def vMin : Float := -12.0
def vMax : Float := 1.0

def localOutputPath : System.FilePath :=
  "BurgersBlowUp.svg"

def repositoryOutputDir : System.FilePath :=
  "T-ORIK4/Math/BurgersBlowUp"

def repositoryOutputPath : System.FilePath :=
  "T-ORIK4/Math/BurgersBlowUp/BurgersBlowUp.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

def txL (t : Float) : Float :=
  leftX0 + ((t - tMin) / (tMax - tMin)) * (leftX1 - leftX0)

def xxL (x : Float) : Float :=
  plotBottom - ((x - xMin) / (xMax - xMin)) * (plotBottom - plotTop)

def txR (t : Float) : Float :=
  rightX0 + ((t - tMin) / (tMax - tMin)) * (rightX1 - rightX0)

def vyR (v : Float) : Float :=
  plotBottom - ((v - vMin) / (vMax - vMin)) * (plotBottom - plotTop)

def charX (x0 t : Float) : Float :=
  x0 * (1.0 - t)

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

def polyline (points color : String) (w : Float) : String :=
  tag "polyline" [
    ("points", points), ("stroke", color), ("stroke-width", fstr w),
    ("fill", "none"), ("stroke-linejoin", "round"), ("stroke-linecap", "round")
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
  "  </defs>\n"

def gridLeft : String :=
  [0.0, 0.25, 0.5, 0.75, 1.0].foldl (fun out t =>
    out ++ line (txL t) plotTop (txL t) plotBottom "#e5e7eb" 0.65 (some "4 6")
  ) "" ++
  [-1.0, -0.5, 0.0, 0.5, 1.0].foldl (fun out x =>
    out ++ line leftX0 (xxL x) leftX1 (xxL x) style.grid 0.65 (some "4 6")
  ) ""

def gridRight : String :=
  [0.0, 0.25, 0.5, 0.75, 1.0].foldl (fun out t =>
    out ++ line (txR t) plotTop (txR t) plotBottom "#e5e7eb" 0.65 (some "4 6")
  ) "" ++
  [-10.0, -8.0, -6.0, -4.0, -2.0, 0.0].foldl (fun out v =>
    out ++ line rightX0 (vyR v) rightX1 (vyR v) style.grid 0.65 (some "4 6")
  ) ""

def axesLeft : String :=
  rect leftX0 plotTop (leftX1 - leftX0) (plotBottom - plotTop) "none" style.axis 2.4 ++
  gridLeft ++
  line leftX0 plotBottom leftX1 plotBottom style.axis 2.2 ++
  line leftX0 plotTop leftX0 plotBottom style.axis 2.2 ++
  line (txL 1.0) plotTop (txL 1.0) plotBottom style.critical 3.2 (some "18 12") ++
  textAt (txL 0.0) (plotBottom + 42.0) "0" 24 style.axis ++
  textAt (txL 1.0) (plotBottom + 42.0) "1" 24 style.critical ++
  textAt ((leftX0 + leftX1) / 2.0) (plotBottom + 92.0) "time t" 28 style.axis ++
  textAt (leftX0 - 82.0) ((plotTop + plotBottom) / 2.0) "space x" 28 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (leftX0 - 82.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def axesRight : String :=
  rect rightX0 plotTop (rightX1 - rightX0) (plotBottom - plotTop) "none" style.axis 2.4 ++
  gridRight ++
  line rightX0 (vyR 0.0) rightX1 (vyR 0.0) style.axis 2.0 ++
  line rightX0 plotTop rightX0 plotBottom style.axis 2.2 ++
  line (txR 1.0) plotTop (txR 1.0) plotBottom style.critical 3.2 (some "18 12") ++
  textAt (txR 0.0) (plotBottom + 42.0) "0" 24 style.axis ++
  textAt (txR 1.0) (plotBottom + 42.0) "1" 24 style.critical ++
  textAt ((rightX0 + rightX1) / 2.0) (plotBottom + 92.0) "time t" 28 style.axis ++
  textAt (rightX0 - 52.0) ((plotTop + plotBottom) / 2.0) "gradient V(t)" 28 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (rightX0 - 52.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def characteristicLine (x0 : Float) : String :=
  line (txL 0.0) (xxL x0) (txL 1.0) (xxL 0.0) style.characteristic 2.4 (some "12 9")
    [("marker-end", "url(#arrow-slate)")]

def characteristics : String :=
  [-1.0, -0.65, -0.32, 0.0, 0.32, 0.65, 1.0].foldl
    (fun out x0 => out ++ characteristicLine x0) "" ++
  circle (txL 1.0) (xxL 0.0) 9.0 style.critical style.white 2.0 ++
  textAt (txL 0.07) (xxL 0.92) "u0(x) = -x" 24 style.axis "start" ++
  textAt (txL 0.50) (xxL (-0.88)) "x(t) = x0(1 - t)" 24 style.characteristic "middle" ++
  textAt (txL 0.94) (xxL 0.0 - 120.0) "gradient singularity" 21 style.critical "end"

def gradientSamples : List (Float × Float) := [
  (0.00, -1.0000), (0.10, -1.1111), (0.20, -1.2500), (0.30, -1.4286),
  (0.40, -1.6667), (0.50, -2.0000), (0.60, -2.5000), (0.70, -3.3333),
  (0.78, -4.5455), (0.84, -6.2500), (0.88, -8.3333), (0.90, -10.0000),
  (0.915, -11.7647)
]

def gradientPointString (p : Float × Float) : String :=
  s!"{fstr (txR p.1)},{fstr (vyR p.2)}"

def gradientCurve : String :=
  let pts := String.intercalate " " (gradientSamples.map gradientPointString)
  polyline pts style.curve 4.2 ++
  circle (txR 0.0) (vyR (-1.0)) 7.5 style.curve style.white 1.6 ++
  textAt (txR 0.03) (vyR (-1.0) - 18.0) "V(0) = -1" 22 style.curve "start" ++
  textAt (txR 0.48) (vyR (-2.0) - 22.0) "V(t) = -1 / (1 - t)" 24 style.curve "middle" ++
  textAt (txR 1.0 - 18.0) (vyR (-9.5)) "t = 1" 24 style.critical "end"

def contradictionPanel : String :=
  let x := 1095.0
  let y := 890.0
  rect x y 500.0 188.0 style.white "#cbd5e1" 1.6 (some 0.96) ++
  textAt (x + 34.0) (y + 42.0) "not_isRegularSolution_initialRamp" 23 style.axis "start" ++
  textAt (x + 34.0) (y + 82.0) "choose t = 1 - 1 / (|M| + 1)" 22 style.muted "start" ++
  textAt (x + 34.0) (y + 122.0) "|u_x(t,0)| = |M| + 1" 22 style.critical "start" ++
  textAt (x + 34.0) (y + 162.0) "contradicts global gradient bound M" 22 style.muted "start"

def titleBlock : String :=
  textAt (width / 2.0) 62.0 "BurgersBlowUp" 54 style.axis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Characteristics collapse and Riccati gradient blow-up at the critical time" 34 style.muted

def footer : String :=
  textAt (width / 2.0) 1350.0
    "Illustration of formal objects in BurgersBlowUp: initialRamp, constant_along_characteristic, gradient_eq_neg_one_div, not_isRegularSolution_initialRamp."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  rect leftX0 plotTop (leftX1 - leftX0) (plotBottom - plotTop) style.paleBlue "none" 0.0 (some 0.55) ++
  rect rightX0 plotTop (rightX1 - rightX0) (plotBottom - plotTop) style.paleRed "none" 0.0 (some 0.35) ++
  axesLeft ++
  axesRight ++
  characteristics ++
  gradientCurve ++
  contradictionPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end BurgersBlowUpGraph

#eval BurgersBlowUpGraph.writeDefault

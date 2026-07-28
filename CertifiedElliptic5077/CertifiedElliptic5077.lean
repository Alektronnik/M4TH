/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import CertifiedElliptic5077.Basic
public import CertifiedElliptic5077.FiniteFieldCounts
public import CertifiedElliptic5077.IntegralModel
public import CertifiedElliptic5077.Entry5077a1

/-!
# Certified elliptic curve entry 5077a1

This is the root module for the standalone `CertifiedElliptic5077` package.  It
packages a reusable short-Weierstrass computational layer together with the
explicit LMFDB/Cremona entry 5077a1, its integral model, its short model,
finite local point counts, and selected certified rational points.

## Main results

- `CertifiedEC.delta_E5077_integral`.
- `CertifiedEC.shortDiscriminant_E5077`.
- `CertifiedEC.N_two`, `CertifiedEC.N_three`, `CertifiedEC.N_five`.
- `CertifiedEC.P1_add_self`, `CertifiedEC.P2_add_self`, `CertifiedEC.Pm3_add_self`.
- `CertifiedEC.integralP3_toShort`.

## Tags

elliptic curve, 5077a1, Weierstrass model, finite-field counts
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The diagram shows the short Weierstrass curve, the integral-to-short
coordinate change, the discriminant certificate, and the finite local counts.
-/

namespace CertifiedElliptic5077Graph

structure Point where
  x : Float
  y : Float
  deriving Repr

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  curve : String := "#0f766e"
  shifted : String := "#1f5fd1"
  critical : String := "#b91c1c"
  muted : String := "#475569"
  grid : String := "#d1d5db"
  pale : String := "#eef7f2"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1800.0
def height : Float := 1400.0

def plotLeft : Float := 220.0
def plotRight : Float := 1160.0
def plotTop : Float := 305.0
def plotBottom : Float := 1045.0

def xMin : Float := -4.5
def xMax : Float := 4.5
def yMin : Float := -8.0
def yMax : Float := 8.0

def localOutputPath : System.FilePath :=
  "CertifiedElliptic5077.svg"

def repositoryOutputDir : System.FilePath :=
  "M4TH/CertifiedElliptic5077"

def repositoryOutputPath : System.FilePath :=
  "M4TH/CertifiedElliptic5077/CertifiedElliptic5077.svg"

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
    s!"  <{name}{attrs xs}>{esc body}</{name}>\n"

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

def circle (x y r : Float) (fill stroke : String) (sw : Float := 0.0) : String :=
  tag "circle" [
    ("cx", fstr x), ("cy", fstr y), ("r", fstr r),
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

def upperBranch : List Point := [
  ⟨-3.012443, 0.000000⟩, ⟨-3.0, 0.500000⟩, ⟨-2.6, 2.621831⟩, ⟨-2.2, 3.316926⟩,
  ⟨-1.8, 3.608047⟩, ⟨-1.4, 3.647739⟩, ⟨-1.0, 3.500000⟩,
  ⟨-0.6, 3.199062⟩, ⟨-0.2, 2.764417⟩, ⟨0.0, 2.500000⟩,
  ⟨0.2, 2.204087⟩, ⟨0.6, 1.505324⟩, ⟨1.0, 0.500000⟩, ⟨1.065814, 0.000000⟩
]

def lowerBranch : List Point :=
  upperBranch.map fun p => ⟨p.x, -p.y⟩

def rightBranch : List Point := [
  ⟨1.946629, 0.000000⟩, ⟨2.0, 0.500000⟩, ⟨2.2, 1.223928⟩, ⟨2.4, 1.809420⟩,
  ⟨2.8, 2.932917⟩, ⟨3.2, 4.076518⟩, ⟨3.6, 5.263649⟩,
  ⟨4.0, 6.500000⟩, ⟨4.3, 7.460362⟩
]

def rightLowerBranch : List Point :=
  rightBranch.map fun p => ⟨p.x, -p.y⟩

def pointString (p : Point) : String :=
  s!"{fstr (px p.x)},{fstr (py p.y)}"

def curveString (pts : List Point) : String :=
  String.intercalate " " (pts.map pointString)

def grid : String :=
  [-4.0, -2.0, 0.0, 2.0, 4.0].foldl (fun out x =>
    out ++ line (px x) plotTop (px x) plotBottom style.grid 0.65 (some "4 7")
  ) "" ++
  [-6.0, -3.0, 0.0, 3.0, 6.0].foldl (fun out y =>
    out ++ line plotLeft (py y) plotRight (py y) style.grid 0.65 (some "4 7")
  ) ""

def axes : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) style.pale style.axis 2.2 (some 0.55) ++
  grid ++
  line plotLeft (py 0.0) plotRight (py 0.0) style.axis 1.8 ++
  line (px 0.0) plotTop (px 0.0) plotBottom style.axis 1.8 ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 76.0) "x" 30 style.axis ++
  textAt (plotLeft - 76.0) ((plotTop + plotBottom) / 2.0) "Y" 30 style.axis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 76.0)} {fstr ((plotTop + plotBottom) / 2.0)})")]

def curve : String :=
  polyline (curveString upperBranch) style.curve 4.2 ++
  polyline (curveString lowerBranch) style.curve 4.2 ++
  polyline (curveString rightBranch) style.curve 4.2 ++
  polyline (curveString rightLowerBranch) style.curve 4.2 ++
  circle (px 1.0) (py 0.5) 7.5 style.critical style.white 1.7 ++
  textAt (px 1.0 + 18.0) (py 0.5 - 18.0) "P₁" 22 style.critical "start" ++
  circle (px 2.0) (py 0.5) 7.5 style.critical style.white 1.7 ++
  textAt (px 2.0 + 18.0) (py 0.5 - 18.0) "P₂" 22 style.critical "start" ++
  circle (px (-3.0)) (py 0.5) 7.5 style.critical style.white 1.7 ++
  textAt (px (-3.0) - 20.0) (py 0.5 - 14.0) "P₋₃" 22 style.critical "end" ++
  circle (px 0.0) (py 2.5) 7.5 style.shifted style.white 1.7 ++
  textAt (px 0.0 + 18.0) (py 2.5 - 18.0) "P₃" 22 style.shifted "start" ++
  textAt (px (-2.55)) (py 4.25) "Y² = x³ - 7x + 25/4" 25 style.curve "start"

def modelPanel : String :=
  let x := 1210.0
  let y := 330.0
  rect x y 425.0 150.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 38.0) "integral model" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 72.0) "y² + y = x³ - 7x + 6" 21 style.muted "start" ++
  textAt (x + 24.0) (y + 108.0) "Y = y + 1/2" 22 style.shifted "start"

def discriminantPanel : String :=
  let x := 1210.0
  let y := 525.0
  rect x y 425.0 150.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 38.0) "certified invariants" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 72.0) "Δ = 5077" 24 style.critical "start" ++
  textAt (x + 24.0) (y + 108.0) "shortDiscriminant_E5077" 19 style.muted "start"

def countsPanel : String :=
  let x := 1210.0
  let y := 720.0
  rect x y 425.0 160.0 style.white "#cbd5e1" 1.45 (some 0.96) ++
  textAt (x + 24.0) (y + 38.0) "finite local counts" 20 style.axis "start" ++
  textAt (x + 24.0) (y + 74.0) "N₂ = 5,  N₃ = 7,  N₅ = 10" 21 style.curve "start" ++
  textAt (x + 24.0) (y + 112.0) "a₂ = -2, a₃ = -3, a₅ = -4" 19 style.muted "start"

def titleBlock : String :=
  textAt (width / 2.0) 66.0 "CertifiedElliptic5077" 52 style.axis ++
  textAt (width / 2.0) 100.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "Certified 5077a1 data: models, discriminant, local counts, and rational points" 31 style.muted

def footer : String :=
  textAt (width / 2.0) 1348.0
    "Illustration of formal objects in CertifiedElliptic5077: E5077, E5077Integral, N_p, delta_E5077_integral, certified point doubles."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  axes ++
  curve ++
  modelPanel ++
  discriminantPanel ++
  countsPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end CertifiedElliptic5077Graph

#eval CertifiedElliptic5077Graph.writeDefault

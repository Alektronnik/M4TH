/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import SU3Wilson.SU3
public import SU3Wilson.Wilson
public import SU3Wilson.Lattice4D

/-!
# SU(3) Wilson plaquette positivity

This is the root module for the standalone `SU3Wilson` package.  It packages
the concrete group `SU(3)`, the normalized trace bound, finite lattice Wilson
terms, and the constructive four-dimensional plaquette layer.

## Main results

- `Physics.YangMills.su3_trace_re_bound`.
- `Physics.YangMills.wilsonTerm_nonneg`.
- `Physics.YangMills.wilsonTerm_le_two`.
- `Physics.YangMills.WilsonAction_nonneg`.
- `Physics.YangMills.plaquette4D_diagonal`.
- `Physics.YangMills.WilsonAction4D_nonneg`.

## Tags

SU(3), Wilson action, lattice gauge theory, plaquette positivity
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The diagram shows a single oriented plaquette with `SU(3)` link
variables and the normalized Wilson term certified by the package.
-/

namespace SU3WilsonGraph

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  link : String := "#0f766e"
  linkAlt : String := "#1f5fd1"
  critical : String := "#b91c1c"
  muted : String := "#475569"
  grid : String := "#d1d5db"
  pale : String := "#eef7f2"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1800.0
def height : Float := 1400.0

def localOutputPath : System.FilePath :=
  "SU3Wilson.svg"

def repositoryOutputDir : System.FilePath :=
  "M4TH/SU3Wilson"

def repositoryOutputPath : System.FilePath :=
  "M4TH/SU3Wilson/SU3Wilson.svg"

def defaultOutputPath : IO System.FilePath := do
  if (← repositoryOutputDir.pathExists) then
    pure repositoryOutputPath
  else
    pure localOutputPath

def fstr (x : Float) : String :=
  toString x

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

def path (d fill stroke : String) (w : Float)
    (extra : List (String × String) := []) : String :=
  tag "path" ([
    ("d", d), ("fill", fill), ("stroke", stroke), ("stroke-width", fstr w),
    ("stroke-linecap", "round"), ("stroke-linejoin", "round")
  ] ++ extra)

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

def textAt (x y : Float) (content : String) (size : Nat) (color : String)
    (anchor : String := "middle") (extra : List (String × String) := []) : String :=
  tag "text" ([
    ("x", fstr x), ("y", fstr y), ("font-size", toString size),
    ("fill", color), ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] ++ extra) (esc content)

def arrowDefs : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-green\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"8\" markerHeight=\"8\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#0f766e\"/>\n" ++
  "    </marker>\n" ++
  "    <marker id=\"arrow-blue\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"8\" markerHeight=\"8\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#1f5fd1\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def x0 : Float := 670.0
def y0 : Float := 800.0
def side : Float := 380.0

def latticeGrid : String :=
  [-1.0, 0.0, 1.0, 2.0].foldl (fun out k =>
    out ++ line (x0 - side / 2.0) (y0 - k * side / 2.0) (x0 + 1.5 * side) (y0 - k * side / 2.0)
      style.grid 0.9 (some "5 9") ++
    line (x0 + k * side / 2.0) (y0 + side / 2.0) (x0 + k * side / 2.0) (y0 - 1.5 * side)
      style.grid 0.9 (some "5 9")
  ) ""

def plaquetteOrientation : String :=
  -- Interior trace indicator: counter-clockwise flow, matching `P_{μν}(x)`.
  path "M 806 575 A 54 32 0 0 0 860 607" "none" style.link 2.5 ++
  path "M 860 607 A 54 32 0 0 0 914 575" "none" style.link 2.5 ++
  path "M 914 575 A 54 32 0 0 0 860 543" "none" style.link 2.5 ++
  path "M 860 543 A 54 32 0 0 0 806 575" "none" style.link 2.5 ++
  path "M 906 583 L 914 569 L 922 583" "none" style.link 2.5

def plaquette : String :=
  rect x0 (y0 - side) side side style.pale style.axis 2.4 (some 0.75) ++
  line x0 y0 (x0 + side) y0 style.link 5.0 none [("marker-end", "url(#arrow-green)")] ++
  line (x0 + side) y0 (x0 + side) (y0 - side) style.linkAlt 5.0 none [("marker-end", "url(#arrow-blue)")] ++
  line (x0 + side) (y0 - side) x0 (y0 - side) style.link 5.0 none [("marker-end", "url(#arrow-green)")] ++
  line x0 (y0 - side) x0 y0 style.linkAlt 5.0 none [("marker-end", "url(#arrow-blue)")] ++
  circle x0 y0 10.0 style.axis style.white 2.0 ++
  circle (x0 + side) y0 10.0 style.axis style.white 2.0 ++
  circle x0 (y0 - side) 10.0 style.axis style.white 2.0 ++
  circle (x0 + side) (y0 - side) 10.0 style.axis style.white 2.0 ++
  textAt (x0 + side / 2.0) (y0 + 45.0) "Uμ(x)" 24 style.link ++
  textAt (x0 + side + 62.0) (y0 - side / 2.0 + 8.0) "Uν(x+μ)" 24 style.linkAlt "start" ++
  textAt (x0 + side / 2.0) (y0 - side - 34.0) "Uμ(x+ν)⁻¹" 24 style.link ++
  textAt (x0 - 62.0) (y0 - side / 2.0 + 8.0) "Uν(x)⁻¹" 24 style.linkAlt "end" ++
  plaquetteOrientation ++
  textAt (x0 + side / 2.0) (y0 - side / 2.0 + 76.0) "plaquette4D" 29 style.axis

def leftPanel : String :=
  let x := 118.0
  let y := 315.0
  rect x y 360.0 118.0 style.white "#cbd5e1" 1.35 (some 0.96) ++
  textAt (x + 22.0) (y + 34.0) "SU(3) trace bound" 19 style.axis "start" ++
  textAt (x + 22.0) (y + 66.0) "-1 ≤ Re Tr(U)/3 ≤ 1" 19 style.critical "start" ++
  textAt (x + 22.0) (y + 96.0) "su3_trace_re_bound" 18 style.muted "start"

def rightPanel : String :=
  let x := 1322.0
  let y := 315.0
  rect x y 360.0 118.0 style.white "#cbd5e1" 1.35 (some 0.96) ++
  textAt (x + 22.0) (y + 34.0) "Wilson positivity" 19 style.axis "start" ++
  textAt (x + 22.0) (y + 66.0) "0 ≤ 1 - Re Tr(P)/3 ≤ 2" 19 style.link "start" ++
  textAt (x + 22.0) (y + 96.0) "WilsonAction4D_nonneg" 18 style.muted "start"

def bottomPanel : String :=
  let x := 540.0
  let y := 1095.0
  rect x y 720.0 90.0 style.white "#cbd5e1" 1.35 (some 0.96) ++
  textAt (x + 360.0) (y + 36.0) "Pμν(x) = Uμ(x) Uν(x+μ) Uμ(x+ν)⁻¹ Uν(x)⁻¹" 21 style.axis ++
  textAt (x + 360.0) (y + 64.0) "constructive plaquettes, no global plaquette assumptions" 18 style.muted

def titleBlock : String :=
  textAt (width / 2.0) 66.0 "SU3Wilson" 54 style.axis ++
  textAt (width / 2.0) 100.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 202.0 "SU(3) trace bound, Wilson plaquette terms, and nonnegative lattice action" 32 style.muted

def footer : String :=
  textAt (width / 2.0) 1348.0
    "Illustration of formal objects in SU3Wilson: SU3, plaquette4D, wilsonTerm4D, WilsonAction4D_nonneg."
    22 style.muted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowDefs ++
  rect 0.0 0.0 width height style.background "none" 0.0 ++
  titleBlock ++
  latticeGrid ++
  plaquette ++
  leftPanel ++
  rightPanel ++
  bottomPanel ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end SU3WilsonGraph

#eval SU3WilsonGraph.writeDefault

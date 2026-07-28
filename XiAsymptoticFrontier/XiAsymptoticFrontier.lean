/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import XiAsymptoticFrontier.Basic
public import XiAsymptoticFrontier.Frontier
public import XiAsymptoticFrontier.Synthesis

/-!
# XiAsymptoticFrontier

Typed analytic frontier for the asymptotic Riemann-von Mangoldt contour
synthesis.
-/

namespace XiAsymptoticFrontierGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "XiAsymptoticFrontier.svg"

def repositoryOutputDir : System.FilePath :=
  "/Users/bezalelizquierdoperez/DEV/LEAN4/M4TH/XiAsymptoticFrontier"

def repositoryOutputPath : System.FilePath :=
  repositoryOutputDir / "XiAsymptoticFrontier.svg"

def defaultOutputPath : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd == repositoryOutputDir then pure localOutputPath else pure repositoryOutputPath

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
  textAt (width / 2.0) 62.0 "XiAsymptoticFrontier" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "typed analytic frontier for the Riemann-von Mangoldt contour synthesis"
    30 styleMuted

def panel (x y w : Float) (head body1 body2 color : String) : String :=
  rect x y w 150.0 stylePanel "#cbd5e1" 1.6 (some 0.94) ++
  textAt (x + 28.0) (y + 42.0) head 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 84.0) body1 21 color "start" ++
  textAt (x + 28.0) (y + 122.0) body2 19 styleMuted "start"

def diagram : String :=
  panel 180.0 305.0 410.0 "Gamma horizontal" "gamma ~ main term" "Stirling frontier" styleTeal ++
  panel 695.0 305.0 410.0 "Residual terms" "origin + vertical + zeta = o(M)" "edge frontier" styleRed ++
  panel 1210.0 305.0 410.0 "Safe-height count" "Nsafe = gamma + residual" "contour reconstruction" styleBlue ++
  line 590.0 380.0 695.0 380.0 styleMuted 2.5 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  line 1105.0 380.0 1210.0 380.0 styleMuted 2.5 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  panel 485.0 610.0 830.0 "riemann_von_mangoldt_from_contour_bridge"
    "AnalyticFrontier N Nsafe C -> N ~ vonMangoldtMainTerm"
    "all residual analytic estimates are explicit hypotheses" styleTeal ++
  line 900.0 455.0 900.0 610.0 styleMuted 2.5 (some "9 7")
    [("marker-end", "url(#arrow-muted)")]

def footer : String :=
  textAt (width / 2.0) 1120.0
    "Illustration of formal objects in XiAsymptoticFrontier: AnalyticFrontier, ContourComponents, GammaHorizontalStirlingGoal, RiemannVonMangoldtMultiplicityCounting."
    21 styleMuted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height "#fffefd" "none" 0.0 ++
  title ++ diagram ++ footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  let path ← defaultOutputPath
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end XiAsymptoticFrontierGraph

#eval XiAsymptoticFrontierGraph.writeDefault

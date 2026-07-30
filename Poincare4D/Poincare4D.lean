/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import Poincare4D.Basic
public import Poincare4D.Flow
public import Poincare4D.Surgery
public import Poincare4D.Conditional

/-!
# Poincare4D

Smooth surgery chains, coupled Ricci-gauge flow contracts, and the conditional
smooth 4D Poincare theorem. All analytic PDE inputs are explicit typed
hypotheses; no package-local axioms.
-/

namespace Poincare4DGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "Poincare4D.svg"

def repositoryOutputPath : System.FilePath :=
  "Poincare4D/Poincare4D.svg"

def defaultOutputPath : IO System.FilePath :=
  pure repositoryOutputPath

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

def arrowMarker : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-muted\" viewBox=\"0 0 10 10\" refX=\"8\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n" ++
  "      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"#475569\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def styleAxis : String := "#1f2937"
def styleMuted : String := "#475569"
def styleBlue : String := "#2563eb"
def styleTeal : String := "#0f766e"
def styleRed : String := "#b91c1c"
def stylePanel : String := "#ffffff"

def title : String :=
  textAt (width / 2.0) 62.0 "Poincare4D" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "smooth surgery chains, coupled Ricci-gauge flow, and conditional 4D Poincare"
    30 styleMuted

def diagram : String :=
  rect 210.0 255.0 1380.0 560.0 "#f8fafc" styleAxis 2.2 (some 0.58) ++
  -- left panel: topology
  rect 250.0 310.0 430.0 150.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt 278.0 352.0 "HomotopySphere" 24 styleAxis "start" ++
  textAt 278.0 394.0 "closed, simply connected" 21 styleTeal "start" ++
  textAt 278.0 432.0 "homotopy equivalent to S^4" 19 styleMuted "start" ++
  -- right panel: surgery
  rect 1120.0 310.0 430.0 150.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt 1148.0 352.0 "FiniteSurgeryChain" 24 styleAxis "start" ++
  textAt 1148.0 394.0 "preserves homotopy sphere" 21 styleBlue "start" ++
  textAt 1148.0 432.0 "preserves diffeomorphism type" 19 styleMuted "start" ++
  -- centre: conditional theorem
  rect 650.0 570.0 500.0 150.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt 678.0 612.0 "smoothPoincare4D_conditional" 23 styleAxis "start" ++
  textAt 678.0 654.0 "HomotopySphere + SurgeryChain" 20 styleRed "start" ++
  textAt 678.0 692.0 "-> DiffeomorphicToSphere4" 19 styleMuted "start" ++
  -- arrows
  line 680.0 460.0 830.0 570.0 styleMuted 2.6 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  line 1350.0 460.0 1000.0 570.0 styleMuted 2.6 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  -- axis labels
  textAt 900.0 850.0 "conditional on analytic PDE frontier" 22 styleMuted

def footer : String :=
  textAt (width / 2.0) 1120.0
    "Illustration of formal objects in Poincare4D: HomotopySphere, FiniteSurgeryChain, SmoothSurgeryStep, smoothPoincare4D_conditional."
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

  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end Poincare4DGraph

#eval Poincare4DGraph.writeDefault

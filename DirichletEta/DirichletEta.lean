/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import DirichletEta.Basic
public import DirichletEta.Analytic
public import DirichletEta.Nonvanishing

/-!
# DirichletEta

Dirichlet eta, its zeta-product identity in `Re s > 1`, analytic product API,
and the typed real frontier for non-vanishing of `ζ` on `(0, 1)`.
-/

namespace DirichletEtaGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "DirichletEta.svg"

def repositoryOutputDir : System.FilePath :=
  "/Users/bezalelizquierdoperez/DEV/LEAN4/M4TH/DirichletEta"

def repositoryOutputPath : System.FilePath :=
  repositoryOutputDir / "DirichletEta.svg"

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

def line (x1 y1 x2 y2 : Float) (stroke : String) (sw : Float) (dash : Option String := none) :
    String :=
  tag "line" <|
    [("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
      ("stroke", stroke), ("stroke-width", fstr sw), ("stroke-linecap", "round")] ++
      match dash with | none => [] | some d => [("stroke-dasharray", d)]

def polyline (pts : String) (stroke : String) (sw : Float) (dash : Option String := none) :
    String :=
  tag "polyline" <|
    [("points", pts), ("fill", "none"), ("stroke", stroke), ("stroke-width", fstr sw),
      ("stroke-linecap", "round"), ("stroke-linejoin", "round")] ++
      match dash with | none => [] | some d => [("stroke-dasharray", d)]

def circle (cx cy r : Float) (fill stroke : String) (sw : Float) : String :=
  tag "circle"
    [("cx", fstr cx), ("cy", fstr cy), ("r", fstr r), ("fill", fill),
      ("stroke", stroke), ("stroke-width", fstr sw)]

def markerLine (x y : Float) (stroke : String) (dash : Option String := none) : String :=
  line x y (x + 58.0) y stroke 4.2 dash

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
def stylePale : String := "#f8fafc"

def plotLeft : Float := 210.0
def plotRight : Float := 1590.0
def plotTop : Float := 250.0
def plotBottom : Float := 850.0

def px (x : Float) : Float :=
  plotLeft + (x / 1.2) * (plotRight - plotLeft)

def py (y : Float) : Float :=
  plotBottom - (y / 1.2) * (plotBottom - plotTop)

def title : String :=
  textAt (width / 2.0) 62.0 "DirichletEta" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "alternating eta series, zeta-product identity, and real non-vanishing frontier"
    30 styleMuted

def grid : String :=
  [0.0, 0.25, 0.5, 0.75, 1.0].foldl (fun out x =>
    out ++ line (px x) plotTop (px x) plotBottom "#dbe4ee" 0.7 (some "4 7")) "" ++
  [0.0, 0.4, 0.8, 1.2].foldl (fun out y =>
    out ++ line plotLeft (py y) plotRight (py y) "#dbe4ee" 0.7 (some "4 7")) ""

def axes : String :=
  rect plotLeft plotTop (plotRight - plotLeft) (plotBottom - plotTop) stylePale styleAxis 2.2 (some 0.58) ++
  grid ++
  line plotLeft (py 0.0) plotRight (py 0.0) styleAxis 1.8 ++
  line (px 1.0) plotTop (px 1.0) plotBottom styleRed 2.6 (some "11 8") ++
  -- x-axis tick labels
  textAt (px 0.0) (plotBottom + 42.0) "0" 22 styleAxis ++
  textAt (px 0.5) (plotBottom + 42.0) "0.5" 22 styleAxis ++
  textAt (px 1.0) (plotBottom + 42.0) "1" 22 styleAxis ++
  textAt ((plotLeft + plotRight) / 2.0) (plotBottom + 88.0) "real parameter x" 26 styleAxis ++
  textAt (plotLeft - 82.0) ((plotTop + plotBottom) / 2.0) "eta scale" 30 styleAxis "middle"
    [("transform", s!"rotate(-90 {fstr (plotLeft - 82.0)} {fstr ((plotTop + plotBottom) / 2.0)})")] ++
  -- zeta pole label centred above the red dashed line
  textAt (px 1.0) (plotTop - 18.0) "zeta pole x = 1" 22 styleRed "middle"

def legend : String :=
  markerLine 350.0 224.0 styleTeal ++
  textAt 425.0 232.0 "positive alternating limit" 22 styleTeal "start" ++
  markerLine 940.0 224.0 styleBlue (some "9 8") ++
  textAt 1015.0 232.0 "partial sums oscillate" 22 styleBlue "start"

def etaPoints : String :=
  String.intercalate " "
    ([((0.05 : Float), (0.60 : Float)), (0.10, 0.62), (0.18, 0.65), (0.28, 0.69),
      (0.40, 0.73), (0.55, 0.78), (0.70, 0.83), (0.85, 0.88), (0.98, 0.92)].map
      (fun p => s!"{fstr (px p.1)}{","}{fstr (py p.2)}"))

def partialPoints : String :=
  String.intercalate " "
    ([((0.05 : Float), (0.18 : Float)), (0.16, 0.42), (0.28, 0.32), (0.40, 0.48),
      (0.52, 0.40), (0.64, 0.53), (0.76, 0.47), (0.88, 0.57), (0.98, 0.52)].map
      (fun p => s!"{fstr (px p.1)}{","}{fstr (py p.2)}"))

def curves : String :=
  polyline partialPoints styleBlue 3.2 (some "9 8") ++
  polyline etaPoints styleTeal 4.2 ++
  circle (px 0.55) (py 0.78) 7.0 styleTeal stylePanel 1.4

def panel (x y w h : Float) (head body1 body2 color : String) : String :=
  rect x y w h stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt (x + 28.0) (y + 42.0) head 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 84.0) body1 21 color "start" ++
  textAt (x + 28.0) (y + 122.0) body2 19 styleMuted "start"

def panelCompactTwoLine (x y w h : Float) (line1 line2 body1 body2 color : String) : String :=
  rect x y w h stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt (x + 28.0) (y + 38.0) line1 19 styleAxis "start" ++
  textAt (x + 28.0) (y + 62.0) line2 19 styleAxis "start" ++
  textAt (x + 28.0) (y + 102.0) body1 20 color "start" ++
  textAt (x + 28.0) (y + 130.0) body2 18 styleMuted "start"

def panels : String :=
  panel 265.0 905.0 525.0 145.0 "eta_eq_zeta_of_re_gt_one"
    "η(s) = (1 − 2^(1−s)) ζ(s)" "proved by even/odd splitting in Re(s) > 1" styleTeal ++
  panelCompactTwoLine 1010.0 905.0 525.0 145.0
    "Alternating-limit bridge" "(RiemannZetaAlternatingLimitIdentity)"
    "typed continuation frontier" "implies ζ(x) ≠ 0 for 0 < x < 1" styleRed

def footer : String :=
  textAt (width / 2.0) 1110.0
    "Formal objects: etaTerm, dirichletEtaSeries, eta_eq_zeta_of_re_gt_one, alternating_zeta_real_pos."
    20 styleMuted ++
  textAt (width / 2.0) 1140.0
    "Schematic illustration — green curve depicts the alternating-series limit trend."
    18 styleMuted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  rect 0.0 0.0 width height "#fffefd" "none" 0.0 ++
  title ++ legend ++ axes ++ curves ++ panels ++ footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  let path ← defaultOutputPath
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end DirichletEtaGraph

#eval DirichletEtaGraph.writeDefault

/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import DiscreteAbelChebyshev.Basic
public import DiscreteAbelChebyshev.ChebyshevBridge

/-!
# DiscreteAbelChebyshev

Discrete Abel summation and a typed Chebyshev-to-prime-counting bridge.
-/

/-!
## Native SVG cover

The following auxiliary namespace generates the package cover figure directly
from Lean.  The code is intentionally separate from the mathematical namespace:
it illustrates the main objects certified in this package, but it does not
add mathematical assumptions or alter the API of the formal package.
-/

namespace DiscreteAbelChebyshevGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "DiscreteAbelChebyshev.svg"

def repositoryOutputDir : System.FilePath :=
  "DiscreteAbelChebyshev"

def repositoryOutputPath : System.FilePath :=
  "DiscreteAbelChebyshev/DiscreteAbelChebyshev.svg"

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

def textAt (x y : Float) (body : String) (size : Nat) (fill : String)
    (anchor : String := "middle") : String :=
  tag "text"
    [("x", fstr x), ("y", fstr y), ("font-family", "DejaVu Serif, Georgia, serif"),
      ("font-size", toString size), ("fill", fill), ("text-anchor", anchor)] body

def styleAxis : String := "#1f2937"
def styleMuted : String := "#475569"
def styleBlue : String := "#2563eb"
def styleTeal : String := "#0f766e"
def styleRed : String := "#b91c1c"
def stylePanel : String := "#ffffff"

def title : String :=
  textAt (width / 2.0) 62.0 "DiscreteAbelChebyshev" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "finite Abel summation and a typed Chebyshev error-transfer frontier"
    30 styleMuted

def panel (x y w : Float) (head body1 body2 color : String) : String :=
  rect x y w 150.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt (x + 28.0) (y + 42.0) head 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 84.0) body1 21 color "start" ++
  textAt (x + 28.0) (y + 122.0) body2 19 styleMuted "start"

def panelFormula (x y w : Float) (head body1 body2 color : String) : String :=
  rect x y w 150.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt (x + 28.0) (y + 42.0) head 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 84.0) body1 17 color "start" ++
  textAt (x + 28.0) (y + 122.0) body2 19 styleMuted "start"

def diagram : String :=
  rect 210.0 255.0 1380.0 640.0 "#f8fafc" styleAxis 2.2 (some 0.58) ++
  -- left: abel summation (formula needs smaller font)
  panelFormula 250.0 310.0 500.0 "abel_summation"
    "Σ a_n f_n = A_N f_N − Σ A_{n+1} Δf_n" "finite, exact, no limits" styleTeal ++
  -- right: Chebyshev error bound
  panel 1050.0 310.0 500.0 "ChebyshevErrorSumBound"
    "explicit residual frontier" "no trusted declaration" styleRed ++
  -- centre: pi approximation (convergence point)
  panel 650.0 570.0 500.0 "pi_approx_final"
    "weighted Λ sum = discrete Li + error" "main term collapses by reverse Abel" styleBlue ++
  -- arrows: left → centre, right → centre (V-flow)
  line 700.0 460.0 850.0 570.0 styleMuted 2.6 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  line 1100.0 460.0 950.0 570.0 styleMuted 2.6 (some "9 7")
    [("marker-end", "url(#arrow-muted)")] ++
  -- conclusion inside panel, with room to breathe
  textAt 900.0 800.0 "chebyshev_implies_prime_error" 30 styleAxis ++
  textAt 900.0 842.0 "Chebyshev bound + residual frontier → prime-counting error" 22 styleMuted

def footer : String :=
  textAt (width / 2.0) 1120.0
    "Illustration of formal objects in DiscreteAbelChebyshev: abel_summation, invLog, pi_approx_final, ChebyshevErrorSumBound."
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

end DiscreteAbelChebyshevGraph

#eval DiscreteAbelChebyshevGraph.writeDefault

/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import PrimeGapsSophie.SophieGermain
public import PrimeGapsSophie.PrimeGap
public import PrimeGapsSophie.HigherOrder

/-!
# PrimeGapsSophie

Sophie Germain primes and parity of higher-order prime gaps.
-/

namespace PrimeGapsSophieGraph

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath := "PrimeGapsSophie.svg"

def repositoryOutputDir : System.FilePath :=
  "/Users/bezalelizquierdoperez/DEV/LEAN4/M4TH/PrimeGapsSophie"

def repositoryOutputPath : System.FilePath :=
  repositoryOutputDir / "PrimeGapsSophie.svg"

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
  textAt (width / 2.0) 62.0 "PrimeGapsSophie" 48 styleAxis ++
  textAt (width / 2.0) 96.0 "by Alektronnik" 22 styleMuted ++
  textAt (width / 2.0) 172.0
    "Sophie Germain congruences and parity of higher-order prime gaps"
    30 styleMuted

def lattice : String :=
  rect 210.0 255.0 1380.0 555.0 "#f8fafc" styleAxis 2.2 (some 0.58) ++
  [0.0, 1.0, 2.0, 3.0, 4.0].foldl (fun out y =>
    out ++ line 210.0 (315.0 + 110.0 * y) 1590.0 (315.0 + 110.0 * y) "#dbe4ee" 0.7 (some "4 7")) "" ++
  [0.0, 1.0, 2.0, 3.0, 4.0, 5.0].foldl (fun out x =>
    out ++ line (310.0 + 230.0 * x) 255.0 (310.0 + 230.0 * x) 810.0 "#dbe4ee" 0.7 (some "4 7")) ""

def points : List (Float × Float × String) :=
  [(310.0, 700.0, "p₀"), (540.0, 590.0, "p₁"), (770.0, 650.0, "p₂"),
   (1000.0, 520.0, "p₃"), (1230.0, 575.0, "p₄"), (1460.0, 470.0, "p₅")]

def pointDiagram : String :=
  points.foldl (fun out p =>
    out ++ circle p.1 p.2.1 9.0 styleTeal stylePanel 1.8 ++
      textAt p.1 (p.2.1 - 24.0) p.2.2 22 styleAxis) "" ++
  line 310.0 700.0 540.0 590.0 styleBlue 3.2 (some "10 8") ++
  line 540.0 590.0 770.0 650.0 styleBlue 3.2 (some "10 8") ++
  line 770.0 650.0 1000.0 520.0 styleBlue 3.2 (some "10 8") ++
  line 1000.0 520.0 1230.0 575.0 styleBlue 3.2 (some "10 8") ++
  line 1230.0 575.0 1460.0 470.0 styleBlue 3.2 (some "10 8") ++
  textAt 900.0 320.0 "nthOrderGap N p = Σ (-1)^k choose(N,k) p(N-k)" 27 styleAxis ++
  textAt 900.0 365.0 "odd primes force every positive finite difference to be even" 23 styleMuted

def panel (x y w : Float) (head body1 body2 color : String) : String :=
  rect x y w 145.0 stylePanel "#cbd5e1" 1.6 (some 0.95) ++
  textAt (x + 28.0) (y + 42.0) head 24 styleAxis "start" ++
  textAt (x + 28.0) (y + 84.0) body1 21 color "start" ++
  textAt (x + 28.0) (y + 122.0) body2 19 styleMuted "start"

def panels : String :=
  panel 225.0 865.0 435.0 "IsSophieGermainPrime"
    "p prime and 2p + 1 prime" "p >= 5 -> p ≡ 5 mod 6" styleTeal ++
  panel 700.0 865.0 405.0 "primeGap_even"
    "p_{n+1} - p_n = 2k" "for n >= 1" styleBlue ++
  panel 1145.0 865.0 435.0 "nthOrderGap_even"
    "finite differences remain even" "all positive orders N" styleRed

def footer : String :=
  textAt (width / 2.0) 1120.0
    "Illustration of formal objects in PrimeGapsSophie: IsSophieGermainPrime, nthPrime, primeGap, nthOrderGap_even_of_odd_primes."
    21 styleMuted

def svg : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fstr width} {fstr height}\" width=\"{fstr width}\" height=\"{fstr height}\">\n" ++
  arrowMarker ++
  rect 0.0 0.0 width height "#fffefd" "none" 0.0 ++
  title ++ lattice ++ pointDiagram ++ panels ++ footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  let path ← defaultOutputPath
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path svg
  IO.println s!"wrote {path}"

end PrimeGapsSophieGraph

#eval PrimeGapsSophieGraph.writeDefault

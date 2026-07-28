/-
Copyright (c) 2026 Bezalel Izquierdo Pérez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bezalel Izquierdo Pérez
-/
module

import Lean

public import XiLogDeriv.Basic
public import XiLogDeriv.GammaR
public import XiLogDeriv.DigammaContinuity
public import XiLogDeriv.Expansion

/-!
# XiLogDeriv

This is the root module for the standalone `XiLogDeriv` package.  It packages
the logarithmic-derivative expansion of the entire Xi variant, the `Gammaℝ`
digamma identity, and continuity wrappers for `Complex.digamma`.
-/

/-!
## Native SVG cover

The auxiliary namespace below generates a compact diagram of the decomposition

`Xi'/Xi = polynomial + GammaR/digamma + zeta'/zeta`.

The generator is intentionally isolated from the mathematical namespace.
-/

namespace XiLogDerivGraph

structure Style where
  background : String := "#fbfaf7"
  axis : String := "#1f2933"
  muted : String := "#475569"
  blue : String := "#1f5fd1"
  teal : String := "#0f766e"
  red : String := "#b91c1c"
  paleBlue : String := "#eff6ff"
  paleTeal : String := "#ecfdf5"
  paleRed : String := "#fef2f2"
  white : String := "#ffffff"

def style : Style := {}

def width : Float := 1800.0
def height : Float := 1180.0

def localOutputPath : System.FilePath :=
  "XiLogDeriv.svg"

def repositoryOutputDir : System.FilePath :=
  "M4TH/XiLogDeriv"

def repositoryOutputPath : System.FilePath :=
  "M4TH/XiLogDeriv/XiLogDeriv.svg"

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
    s!"  <{name}{attrs xs}>{body}</{name}>\n"

def rect (x y w h : Float) (fill stroke : String) (sw : Float) (opacity : Option Float := none) : String :=
  let base := [
    ("x", fstr x), ("y", fstr y), ("width", fstr w), ("height", fstr h),
    ("fill", fill), ("stroke", stroke), ("stroke-width", fstr sw)
  ]
  let xs := match opacity with
    | some a => base ++ [("fill-opacity", fstr a)]
    | none => base
  tag "rect" xs

def line (x1 y1 x2 y2 : Float) (stroke : String) (sw : Float) (dash : Option String := none) : String :=
  let base := [
    ("x1", fstr x1), ("y1", fstr y1), ("x2", fstr x2), ("y2", fstr y2),
    ("stroke", stroke), ("stroke-width", fstr sw), ("stroke-linecap", "round")
  ]
  let xs := match dash with
    | some d => base ++ [("stroke-dasharray", d)]
    | none => base
  tag "line" xs

def textAt (x y : Float) (body : String) (size : Nat) (fill : String)
    (anchor : String := "middle") : String :=
  tag "text" [
    ("x", fstr x), ("y", fstr y), ("font-size", toString size), ("fill", fill),
    ("text-anchor", anchor), ("font-family", "DejaVu Serif, Georgia, serif")
  ] (esc body)

def arrowMarker : String :=
  "  <defs>\n" ++
  "    <marker id=\"arrow-blue\" markerWidth=\"12\" markerHeight=\"12\" refX=\"10\" refY=\"6\" orient=\"auto\">\n" ++
  "      <path d=\"M 0 0 L 12 6 L 0 12 z\" fill=\"#1f5fd1\"/>\n" ++
  "    </marker>\n" ++
  "  </defs>\n"

def title : String :=
  textAt (width / 2.0) 66.0 "XiLogDeriv" 54 style.axis ++
  textAt (width / 2.0) 100.0 "by Alektronnik" 24 style.muted ++
  textAt (width / 2.0) 165.0
    "logarithmic derivative of Xi: polynomial, GammaR/digamma, and zeta components"
    30 style.muted

def componentBox (x y : Float) (fill stroke title body : String) : String :=
  rect x y 410.0 210.0 fill stroke 1.8 (some 0.92) ++
  textAt (x + 28.0) (y + 48.0) title 27 style.axis "start" ++
  textAt (x + 28.0) (y + 98.0) body 25 stroke "start"

def diagram : String :=
  let y := 400.0
  componentBox 115.0 y style.paleBlue style.blue
    "polynomial factor"
    "1 / s + 1 / (s - 1)" ++
  componentBox 695.0 y style.paleTeal style.teal
    "GammaR factor"
    "-1/2 log pi + 1/2 digamma(s/2)" ++
  componentBox 1275.0 y style.paleRed style.red
    "zeta factor"
    "zeta'(s) / zeta(s)" ++
  line 525.0 (y + 105.0) 685.0 (y + 105.0) style.blue 3.0 (some "10 8") ++
  line 1105.0 (y + 105.0) 1265.0 (y + 105.0) style.blue 3.0 (some "10 8") ++
  textAt (width / 2.0) 300.0 "entireXiLogDeriv s = Xi'(s) / Xi(s)" 32 style.axis ++
  textAt (width / 2.0) 705.0
    "entireXiLogDeriv_full_expansion_with_digamma"
    26 style.axis ++
  textAt (width / 2.0) 760.0
    "requires the explicit nonvanishing hypotheses for Xi, GammaR, zeta, and completed zeta"
    23 style.muted

def footer : String :=
  textAt (width / 2.0) 1065.0
    "Illustration of formal objects in XiLogDeriv: entireXiLogDeriv, gammaRFactorLogDeriv_eq_neg_half_log_pi_add_half_digamma, digamma continuity."
    22 style.muted

def svg : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 " ++ fstr width ++ " " ++ fstr height ++ "\">\n" ++
  rect 0.0 0.0 width height style.background style.background 0.0 ++
  arrowMarker ++
  title ++
  diagram ++
  footer ++
  "</svg>\n"

def writeDefault : IO Unit := do
  IO.FS.writeFile (← defaultOutputPath) svg

end XiLogDerivGraph

#eval XiLogDerivGraph.writeDefault

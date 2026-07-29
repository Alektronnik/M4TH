# XiLogResidue.web.lean — Compatibilidad Lean v4.33.0-rc1

## Cambios respecto a XiLogResidue.live.lean

| API v4.31.0 (.live) | API v4.33.0-rc1 (.web) |
|---------------------|-------------------------|
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `ENat.map_coe` | `ENat.map_natCast` |
| `Nat.cast_zero` (ENat) | `ENat.natCast_zero` |

## Fixes adicionales

- `entireXi_meromorphicOrder_ne_top_on_criticalBox` (L523): `simp` pasa a `simp [ENat.map_natCast]`. En v4.33.0-rc1, `simp` ya no encuentra `ENat.map_natCast` sin explicitarlo.
- `mem_zerosUpToIm_finset_divisor_support` (L600-601): `rw [ENat.map_coe, WithTop.untop₀_coe]` pasa a `simp [ENat.map_natCast]` y `ENat.coe_zero` pasa a `ENat.natCast_zero`.

## Verificacion

```
grep -c 'Set\.mem_ofPred_eq' XiLogResidue.web.lean      # debe dar 5
grep -c 'ENat\.map_natCast' XiLogResidue.web.lean        # debe dar 3
grep -c 'ENat\.natCast_zero' XiLogResidue.web.lean       # debe dar 1
grep -c 'Set\.mem_setOf_eq\|ENat\.map_coe\|Nat\.cast_zero' XiLogResidue.web.lean  # debe dar 0
```

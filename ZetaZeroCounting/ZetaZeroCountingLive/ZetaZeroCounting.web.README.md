# ZetaZeroCounting.web.lean — Compatibilidad Lean v4.33.0-rc1

## Cambios respecto a ZetaZeroCounting.live.lean

| API v4.31.0 (.live) | API v4.33.0-rc1 (.web) |
|---------------------|-------------------------|
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` |
| `Nat.cast_zero` (ENat) | `ENat.natCast_zero` |

## Verificacion

```
grep -c 'Set\.mem_ofPred_eq\|ENat\.natCast_zero' ZetaZeroCounting.web.lean   # debe dar 7
grep -c 'Set\.mem_setOf_eq\|Nat\.cast_zero' ZetaZeroCounting.web.lean        # debe dar 0
```
